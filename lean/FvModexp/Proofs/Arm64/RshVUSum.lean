import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Common.AsmShift
import FvModexp.Proofs.Lib.RshVUA64

/-!
# `math/big.rshVU.abi0` (go-bigmodexpfix arith_arm64.s:161, ABI0, arm64): library summary

`rshVU(z, x []Word, s uint) (c Word)`, forward loop: `z[i] = x[i] >> s | x[i+1] << (64-s)`, `z[n-1] = x[n-1] >> s`,
`c = x[0] << (64-s)`. Value form: `Z = X >> s`, `c = (X mod 2^s) · 2^(64-s)` (`Common/AsmShift.lean` `RInv`).
Loop structure (one `janus_run` per declaration): entry → `pos_lem`/`zero_lem`; `1x` loop `one_lem` (induction),
loop head `h4_lem`, `4x` block `blk_lem` (induction), final store `fin_lem`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.RshVUA64 (program entry)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.RshVUSum

abbrev head4 : Nat := entry + 0x58
abbrev body1 : Nat := entry + 0x3c
abbrev body4 : Nat := entry + 0x5c
abbrev fin : Nat := entry + 0xa4

/-- the preconditions at the entry (frame words: `z, len, cap, x, len, cap, s, c`) -/
structure Ctx (s : State) (z x n sh : Nat) : Prop where
  hz : s.mem.readLE (s.sp.toNat + 8) 8 = z
  hn : s.mem.readLE (s.sp.toNat + 16) 8 = n
  hx : s.mem.readLE (s.sp.toNat + 32) 8 = x
  hs : s.mem.readLE (s.sp.toNat + 56) 8 = sh
  lr4 : (s.regs 30).toNat % 4 = 0
  lr56 : (s.regs 30).toNat < 2 ^ 56
  al : s.sp.toNat % 16 = 0
  fb : s.sp.toNat + 72 ≤ 2 ^ 48
  facc : s.mem.accessible (s.sp.toNat + 8) 64 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  sh1 : 1 ≤ sh
  sh63 : sh ≤ 63
  alx : z ≤ x ∨ Apart z (8 * n) x (8 * n)
  azr : Apart z (8 * n) (s.sp.toNat + 64) 8
  axr : Apart x (8 * n) (s.sp.toNat + 64) 8

def Pre (s : State) : Prop :=
  Ctx s (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8)
    (s.mem.readLE (s.sp.toNat + 56) 8)

/-- the memory after the call: `Z = X >> s`, `c = (X mod 2^s) · 2^(64-s)` -/
def Q (s : State) (m : Memory) : Prop :=
  lv m (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) =
      lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) /
        2 ^ s.mem.readLE (s.sp.toNat + 56) 8 ∧
  m.readLE (s.sp.toNat + 64) 8 =
      lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) %
        2 ^ s.mem.readLE (s.sp.toNat + 56) 8 * 2 ^ (64 - s.mem.readLE (s.sp.toNat + 56) 8) ∧
  MemFrame s.mem m [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8),
      (s.sp.toNat + 64, s.sp.toNat + 72)]

/-- limbs of `x` at or above the written prefix are still intact -/
theorem xr {z x n sh : Nat} {s S : State} (hc : Ctx s z x n sh) (u m : Nat) (hm : u ≤ m) (hj : m + 1 ≤ n)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * u), (s.sp.toNat + 64, s.sp.toNat + 72)]) :
    S.mem.readLE (x + 8 * m) 8 = s.mem.readLE (x + 8 * m) 8 := by
  obtain ⟨hz, hn, hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc
  exact hf.readLE _ _ (by
    simp only [outside_cons, outside_nil, and_true]
    unfold Apart at alx axr; omega)

theorem frame_st {m m' : Memory} {z u r1 r2 : Nat} (h : MemFrame m m' [(z, z + 8 * u), (r1, r2)]) (v : Nat) :
    MemFrame m (m'.writeLE (z + 8 * u) 8 v) [(z, z + 8 * (u + 1)), (r1, r2)] :=
  MemFrame.writeLE (frame_mono h (fun a0 n0 h0 => by
    simp only [outside_cons, outside_nil, and_true] at h0 ⊢; omega)) _ (r := (z, z + 8 * (u + 1))) (by simp)
    (by omega) (by omega)

theorem frame_st4 {m m' : Memory} {z u r1 r2 : Nat} (h : MemFrame m m' [(z, z + 8 * u), (r1, r2)])
    (v0 v1 v2 v3 : Nat) :
    MemFrame m ((((m'.writeLE (z + 8 * u) 8 v0).writeLE (z + 8 * u + 8) 8 v1).writeLE (z + 8 * u + 16) 8 v2).writeLE
      (z + 8 * u + 24) 8 v3) [(z, z + 8 * (u + 4)), (r1, r2)] := by
  have A := frame_st h v0
  have B := frame_st A v1
  have C := frame_st B v2
  have D := frame_st C v3
  rw [show z + 8 * (u + 1) = z + 8 * u + 8 by omega, show z + 8 * (u + 1 + 1) = z + 8 * u + 16 by omega,
    show z + 8 * (u + 1 + 1 + 1) = z + 8 * u + 24 by omega, show u + 1 + 1 + 1 + 1 = u + 4 by omega] at D
  exact D

/-- the written word of one step, `(b << (64-s)) ||| (a >> s)`, as the machine computes it -/
theorem ow' {sh : Nat} (sh1 : 1 ≤ sh) (sh63 : sh ≤ 63) (a b : Nat) (ha : a < 2 ^ 64) :
    (b * 2 ^ (64 - sh) % 2 ^ 64 ||| a / 2 ^ sh) % 2 ^ 64 = a / 2 ^ sh + b * 2 ^ (64 - sh) % 2 ^ 64 := by
  rw [or_shr a b sh ha sh1 sh63]; exact Nat.mod_eq_of_lt (shr_sum_lt a b sh ha sh1 sh63)

theorem shr_ofNat (v sh : Nat) (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> sh = BitVec.ofNat 64 (v / 2 ^ sh) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv)]

theorem fin_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) (S : State) (t : Nat)
    (hn : t + 1 = n) (hpc : S.pc = BitVec.ofNat 64 fin)
    (r3 : S.regs 3 = BitVec.ofNat 64 (z + 8 * t)) (r4 : S.regs 4 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * t) 8 / 2 ^ sh))
    (hC : S.mem.readLE (s.sp.toNat + 64) 8 = s.mem.readLE x 8 * 2 ^ (64 - sh) % 2 ^ 64) (hI : RInv s.mem S.mem x z sh t)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * t), (s.sp.toNat + 64, s.sp.toNat + 72)])
    (hsp : S.sp = s.sp) (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.regs 29) (h30 : S.regs 30 = s.regs 30) (hfp : S.fpcr = s.fpcr)
    (htp : S.tpidr = s.tpidr) (hdc : S.dczid = s.dczid) (hex : S.excl = s.excl)
    (hep : S.exclPass = s.exclPass) :
    ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn', hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  janus_run [Q]
  subst hn
  rw [hz, hn', hx, hs]
  have hv : s.mem.readLE (x + 8 * t) 8 / 2 ^ sh % 2 ^ 64 = s.mem.readLE (x + 8 * t) 8 / 2 ^ sh :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (limb_lt _ _))
  obtain ⟨e1, e2⟩ := rinv_fin s.mem S.mem x z sh t (s.mem.readLE (x + 8 * t) 8 / 2 ^ sh) hI hv
  refine ⟨htp, hdc, hex, hep, e1, ?_, ?_⟩
  · rw [hC, e2, shr_lo_eq _ _ sh1 sh63, Nat.mul_comm]
  · exact (frame_st hf _)

/-- the memory effect of one `1x` iteration (`w` the stored word) -/
theorem one_inv {z x n sh : Nat} {s S : State} (hc : Ctx s z x n sh) (u C : Nat) (hn : u + 2 ≤ n)
    (hC : S.mem.readLE (s.sp.toNat + 64) 8 = C) (hI : RInv s.mem S.mem x z sh u)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * u), (s.sp.toNat + 64, s.sp.toNat + 72)]) (w : Nat)
    (hw : w % 2 ^ 64 = s.mem.readLE (x + 8 * u) 8 / 2 ^ sh + s.mem.readLE (x + 8 * (u + 1)) 8 * 2 ^ (64 - sh) % 2 ^ 64) :
    (S.mem.writeLE (z + 8 * u) 8 w).readLE (s.sp.toNat + 64) 8 = C ∧
      RInv s.mem (S.mem.writeLE (z + 8 * u) 8 w) x z sh (u + 1) ∧
      MemFrame s.mem (S.mem.writeLE (z + 8 * u) 8 w) [(z, z + 8 * (u + 1)), (s.sp.toNat + 64, s.sp.toNat + 72)] := by
  have hc' := hc
  obtain ⟨hz, hn', hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc'
  refine ⟨?_, rinv_step1 s.mem S.mem x z sh u w sh1 sh63 hI hw, frame_st hf _⟩
  rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega)]; exact hC

/-- the memory effect of one `4x` iteration -/
theorem blk_inv {z x n sh : Nat} {s S : State} (hc : Ctx s z x n sh) (u C : Nat) (hn : u + 5 ≤ n)
    (hC : S.mem.readLE (s.sp.toNat + 64) 8 = C) (hI : RInv s.mem S.mem x z sh u)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * u), (s.sp.toNat + 64, s.sp.toNat + 72)])
    (w0 w1 w2 w3 : Nat)
    (hw0 : w0 % 2 ^ 64 = s.mem.readLE (x + 8 * u) 8 / 2 ^ sh + s.mem.readLE (x + 8 * (u + 1)) 8 * 2 ^ (64 - sh) % 2 ^ 64)
    (hw1 : w1 % 2 ^ 64 = s.mem.readLE (x + 8 * (u + 1)) 8 / 2 ^ sh + s.mem.readLE (x + 8 * (u + 2)) 8 * 2 ^ (64 - sh) % 2 ^ 64)
    (hw2 : w2 % 2 ^ 64 = s.mem.readLE (x + 8 * (u + 2)) 8 / 2 ^ sh + s.mem.readLE (x + 8 * (u + 3)) 8 * 2 ^ (64 - sh) % 2 ^ 64)
    (hw3 : w3 % 2 ^ 64 = s.mem.readLE (x + 8 * (u + 3)) 8 / 2 ^ sh + s.mem.readLE (x + 8 * (u + 4)) 8 * 2 ^ (64 - sh) % 2 ^ 64) :
    ((((S.mem.writeLE (z + 8 * u) 8 w0).writeLE (z + 8 * u + 8) 8 w1).writeLE
      (z + 8 * u + 16) 8 w2).writeLE (z + 8 * u + 24) 8 w3).readLE (s.sp.toNat + 64) 8 = C ∧
    RInv s.mem ((((S.mem.writeLE (z + 8 * u) 8 w0).writeLE (z + 8 * u + 8) 8 w1).writeLE
      (z + 8 * u + 16) 8 w2).writeLE (z + 8 * u + 24) 8 w3) x z sh (u + 4) ∧
    MemFrame s.mem ((((S.mem.writeLE (z + 8 * u) 8 w0).writeLE (z + 8 * u + 8) 8 w1).writeLE
      (z + 8 * u + 16) 8 w2).writeLE (z + 8 * u + 24) 8 w3)
      [(z, z + 8 * (u + 4)), (s.sp.toNat + 64, s.sp.toNat + 72)] := by
  have hc' := hc
  obtain ⟨hz, hn', hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc'
  refine ⟨?_, rinv_step4 s.mem S.mem x z sh u _ _ _ _ sh1 sh63 hI hw0 hw1 hw2 hw3, frame_st4 hf _ _ _ _⟩
  rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega),
    Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega),
    Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega),
    Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega)]
  exact hC

theorem shr_rd (m : Memory) (a sh : Nat) :
    BitVec.ofNat 64 (m.readLE a 8) >>> sh = BitVec.ofNat 64 (m.readLE a 8 / 2 ^ sh) := shr_ofNat _ _ (limb_lt _ _)

/-- the stored word, as the machine computes it (`(b << (64-s)) ||| (a >> s)`), reduced mod `2^64` -/
theorem ow {sh : Nat} (sh1 : 1 ≤ sh) (sh63 : sh ≤ 63) (a b : Nat) (ha : a < 2 ^ 64) :
    (b * 2 ^ (64 - sh) % 18446744073709551616 ||| a / 2 ^ sh % 18446744073709551616) % 2 ^ 64 =
      a / 2 ^ sh + b * 2 ^ (64 - sh) % 2 ^ 64 := by
  rw [show (18446744073709551616 : Nat) = 2 ^ 64 from rfl,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a _) ha)]
  exact ow' sh1 sh63 a b ha

theorem blk_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) :
    ∀ k (S : State) (u : Nat), u + 4 * (k + 1) + 1 = n →
      S.pc = BitVec.ofNat 64 body4 → S.regs 0 = BitVec.ofNat 64 (k + 1) →
      S.regs 1 = BitVec.ofNat 64 sh → S.regs 5 = 64#64 - BitVec.ofNat 64 sh →
      S.regs 2 = BitVec.ofNat 64 (x + 8 * (u + 1)) → S.regs 3 = BitVec.ofNat 64 (z + 8 * u) →
      S.regs 4 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * u) 8 / 2 ^ sh) →
      S.mem.readLE (s.sp.toNat + 64) 8 = s.mem.readLE x 8 * 2 ^ (64 - sh) % 2 ^ 64 → RInv s.mem S.mem x z sh u →
      MemFrame s.mem S.mem [(z, z + 8 * u), (s.sp.toNat + 64, s.sp.toNat + 72)] →
      S.sp = s.sp → S.regs 18 = s.regs 18 → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 30 = s.regs 30 → S.fpcr = s.fpcr →
      S.tpidr = s.tpidr → S.dczid = s.dczid → S.excl = s.excl → S.exclPass = s.exclPass →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have hsh : sh % 64 = sh := Nat.mod_eq_of_lt (by omega)
  have hn64 : n < 2 ^ 64 := by omega
  have hE : (18446744073709551616 - sh - 18446744073709551552) % 64 = 64 - sh := by omega
  intro k
  induction k with
  | zero =>
    intro S u hu hpc h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    have rx1 := xr hc u (u + 1) (by omega) (by omega) hf
    have rx2 := xr hc u (u + 2) (by omega) (by omega) hf
    have rx3 := xr hc u (u + 3) (by omega) (by omega) hf
    have rx4 := xr hc u (u + 4) (by omega) (by omega) hf
    janus_run until [body4, fin]
    simp only [hsh, hE, shr_rd, BitVec.toNat_ofNat, show x + 8 * (u + 1) + 8 = x + 8 * (u + 2) by omega,
      show x + 8 * (u + 1) + 16 = x + 8 * (u + 3) by omega, show x + 8 * (u + 1) + 24 = x + 8 * (u + 4) by omega,
      rx1, rx2, rx3, rx4]
    refine fin_lem s hc _ (u + 4) (by omega) ?_ ?_ ?_ ?hC ?hI ?hf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case hC => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _))).1
    case hI => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _))).2.1
    case hf => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _))).2.2
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; first | exact hsp | exact h18 | exact h28 | exact h29 | exact h30 | exact hfp | exact htp | exact hdc | exact hex | exact hep | exact h1 | exact h5) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
  | succ k ih =>
    intro S u hu hpc h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    have hk : k + 1 + 1 < 2 ^ 64 := by omega
    have rx1 := xr hc u (u + 1) (by omega) (by omega) hf
    have rx2 := xr hc u (u + 2) (by omega) (by omega) hf
    have rx3 := xr hc u (u + 3) (by omega) (by omega) hf
    have rx4 := xr hc u (u + 4) (by omega) (by omega) hf
    janus_run until [body4, fin]
    simp only [hsh, hE, shr_rd, BitVec.toNat_ofNat, show x + 8 * (u + 1) + 8 = x + 8 * (u + 2) by omega,
      show x + 8 * (u + 1) + 16 = x + 8 * (u + 3) by omega, show x + 8 * (u + 1) + 24 = x + 8 * (u + 4) by omega,
      rx1, rx2, rx3, rx4]
    refine ih _ (u + 4) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case hC => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _))).1
    case hI => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _))).2.1
    case hf => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _)) (ow sh1 sh63 _ _ (limb_lt _ _))).2.2
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; first | exact hsp | exact h18 | exact h28 | exact h29 | exact h30 | exact hfp | exact htp | exact hdc | exact hex | exact hep | exact h1 | exact h5) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

theorem h4_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) :
    ∀ (q : Nat) (S : State) (u : Nat), u + 4 * q + 1 = n →
      S.pc = BitVec.ofNat 64 head4 → S.regs 0 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 sh → S.regs 5 = 64#64 - BitVec.ofNat 64 sh →
      S.regs 2 = BitVec.ofNat 64 (x + 8 * (u + 1)) → S.regs 3 = BitVec.ofNat 64 (z + 8 * u) →
      S.regs 4 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * u) 8 / 2 ^ sh) →
      S.mem.readLE (s.sp.toNat + 64) 8 = s.mem.readLE x 8 * 2 ^ (64 - sh) % 2 ^ 64 → RInv s.mem S.mem x z sh u →
      MemFrame s.mem S.mem [(z, z + 8 * u), (s.sp.toNat + 64, s.sp.toNat + 72)] →
      S.sp = s.sp → S.regs 18 = s.regs 18 → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 30 = s.regs 30 → S.fpcr = s.fpcr →
      S.tpidr = s.tpidr → S.dczid = s.dczid → S.excl = s.excl → S.exclPass = s.exclPass →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have hsh : sh % 64 = sh := Nat.mod_eq_of_lt (by omega)
  have hn64 : n < 2 ^ 64 := by omega
  have hE : (18446744073709551616 - sh - 18446744073709551552) % 64 = 64 - sh := by omega
  intro q
  rcases q with _ | k
  · intro S u hu hpc h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    janus_run until [fin]
    refine fin_lem s hc _ u (by omega) ?_ ?_ ?_ hC hI hf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; first | exact hsp | exact h18 | exact h28 | exact h29 | exact h30 | exact hfp | exact htp | exact hdc | exact hex | exact hep | exact h1 | exact h5) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
  · intro S u hu hpc h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    janus_run until [body4]
    refine blk_lem s hc k _ u (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hC hI hf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; first | exact hsp | exact h18 | exact h28 | exact h29 | exact h30 | exact hfp | exact htp | exact hdc | exact hex | exact hep | exact h1 | exact h5) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

theorem one_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) (q : Nat) :
    ∀ j (S : State) (u : Nat), u + (j + 1) + 4 * q + 1 = n →
      S.pc = BitVec.ofNat 64 body1 → S.regs 6 = BitVec.ofNat 64 (j + 1) → S.regs 0 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 sh → S.regs 5 = 64#64 - BitVec.ofNat 64 sh →
      S.regs 2 = BitVec.ofNat 64 (x + 8 * (u + 1)) → S.regs 3 = BitVec.ofNat 64 (z + 8 * u) →
      S.regs 4 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * u) 8 / 2 ^ sh) →
      S.mem.readLE (s.sp.toNat + 64) 8 = s.mem.readLE x 8 * 2 ^ (64 - sh) % 2 ^ 64 → RInv s.mem S.mem x z sh u →
      MemFrame s.mem S.mem [(z, z + 8 * u), (s.sp.toNat + 64, s.sp.toNat + 72)] →
      S.sp = s.sp → S.regs 18 = s.regs 18 → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 30 = s.regs 30 → S.fpcr = s.fpcr →
      S.tpidr = s.tpidr → S.dczid = s.dczid → S.excl = s.excl → S.exclPass = s.exclPass →
      ReachesRet program (s.regs 30) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have hsh : sh % 64 = sh := Nat.mod_eq_of_lt (by omega)
  have hn64 : n < 2 ^ 64 := by omega
  have hE : (18446744073709551616 - sh - 18446744073709551552) % 64 = 64 - sh := by omega
  intro j
  induction j with
  | zero =>
    intro S u hu hpc h6 h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    have rx1 := xr hc u (u + 1) (by omega) (by omega) hf
    janus_run until [body1, head4]
    simp only [hsh, hE, shr_rd, BitVec.toNat_ofNat, rx1]
    refine h4_lem s hc q _ (u + 1) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case hC => exact (one_inv hc u _ (by omega) hC hI hf _ (ow sh1 sh63 _ _ (limb_lt _ _))).1
    case hI => exact (one_inv hc u _ (by omega) hC hI hf _ (ow sh1 sh63 _ _ (limb_lt _ _))).2.1
    case hf => exact (one_inv hc u _ (by omega) hC hI hf _ (ow sh1 sh63 _ _ (limb_lt _ _))).2.2
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; first | exact hsp | exact h18 | exact h28 | exact h29 | exact h30 | exact hfp | exact htp | exact hdc | exact hex | exact hep | exact h1 | exact h5) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
  | succ j ih =>
    intro S u hu hpc h6 h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    have rx1 := xr hc u (u + 1) (by omega) (by omega) hf
    janus_run until [body1, head4]
    simp only [hsh, hE, shr_rd, BitVec.toNat_ofNat, rx1]
    refine ih _ (u + 1) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case hC => exact (one_inv hc u _ (by omega) hC hI hf _ (ow sh1 sh63 _ _ (limb_lt _ _))).1
    case hI => exact (one_inv hc u _ (by omega) hC hI hf _ (ow sh1 sh63 _ _ (limb_lt _ _))).2.1
    case hf => exact (one_inv hc u _ (by omega) hC hI hf _ (ow sh1 sh63 _ _ (limb_lt _ _))).2.2
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; first | exact hsp | exact h18 | exact h28 | exact h29 | exact h30 | exact hfp | exact htp | exact hdc | exact hex | exact hep | exact h1 | exact h5) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

theorem sub1 (m : Nat) (h : m + 1 < 2 ^ 64) : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem zero_lem {z x sh : Nat} (s : State) (hc : Ctx s z x 0 sh) (hpc : s.pc = BitVec.ofNat 64 entry) :
    ReachesRet program (s.regs 30) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc'
  janus_run [Q]
  refine ⟨?_, ?_, ?_⟩
  · simp [lv_zero]
  · simp [lv_zero]
  · exact MemFrame.writeLE (MemFrame.refl _ _) _ (r := (s.sp.toNat + 64, s.sp.toNat + 72)) (by simp) (Nat.le_refl _) (Nat.le_refl _)

theorem pos_lem {z x m sh : Nat} (s : State) (hc : Ctx s z x (m + 1) sh) (hpc : s.pc = BitVec.ofNat 64 entry) :
    ReachesRet program (s.regs 30) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc'
  have bz := Memory.accessible_bound _ accz
  have bx := Memory.accessible_bound _ accx
  have hsh : sh % 64 = sh := Nat.mod_eq_of_lt (by omega)
  have hn64 : m + 1 < 2 ^ 64 := by omega
  have hE : (18446744073709551616 - sh - 18446744073709551552) % 64 = 64 - sh := by omega
  have hsp : s.sp = s.sp := rfl
  have h18 : s.regs 18 = s.regs 18 := rfl
  have h28 : s.regs 28 = s.regs 28 := rfl
  have h29 : s.regs 29 = s.regs 29 := rfl
  have h30 : s.regs 30 = s.regs 30 := rfl
  have hfp : s.fpcr = s.fpcr := rfl
  have htp : s.tpidr = s.tpidr := rfl
  have hdc : s.dczid = s.dczid := rfl
  have hex : s.excl = s.excl := rfl
  have hep : s.exclPass = s.exclPass := rfl
  janus_run until [body1, head4]
  all_goals simp only [hz, hn, hx, hs, hsh, hE, sub1 m hn64, shr_rd] at hbr ⊢
  · refine h4_lem s hc (m / 4) _ 0 (by omega) ?_ ?r0 ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case r0 =>
      janus_simp; apply BitVec.eq_of_toNat_eq; rw [lsr2_toNat m (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hI => exact rinv_init _ _ x z sh
    case hC => janus_simp
    case hf => exact MemFrame.writeLE (MemFrame.refl _ _) _ (r := (s.sp.toNat + 64, s.sp.toNat + 72)) (by simp) (Nat.le_refl _) (by omega)
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; first | exact hsp | exact h18 | exact h28 | exact h29 | exact h30 | exact hfp | exact htp | exact hdc | exact hex | exact hep) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
  · obtain ⟨j, hj⟩ : ∃ j, m % 4 = j + 1 := ⟨m % 4 - 1, by omega⟩
    refine one_lem s hc (m / 4) j _ 0 (by omega) ?_ ?r6 ?r0 ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case r6 =>
      janus_simp; apply BitVec.eq_of_toNat_eq; rw [and3_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case r0 =>
      janus_simp; apply BitVec.eq_of_toNat_eq; rw [lsr2_toNat m (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hI => exact rinv_init _ _ x z sh
    case hC => janus_simp
    case hf => exact MemFrame.writeLE (MemFrame.refl _ _) _ (r := (s.sp.toNat + 64, s.sp.toNat + 72)) (by simp) (Nat.le_refl _) (by omega)
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; first | exact hsp | exact h18 | exact h28 | exact h29 | exact h30 | exact hfp | exact htp | exact hdc | exact hex | exact hep) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

theorem main_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) (hpc : s.pc = BitVec.ofNat 64 entry) :
    ReachesRet program (s.regs 30) s (fun s' => Ret0 s s' (Q s)) := by
  rcases n with _ | m
  · exact zero_lem s hc hpc
  · exact pos_lem s hc hpc

/-- `rshVU.abi0` as a callee (library summary). -/
theorem rshVU_summary : Summary0 program entry Pre Q :=
  fun s hpc hpre => main_lem s hpre hpc

/-- the standalone contract, for every frame (`lshVU(z, x []Word, s uint) (c Word)`) -/
theorem ensures (z zl zc x xl xc sh : BitVec 64) :
    Ensures0 program entry [z, zl, zc, x, xl, xc, sh] 1
      (fun s => Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        1 ≤ sh.toNat ∧ sh.toNat ≤ 63 ∧
        (z.toNat ≤ x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.sp.toNat + 64) 8 ∧ Apart x.toNat (8 * zl.toNat) (s.sp.toNat + 64) 8)
      (fun s s' =>
        lv s'.mem z.toNat zl.toNat = lv s.mem x.toNat zl.toNat / 2 ^ sh.toNat ∧
        results0 s s' 7 1 = [BitVec.ofNat 64 (lv s.mem x.toNat zl.toNat % 2 ^ sh.toNat * 2 ^ (64 - sh.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), (s.sp.toNat + 64, s.sp.toNat + 72)]) := by
  refine Ensures0.of_summary0 rshVU_summary ?_ ?_
  · intro ret s hret hs ⟨⟨hz1, hz2⟩, ⟨hx1, hx2⟩, sh1, sh63, alx, azr, axr⟩
    have h1 := hret.aligned
    have h2 := hret.user
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at a0 a1 a3 a6
    unfold Pre
    rw [a0, a3, a6, a1]
    refine ⟨a0, a1, a3, a6, ?_, ?_, hs.spAligned, hs.frame_bound, hs.frame_accessible, hz1, hx1, sh1, sh63,
      alx, azr, axr⟩
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
    · rw [hs.lr]; simp only [Program.withExit, BitVec.toNat_ofNat]; omega
  · intro ret s s' hret hs _ hq
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at a0 a1 a3 a6
    unfold Q at hq
    rw [a0, a3, a6, a1] at hq
    obtain ⟨q1, q2, q3⟩ := hq
    refine ⟨q1, ?_, q3⟩
    simp only [results0, wordsAt_succ, wordsAt_zero, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
    rw [show s.sp.toNat + 8 + 8 * 7 = s.sp.toNat + 64 by omega, q2]

end FvModexp.Arm64.RshVUSum
