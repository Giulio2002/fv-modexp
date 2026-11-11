import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Common.AsmTac
import FvModexp.Proofs.Common.AsmShift
import FvModexp.Proofs.Lib.RshVUAmd64

/-!
# `math/big.rshVU.abi0` (go-bigmodexpfix arith_amd64.s:178, ABI0, amd64): library summary

`rshVU(z, x []Word, s uint) (c Word)`, forward loop with `SHRQ CX, hi, lo` (`SHRD`):
`c = x[0] << (64-s)`, `z[i] = x[i] >> s | x[i+1] << (64-s)`, `z[n-1] = x[n-1] >> s`. Value form (as arm64):
`Z = X >> s`, `c = (X mod 2^s) · 2^(64-s)` (invariant `Common/AsmShift.lean` `RInv`; the loop register holds the
unshifted limb `x[u]`). One `janus64_run` per declaration: `zero_lem`/`pos_lem`, `one_lem` (induction), `h4_lem`,
`blk_lem` (induction), `fin_lem`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.RshVUAmd64 (program entry)

namespace FvModexp.Amd64.RshVUSum

abbrev body1 : Nat := entry + 0x44
abbrev head4 : Nat := entry + 0x60
abbrev body4 : Nat := entry + 0x65
abbrev fin : Nat := entry + 0xa5

/-- the preconditions at the entry (frame words above the return address: `z, len, cap, x, len, cap, s, c`) -/
structure Ctx (s : State) (z x n sh : Nat) : Prop where
  hz : s.mem.readLE ((s.regs 4).toNat + 8) 8 = z
  hn : s.mem.readLE ((s.regs 4).toNat + 16) 8 = n
  hx : s.mem.readLE ((s.regs 4).toNat + 32) 8 = x
  hs : s.mem.readLE ((s.regs 4).toNat + 56) 8 = sh
  hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  fb : (s.regs 4).toNat + 72 ≤ 2 ^ 48
  facc : s.mem.accessible (s.regs 4).toNat 72 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  sh1 : 1 ≤ sh
  sh63 : sh ≤ 63
  alx : z ≤ x ∨ Apart z (8 * n) x (8 * n)
  azf : Apart z (8 * n) (s.regs 4).toNat 72
  axr : Apart x (8 * n) ((s.regs 4).toNat + 64) 8

def Pre (s : State) : Prop :=
  Ctx s (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 32) 8)
    (s.mem.readLE ((s.regs 4).toNat + 16) 8) (s.mem.readLE ((s.regs 4).toNat + 56) 8)

/-- the memory after the call: `Z = X >> s`, `c = (X mod 2^s) · 2^(64-s)` -/
def Q (s : State) (m : Memory) : Prop :=
  lv m (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) =
      lv s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) /
        2 ^ s.mem.readLE ((s.regs 4).toNat + 56) 8 ∧
  m.readLE ((s.regs 4).toNat + 64) 8 =
      lv s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) %
        2 ^ s.mem.readLE ((s.regs 4).toNat + 56) 8 * 2 ^ (64 - s.mem.readLE ((s.regs 4).toNat + 56) 8) ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)]

theorem xr {z x n sh : Nat} {s S : State} (hc : Ctx s z x n sh) (u m : Nat) (hm : u ≤ m) (hj : m + 1 ≤ n)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * u), ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)]) :
    S.mem.readLE (x + 8 * m) 8 = s.mem.readLE (x + 8 * m) 8 := by
  obtain ⟨hz, hn, hx, hs, hr, hfb, hfacc, accz, accx, sh1, sh63, alx, azf, axr⟩ := hc
  exact hf.readLE _ _ (by
    simp only [outside_cons, outside_nil, and_true]
    unfold Apart at alx axr; omega)

theorem fin_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) (S : State) (t : Nat)
    (hn : t + 1 = n) (hpc : S.rip = BitVec.ofNat 64 fin) (r1 : S.regs 1 = BitVec.ofNat 64 sh)
    (r7 : S.regs 7 = BitVec.ofNat 64 (z + 8 * t)) (r8 : S.regs 8 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * t) 8))
    (hC : S.mem.readLE ((s.regs 4).toNat + 64) 8 = s.mem.readLE x 8 * 2 ^ (64 - sh) % 2 ^ 64)
    (hI : RInv s.mem S.mem x z sh t)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * t), ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)])
    (hs : Same64 s S) :
    ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn', hx, hs', hr, hfb, hfacc, accz, accx, sh1, sh63, alx, azf, axr⟩ := hc'
  obtain ⟨h4, h5, hfs, hdf, hmx, h87, hfw⟩ := hs
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have hsh : sh % 64 = sh := Nat.mod_eq_of_lt (by omega)
  unfold Apart at azf
  have hra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
    hf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  janus64_run [Q]
  subst hn
  simp only [hsh]
  have hv : (BitVec.ofNat 64 (s.mem.readLE (x + 8 * t) 8) >>> sh).toNat % 2 ^ 64 = s.mem.readLE (x + 8 * t) 8 / 2 ^ sh := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (limb_lt _ _), Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (limb_lt _ _))
  obtain ⟨e1, e2⟩ := rinv_fin s.mem S.mem x z sh t _ hI hv
  refine ⟨hfs, hfw, h87, e1, ?_, ?_⟩
  · rw [e2, shr_lo_eq _ _ sh1 sh63, Nat.mul_comm]
  · refine MemFrame.writeLE (frame_mono hf (fun a n' h => ?_)) _ (r := (z, z + 8 * (t + 1))) (by simp) (by omega) (by omega)
    simp only [outside_cons, outside_nil, and_true] at h ⊢; omega

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

/-- the memory effect of one `1x` iteration (`w` the stored word) -/
theorem one_inv {z x n sh : Nat} {s S : State} (hc : Ctx s z x n sh) (u C : Nat) (hn : u + 2 ≤ n)
    (hC : S.mem.readLE ((s.regs 4).toNat + 64) 8 = C) (hI : RInv s.mem S.mem x z sh u)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * u), ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)]) (w : Nat)
    (hw : w % 2 ^ 64 = s.mem.readLE (x + 8 * u) 8 / 2 ^ sh + s.mem.readLE (x + 8 * (u + 1)) 8 * 2 ^ (64 - sh) % 2 ^ 64) :
    (S.mem.writeLE (z + 8 * u) 8 w).readLE ((s.regs 4).toNat + 64) 8 = C ∧
      RInv s.mem (S.mem.writeLE (z + 8 * u) 8 w) x z sh (u + 1) ∧
      MemFrame s.mem (S.mem.writeLE (z + 8 * u) 8 w) [(z, z + 8 * (u + 1)), ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)] := by
  have hc' := hc
  obtain ⟨hz, hn', hx, hs, hr, hfb, hfacc, accz, accx, sh1, sh63, alx, azf, axr⟩ := hc'
  refine ⟨?_, rinv_step1 s.mem S.mem x z sh u w sh1 sh63 hI hw, frame_st hf _⟩
  rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azf; omega)]; exact hC

/-- the memory effect of one `4x` iteration -/
theorem blk_inv {z x n sh : Nat} {s S : State} (hc : Ctx s z x n sh) (u C : Nat) (hn : u + 5 ≤ n)
    (hC : S.mem.readLE ((s.regs 4).toNat + 64) 8 = C) (hI : RInv s.mem S.mem x z sh u)
    (hf : MemFrame s.mem S.mem [(z, z + 8 * u), ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)])
    (w0 w1 w2 w3 : Nat)
    (hw0 : w0 % 2 ^ 64 = s.mem.readLE (x + 8 * u) 8 / 2 ^ sh + s.mem.readLE (x + 8 * (u + 1)) 8 * 2 ^ (64 - sh) % 2 ^ 64)
    (hw1 : w1 % 2 ^ 64 = s.mem.readLE (x + 8 * (u + 1)) 8 / 2 ^ sh + s.mem.readLE (x + 8 * (u + 2)) 8 * 2 ^ (64 - sh) % 2 ^ 64)
    (hw2 : w2 % 2 ^ 64 = s.mem.readLE (x + 8 * (u + 2)) 8 / 2 ^ sh + s.mem.readLE (x + 8 * (u + 3)) 8 * 2 ^ (64 - sh) % 2 ^ 64)
    (hw3 : w3 % 2 ^ 64 = s.mem.readLE (x + 8 * (u + 3)) 8 / 2 ^ sh + s.mem.readLE (x + 8 * (u + 4)) 8 * 2 ^ (64 - sh) % 2 ^ 64) :
    ((((S.mem.writeLE (z + 8 * u) 8 w0).writeLE (z + 8 * u + 8) 8 w1).writeLE
      (z + 8 * u + 16) 8 w2).writeLE (z + 8 * u + 24) 8 w3).readLE ((s.regs 4).toNat + 64) 8 = C ∧
    RInv s.mem ((((S.mem.writeLE (z + 8 * u) 8 w0).writeLE (z + 8 * u + 8) 8 w1).writeLE
      (z + 8 * u + 16) 8 w2).writeLE (z + 8 * u + 24) 8 w3) x z sh (u + 4) ∧
    MemFrame s.mem ((((S.mem.writeLE (z + 8 * u) 8 w0).writeLE (z + 8 * u + 8) 8 w1).writeLE
      (z + 8 * u + 16) 8 w2).writeLE (z + 8 * u + 24) 8 w3)
      [(z, z + 8 * (u + 4)), ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)] := by
  have hc' := hc
  obtain ⟨hz, hn', hx, hs, hr, hfb, hfacc, accz, accx, sh1, sh63, alx, azf, axr⟩ := hc'
  refine ⟨?_, rinv_step4 s.mem S.mem x z sh u _ _ _ _ sh1 sh63 hI hw0 hw1 hw2 hw3, frame_st4 hf _ _ _ _⟩
  rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azf; omega),
    Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azf; omega),
    Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azf; omega),
    Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azf; omega)]
  exact hC

theorem blk_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) :
    ∀ k (S : State) (u : Nat), u + 4 * (k + 1) + 1 = n →
      S.rip = BitVec.ofNat 64 body4 → S.regs 3 = BitVec.ofNat 64 (k + 1) →
      S.regs 1 = BitVec.ofNat 64 sh →
      S.regs 6 = BitVec.ofNat 64 (x + 8 * u) → S.regs 7 = BitVec.ofNat 64 (z + 8 * u) →
      S.regs 8 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * u) 8) →
      S.mem.readLE ((s.regs 4).toNat + 64) 8 = s.mem.readLE x 8 * 2 ^ (64 - sh) % 2 ^ 64 → RInv s.mem S.mem x z sh u →
      MemFrame s.mem S.mem [(z, z + 8 * u), ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)] →
      Same64 s S → ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hs, hr, hfb, hfacc, accz, accx, sh1, sh63, alx, azf, axr⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have hsh : sh % 64 = sh := Nat.mod_eq_of_lt (by omega)
  have hn64 : n < 2 ^ 64 := by omega
  intro k
  induction k with
  | zero =>
    intro S u hu hpc h3 h1 h6 h7 h8 hC hI hf hs
    have rx1 := xr hc u (u + 1) (by omega) (by omega) hf
    have rx2 := xr hc u (u + 2) (by omega) (by omega) hf
    have rx3 := xr hc u (u + 3) (by omega) (by omega) hf
    have rx4 := xr hc u (u + 4) (by omega) (by omega) hf
    janus64_run until [body4, fin]
    simp only [hsh, show x + 8 * u + 8 = x + 8 * (u + 1) by omega, show x + 8 * u + 16 = x + 8 * (u + 2) by omega,
      show x + 8 * u + 24 = x + 8 * (u + 3) by omega, show x + 8 * u + 32 = x + 8 * (u + 4) by omega,
      rx1, rx2, rx3, rx4]
    refine fin_lem s hc _ (u + 4) (by omega) rfl ?_ ?_ ?_ ?hC ?hI ?hf (by same64_tac hs)
    case hC => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).1
    case hI => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).2.1
    case hf => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).2.2
    all_goals first | (with_reducible rfl) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h1, h3, h6, h7, h8, Nat.mul_zero, Nat.add_zero]; first | done | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))
  | succ k ih =>
    intro S u hu hpc h3 h1 h6 h7 h8 hC hI hf hs
    have rx1 := xr hc u (u + 1) (by omega) (by omega) hf
    have rx2 := xr hc u (u + 2) (by omega) (by omega) hf
    have rx3 := xr hc u (u + 3) (by omega) (by omega) hf
    have rx4 := xr hc u (u + 4) (by omega) (by omega) hf
    have hk : k + 1 + 1 < 2 ^ 64 := by omega
    janus64_run until [body4, fin]
    simp only [hsh, show x + 8 * u + 8 = x + 8 * (u + 1) by omega, show x + 8 * u + 16 = x + 8 * (u + 2) by omega,
      show x + 8 * u + 24 = x + 8 * (u + 3) by omega, show x + 8 * u + 32 = x + 8 * (u + 4) by omega,
      rx1, rx2, rx3, rx4]
    refine ih _ (u + 4) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf (by same64_tac hs)
    case hC => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).1
    case hI => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).2.1
    case hf => exact (blk_inv hc u _ (by omega) hC hI hf _ _ _ _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63) (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).2.2
    all_goals first | (with_reducible rfl) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h1, h3, h6, h7, h8, Nat.mul_zero, Nat.add_zero]; first | done | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))

theorem h4_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) :
    ∀ (q : Nat) (S : State) (u : Nat), u + 4 * q + 1 = n →
      S.rip = BitVec.ofNat 64 head4 → S.regs 3 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 sh →
      S.regs 6 = BitVec.ofNat 64 (x + 8 * u) → S.regs 7 = BitVec.ofNat 64 (z + 8 * u) →
      S.regs 8 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * u) 8) →
      S.mem.readLE ((s.regs 4).toNat + 64) 8 = s.mem.readLE x 8 * 2 ^ (64 - sh) % 2 ^ 64 → RInv s.mem S.mem x z sh u →
      MemFrame s.mem S.mem [(z, z + 8 * u), ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)] →
      Same64 s S → ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hs, hr, hfb, hfacc, accz, accx, sh1, sh63, alx, azf, axr⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have hsh : sh % 64 = sh := Nat.mod_eq_of_lt (by omega)
  have hn64 : n < 2 ^ 64 := by omega
  intro q
  rcases q with _ | k
  · intro S u hu hpc h3 h1 h6 h7 h8 hC hI hf hs
    janus64_run until [fin]
    refine fin_lem s hc _ u (by omega) rfl ?_ ?_ ?_ hC hI hf (by same64_tac hs)
    all_goals first | (with_reducible rfl) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h1, h3, h6, h7, h8, Nat.mul_zero, Nat.add_zero]; first | done | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))
  · intro S u hu hpc h3 h1 h6 h7 h8 hC hI hf hs
    janus64_run until [body4]
    refine blk_lem s hc k _ u (by omega) rfl ?_ ?_ ?_ ?_ ?_ hC hI hf (by same64_tac hs)
    all_goals first | (with_reducible rfl) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h1, h3, h6, h7, h8, Nat.mul_zero, Nat.add_zero]; first | done | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))

theorem one_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) (q : Nat) :
    ∀ j (S : State) (u : Nat), u + (j + 1) + 4 * q + 1 = n →
      S.rip = BitVec.ofNat 64 body1 → S.regs 9 = BitVec.ofNat 64 (j + 1) → S.regs 3 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 sh →
      S.regs 6 = BitVec.ofNat 64 (x + 8 * u) → S.regs 7 = BitVec.ofNat 64 (z + 8 * u) →
      S.regs 8 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * u) 8) →
      S.mem.readLE ((s.regs 4).toNat + 64) 8 = s.mem.readLE x 8 * 2 ^ (64 - sh) % 2 ^ 64 → RInv s.mem S.mem x z sh u →
      MemFrame s.mem S.mem [(z, z + 8 * u), ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)] →
      Same64 s S → ReachesRet program (retAddrOf s) S (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hs, hr, hfb, hfacc, accz, accx, sh1, sh63, alx, azf, axr⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have hsh : sh % 64 = sh := Nat.mod_eq_of_lt (by omega)
  have hn64 : n < 2 ^ 64 := by omega
  intro j
  induction j with
  | zero =>
    intro S u hu hpc h9 h3 h1 h6 h7 h8 hC hI hf hs
    have rx1 := xr hc u (u + 1) (by omega) (by omega) hf
    janus64_run until [body1, head4]
    simp only [hsh, show x + 8 * u + 8 = x + 8 * (u + 1) by omega, rx1]
    refine h4_lem s hc q _ (u + 1) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf (by same64_tac hs)
    case hC => exact (one_inv hc u _ (by omega) hC hI hf _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).1
    case hI => exact (one_inv hc u _ (by omega) hC hI hf _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).2.1
    case hf => exact (one_inv hc u _ (by omega) hC hI hf _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).2.2
    all_goals first | (with_reducible rfl) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h1, h3, h6, h7, h8, Nat.mul_zero, Nat.add_zero]; first | done | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))
  | succ j ih =>
    intro S u hu hpc h9 h3 h1 h6 h7 h8 hC hI hf hs
    have rx1 := xr hc u (u + 1) (by omega) (by omega) hf
    janus64_run until [body1, head4]
    simp only [hsh, show x + 8 * u + 8 = x + 8 * (u + 1) by omega, rx1]
    refine ih _ (u + 1) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf (by same64_tac hs)
    case hC => exact (one_inv hc u _ (by omega) hC hI hf _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).1
    case hI => exact (one_inv hc u _ (by omega) hC hI hf _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).2.1
    case hf => exact (one_inv hc u _ (by omega) hC hI hf _ (shrd_w _ _ _ (limb_lt _ _) sh1 sh63)).2.2
    all_goals first | (with_reducible rfl) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, h1, h3, h6, h7, h8, Nat.mul_zero, Nat.add_zero]; first | done | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))

theorem sub1 (m : Nat) (h : m + 1 < 2 ^ 64) : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem lsr2' (n : Nat) (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n >>> 2).toNat = n / 4 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]

theorem zero_lem {z x sh : Nat} (s : State) (hc : Ctx s z x 0 sh) (hpc : s.rip = BitVec.ofNat 64 entry) :
    ReachesRet program (retAddrOf s) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hs, hr, hfb, hfacc, accz, accx, sh1, sh63, alx, azf, axr⟩ := hc'
  janus64_run [Q]
  all_goals try simp [lv_zero]
  exact MemFrame.writeLE (MemFrame.refl _ _) _ (r := ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)) (by simp)
    (Nat.le_refl _) (Nat.le_refl _)

theorem pos_lem {z x m sh : Nat} (s : State) (hc : Ctx s z x (m + 1) sh) (hpc : s.rip = BitVec.ofNat 64 entry) :
    ReachesRet program (retAddrOf s) s (fun s' => Ret0 s s' (Q s)) := by
  have hc' := hc
  obtain ⟨hz, hn, hx, hs, hr, hfb, hfacc, accz, accx, sh1, sh63, alx, azf, axr⟩ := hc'
  have bz := Arm64.Memory.accessible_bound _ accz
  have bx := Arm64.Memory.accessible_bound _ accx
  have hsh : sh % 64 = sh := Nat.mod_eq_of_lt (by omega)
  have hn64 : m + 1 < 2 ^ 64 := by omega
  have hs0 := Same64.refl s
  have hC0 : (s.mem.writeLE ((s.regs 4).toNat + 64) 8 (s.mem.readLE x 8 * 18446744073709551616 / 2 ^ sh)).readLE
      ((s.regs 4).toNat + 64) 8 = s.mem.readLE x 8 * 2 ^ (64 - sh) % 2 ^ 64 := by
    have e : (18446744073709551616 : Nat) = 2 ^ (64 - sh) * 2 ^ sh := by
      rw [← Nat.pow_add, show 64 - sh + sh = 64 by omega]
    rw [Arm64.Memory.readLE_writeLE_self, e, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos sh)]
  janus64_run until [body1, head4]
  all_goals simp only [hz, hn, hx, hs, hsh, sub1 m hn64] at hbr ⊢
  · refine h4_lem s hc (m / 4) _ 0 (by omega) rfl ?r3 ?_ ?_ ?_ ?_ ?hC (rinv_init _ _ x z sh) ?hf (by same64_tac hs0)
    case r3 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq
      rw [lsr2' m (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hC => simpa using hC0
    case hf => exact MemFrame.writeLE (MemFrame.refl _ _) _ (r := ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)) (by simp) (Nat.le_refl _) (by omega)
    all_goals first | (with_reducible rfl) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.mul_zero, Nat.add_zero]; first | done | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))
  · obtain ⟨j, hj⟩ : ∃ j, m % 4 = j + 1 := ⟨m % 4 - 1, by omega⟩
    refine one_lem s hc (m / 4) j _ 0 (by omega) rfl ?r9 ?r3 ?_ ?_ ?_ ?_ ?hC (rinv_init _ _ x z sh) ?hf (by same64_tac hs0)
    case r9 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq
      rw [and3_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case r3 =>
      simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff]; apply BitVec.eq_of_toNat_eq
      rw [lsr2' m (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hC => simpa using hC0
    case hf => exact MemFrame.writeLE (MemFrame.refl _ _) _ (r := ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)) (by simp) (Nat.le_refl _) (by omega)
    all_goals first | (with_reducible rfl) | (simp only [setRegF_apply, ↓reduceIte, Nat.reduceEqDiff, Nat.mul_zero, Nat.add_zero]; first | done | (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega))

theorem main_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) (hpc : s.rip = BitVec.ofNat 64 entry) :
    ReachesRet program (retAddrOf s) s (fun s' => Ret0 s s' (Q s)) := by
  rcases n with _ | m
  · exact zero_lem s hc hpc
  · exact pos_lem s hc hpc

/-- `rshVU.abi0` as a callee (library summary). -/
theorem rshVU_summary : Summary0 program entry Pre Q :=
  fun s hpc hpre => main_lem s hpre hpc

/-- the standalone contract, for every frame (`rshVU(z, x []Word, s uint) (c Word)`) -/
theorem ensures (z zl zc x xl xc sh : BitVec 64) :
    Ensures0 program entry [z, zl, zc, x, xl, xc, sh] 1
      (fun s => Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        1 ≤ sh.toNat ∧ sh.toNat ≤ 63 ∧
        (z.toNat ≤ x.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.regs 4).toNat 72 ∧ Apart x.toNat (8 * zl.toNat) ((s.regs 4).toNat + 64) 8)
      (fun s s' =>
        lv s'.mem z.toNat zl.toNat = lv s.mem x.toNat zl.toNat / 2 ^ sh.toNat ∧
        results0 s s' 7 1 = [BitVec.ofNat 64 (lv s.mem x.toNat zl.toNat % 2 ^ sh.toNat * 2 ^ (64 - sh.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)]) := by
  refine Ensures0.of_summary0 rshVU_summary ?_ ?_
  · intro ret s hret hs ⟨⟨hz1, hz2⟩, ⟨hx1, hx2⟩, sh1, sh63, alx, azr, axr⟩
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Janus.Amd64.GoABI.regSP] at a0 a1 a3 a6
    have hfa := hs.frame_accessible
    have hfb := hs.frame_bound
    simp only [List.length_cons, List.length_nil, Janus.Amd64.GoABI.regSP, Nat.reduceAdd, Nat.reduceMul,
      Nat.add_assoc] at hfa hfb
    have hr := hs.ret
    simp only [Amd64.Program.withExit, Janus.Amd64.GoABI.regSP] at hr
    unfold Pre
    rw [a0, a3, a6, a1]
    exact ⟨a0, a1, a3, a6, by rw [hr]; exact hret.user, by omega, hfa, hz1, hx1, sh1, sh63, alx, azr, axr⟩
  · intro ret s s' hret hs _ hq
    have a0 := hs.arg (i := 0) (by simp)
    have a1 := hs.arg (i := 1) (by simp)
    have a3 := hs.arg (i := 3) (by simp)
    have a6 := hs.arg (i := 6) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero, Nat.add_zero,
      Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Janus.Amd64.GoABI.regSP] at a0 a1 a3 a6
    unfold Q at hq
    rw [a0, a3, a6, a1] at hq
    obtain ⟨q1, q2, q3⟩ := hq
    refine ⟨q1, ?_, q3⟩
    simp only [results0, wordsAt_succ, wordsAt_zero, Janus.Amd64.GoABI.regSP, Nat.reduceMul, Nat.reduceAdd]
    rw [show (s.regs 4).toNat + 8 + 56 = (s.regs 4).toNat + 64 by omega, q2]

end FvModexp.Amd64.RshVUSum
