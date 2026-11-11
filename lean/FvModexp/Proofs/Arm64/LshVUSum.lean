import FvModexp.Proofs.Common.AsmLimbs
import FvModexp.Proofs.Common.AsmShift
import FvModexp.Proofs.Lib.LshVUA64

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec FvModexp.Asm
open FvModexp.Lib.LshVUA64 (program entry)

namespace FvModexp.Arm64.LshVUSum

abbrev head1 : Nat := entry + 0x40
abbrev head4 : Nat := entry + 0x60
abbrev body1 : Nat := entry + 0x44
abbrev body4 : Nat := entry + 0x64
abbrev fin : Nat := entry + 0xac

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
  alx : x ≤ z ∨ Apart z (8 * n) x (8 * n)
  azr : Apart z (8 * n) (s.sp.toNat + 64) 8
  axr : Apart x (8 * n) (s.sp.toNat + 64) 8

def Pre (s : State) : Prop :=
  Ctx s (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8)
    (s.mem.readLE (s.sp.toNat + 56) 8)

def Q (s : State) (m : Memory) : Prop :=
  lv m (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) =
      (lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) *
        2 ^ s.mem.readLE (s.sp.toNat + 56) 8) % 2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  m.readLE (s.sp.toNat + 64) 8 =
      (lv s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) *
        2 ^ s.mem.readLE (s.sp.toNat + 56) 8) / 2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8),
      (s.sp.toNat + 64, s.sp.toNat + 72)]

/-- limbs of `x` strictly below the written range are still intact -/
theorem xr {z x n sh : Nat} {s S : State} (hc : Ctx s z x n sh) (j m : Nat) (hm : m ≤ j) (hj : j + 1 ≤ n)
    (hf : MemFrame s.mem S.mem [(z + 8 * (j + 1), z + 8 * n), (s.sp.toNat + 64, s.sp.toNat + 72)]) :
    S.mem.readLE (x + 8 * m) 8 = s.mem.readLE (x + 8 * m) 8 := by
  obtain ⟨hz, hn, hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc
  exact hf.readLE _ _ (by
    simp only [outside_cons, outside_nil, and_true]
    unfold Apart at alx axr; omega)

theorem frame_wid {m m' : Memory} {a b r1 r2 : Nat} (h : MemFrame m m' [(a, b), (r1, r2)]) (a' : Nat) (ha : a' ≤ a) :
    MemFrame m m' [(a', b), (r1, r2)] :=
  frame_mono h (fun a0 n0 h0 => by
    simp only [outside_cons, outside_nil, and_true] at h0 ⊢; omega)

theorem frame_st {m m' : Memory} {a b r1 r2 : Nat} (h : MemFrame m m' [(a, b), (r1, r2)]) (p v : Nat)
    (h1 : a ≤ p) (h2 : p + 8 ≤ b) : MemFrame m (m'.writeLE p 8 v) [(a, b), (r1, r2)] :=
  MemFrame.writeLE h _ (r := (a, b)) (by simp) h1 h2

theorem fin_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) (S : State) (t C : Nat)
    (hn : t + 1 = n) (hpc : S.pc = BitVec.ofNat 64 fin)
    (r3 : S.regs 3 = BitVec.ofNat 64 (z + 8)) (r4 : S.regs 4 = BitVec.ofNat 64 (s.mem.readLE x 8 * 2 ^ sh))
    (hC : S.mem.readLE (s.sp.toNat + 64) 8 = C) (hI : LInv s.mem S.mem x z n sh 0 t C)
    (hf : MemFrame s.mem S.mem [(z + 8 * (0 + 1), z + 8 * n), (s.sp.toNat + 64, s.sp.toNat + 72)])
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
  have hz8 : z + 8 * (0 + 1) = z + 8 := by omega
  rw [hz8] at hf
  unfold LInv at hI
  rw [hz8] at hI
  have e1 : lv (S.mem.writeLE z 8 (s.mem.readLE x 8 * 2 ^ sh)) z (t + 1) =
      s.mem.readLE x 8 * 2 ^ sh % 2 ^ 64 + 2 ^ 64 * lv S.mem (z + 8) t := by
    rw [lv_cons, Memory.readLE_writeLE_self, lv_wr (by omega)]
  rw [hn'] at *
  have hlt := lv_lt (S.mem.writeLE z 8 (s.mem.readLE x 8 * 2 ^ sh)) z (t + 1)
  rw [e1] at hlt ⊢
  have hP : 0 < 2 ^ (64 * (t + 1)) := Nat.two_pow_pos _
  have hI' : lv s.mem x (t + 1) * 2 ^ sh = (s.mem.readLE x 8 * 2 ^ sh % 2 ^ 64 +
      2 ^ 64 * lv S.mem (z + 8) t) + C * 2 ^ (64 * (t + 1)) := by
    simp only [lv_zero, Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.pow_zero, Nat.one_mul,
      Nat.mul_one, Nat.mul_zero] at hI
    omega
  refine ⟨htp, hdc, hex, hep, ?_, ?_, ?_⟩
  · rw [hI', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  · rw [hI', Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hlt, hC]; simp
  · refine MemFrame.writeLE (frame_mono hf (fun a n' h => ?_)) _ (r := (z, z + 8 * (t + 1))) (by simp) (Nat.le_refl _) (by omega)
    simp only [outside_cons, outside_nil, and_true] at h ⊢; omega

/-- the memory effect of one `1x` iteration (`w` the stored word) -/
theorem one_inv {z x n sh : Nat} {s S : State} (hc : Ctx s z x n sh) (j t C : Nat) (hn : j + 1 + 1 + t = n)
    (hC : S.mem.readLE (s.sp.toNat + 64) 8 = C) (hI : LInv s.mem S.mem x z n sh (j + 1) t C)
    (hf : MemFrame s.mem S.mem [(z + 8 * (j + 1 + 1), z + 8 * n), (s.sp.toNat + 64, s.sp.toNat + 72)]) (w : Nat)
    (hw : w % 2 ^ 64 = s.mem.readLE (x + 8 * j) 8 / 2 ^ (64 - sh) + s.mem.readLE (x + 8 * (j + 1)) 8 * 2 ^ sh % 2 ^ 64) :
    (S.mem.writeLE (z + 8 * (j + 1)) 8 w).readLE (s.sp.toNat + 64) 8 = C ∧
      LInv s.mem (S.mem.writeLE (z + 8 * (j + 1)) 8 w) x z n sh j (t + 1) C ∧
      MemFrame s.mem (S.mem.writeLE (z + 8 * (j + 1)) 8 w) [(z + 8 * (j + 1), z + 8 * n), (s.sp.toNat + 64, s.sp.toNat + 72)] := by
  have hc' := hc
  obtain ⟨hz, hn', hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc'
  refine ⟨?_, linv_step1 s.mem S.mem x z n sh j t C _ sh1 sh63 hI hw, ?_⟩
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega)]; exact hC
  · exact frame_st (frame_wid hf _ (by omega)) _ _ (by omega) (by omega)

/-- the memory effect of one `4x` iteration -/
theorem blk_inv {z x n sh : Nat} {s S : State} (hc : Ctx s z x n sh) (j t C : Nat) (hn : j + 4 + 1 + t = n)
    (hC : S.mem.readLE (s.sp.toNat + 64) 8 = C) (hI : LInv s.mem S.mem x z n sh (j + 4) t C)
    (hf : MemFrame s.mem S.mem [(z + 8 * (j + 4 + 1), z + 8 * n), (s.sp.toNat + 64, s.sp.toNat + 72)])
    (w0 w1 w2 w3 : Nat)
    (hw0 : w0 % 2 ^ 64 = s.mem.readLE (x + 8 * j) 8 / 2 ^ (64 - sh) + s.mem.readLE (x + 8 * (j + 1)) 8 * 2 ^ sh % 2 ^ 64)
    (hw1 : w1 % 2 ^ 64 = s.mem.readLE (x + 8 * (j + 1)) 8 / 2 ^ (64 - sh) + s.mem.readLE (x + 8 * (j + 2)) 8 * 2 ^ sh % 2 ^ 64)
    (hw2 : w2 % 2 ^ 64 = s.mem.readLE (x + 8 * (j + 2)) 8 / 2 ^ (64 - sh) + s.mem.readLE (x + 8 * (j + 3)) 8 * 2 ^ sh % 2 ^ 64)
    (hw3 : w3 % 2 ^ 64 = s.mem.readLE (x + 8 * (j + 3)) 8 / 2 ^ (64 - sh) + s.mem.readLE (x + 8 * (j + 4)) 8 * 2 ^ sh % 2 ^ 64) :
    ((((S.mem.writeLE (z + 8 * (j + 1)) 8 w0).writeLE (z + 8 * (j + 1) + 8) 8 w1).writeLE
      (z + 8 * (j + 1) + 16) 8 w2).writeLE (z + 8 * (j + 1) + 24) 8 w3).readLE (s.sp.toNat + 64) 8 = C ∧
    LInv s.mem ((((S.mem.writeLE (z + 8 * (j + 1)) 8 w0).writeLE (z + 8 * (j + 1) + 8) 8 w1).writeLE
      (z + 8 * (j + 1) + 16) 8 w2).writeLE (z + 8 * (j + 1) + 24) 8 w3) x z n sh j (t + 4) C ∧
    MemFrame s.mem ((((S.mem.writeLE (z + 8 * (j + 1)) 8 w0).writeLE (z + 8 * (j + 1) + 8) 8 w1).writeLE
      (z + 8 * (j + 1) + 16) 8 w2).writeLE (z + 8 * (j + 1) + 24) 8 w3)
      [(z + 8 * (j + 1), z + 8 * n), (s.sp.toNat + 64, s.sp.toNat + 72)] := by
  have hc' := hc
  obtain ⟨hz, hn', hx, hs, hl4, hl56, hal, hfb, hfacc, accz, accx, sh1, sh63, alx, azr, axr⟩ := hc'
  refine ⟨?_, linv_step4 s.mem S.mem x z n sh j t C _ _ _ _ sh1 sh63 hI hw0 hw1 hw2 hw3, ?_⟩
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at azr; omega)]
    exact hC
  · have f0 := frame_wid hf (z + 8 * (j + 1)) (by omega)
    exact frame_st (frame_st (frame_st (frame_st f0 _ _ (by omega) (by omega)) _ _ (by omega) (by omega)) _ _
      (by omega) (by omega)) _ _ (by omega) (by omega)

theorem ow {sh : Nat} (sh1 : 1 ≤ sh) (sh63 : sh ≤ 63) (a b k : Nat) (ha : a < 2 ^ 64) (hk : k = 64 - sh) :
    ((BitVec.ofNat 64 a >>> k).toNat ||| b * 2 ^ sh % 18446744073709551616) % 2 ^ 64 =
      a / 2 ^ (64 - sh) + b * 2 ^ sh % 2 ^ 64 := or_wr a b sh k ha sh1 sh63 hk

theorem blk_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) :
    ∀ k (S : State) (u t C : Nat), u + 1 + t = n → u = 4 * (k + 1) →
      S.pc = BitVec.ofNat 64 body4 → S.regs 0 = BitVec.ofNat 64 (k + 1) →
      S.regs 1 = BitVec.ofNat 64 sh → S.regs 5 = 64#64 - BitVec.ofNat 64 sh →
      S.regs 2 = BitVec.ofNat 64 (x + 8 * u) → S.regs 3 = BitVec.ofNat 64 (z + 8 * (u + 1)) →
      S.regs 4 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * u) 8 * 2 ^ sh) →
      S.mem.readLE (s.sp.toNat + 64) 8 = C → LInv s.mem S.mem x z n sh u t C →
      MemFrame s.mem S.mem [(z + 8 * (u + 1), z + 8 * n), (s.sp.toNat + 64, s.sp.toNat + 72)] →
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
  intro k
  induction k with
  | zero =>
    intro S u t C hu hu' hpc h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    obtain ⟨j, rfl⟩ : ∃ j, u = j + 4 := ⟨u - 4, by omega⟩
    have hj : j = 0 := by omega
    have rx0 := xr hc (j + 4) j (by omega) (by omega) hf
    have rx1 := xr hc (j + 4) (j + 1) (by omega) (by omega) hf
    have rx2 := xr hc (j + 4) (j + 2) (by omega) (by omega) hf
    have rx3 := xr hc (j + 4) (j + 3) (by omega) (by omega) hf
    janus_run until [head4, fin]
    simp only [show x + 8 * (j + 4) - 32 = x + 8 * j by omega, show x + 8 * (j + 4) - 24 = x + 8 * (j + 1) by omega,
      show x + 8 * (j + 4) - 16 = x + 8 * (j + 2) by omega, show x + 8 * (j + 4) - 8 = x + 8 * (j + 3) by omega,
      show z + 8 * (j + 4 + 1) - 32 = z + 8 * (j + 1) by omega,
      show z + 8 * (j + 4 + 1) - 24 = z + 8 * (j + 1) + 8 by omega,
      show z + 8 * (j + 4 + 1) - 16 = z + 8 * (j + 1) + 16 by omega,
      show z + 8 * (j + 4 + 1) - 8 = z + 8 * (j + 1) + 24 by omega, rx0, rx1, rx2, rx3, hsh]
    subst hj
    refine fin_lem s hc _ (t + 4) C (by omega) ?_ ?_ ?_ ?hC ?hI ?hf rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
    case hC => exact (blk_inv hc 0 t C (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).1
    case hI => exact (blk_inv hc 0 t C (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).2.1
    case hf => exact (blk_inv hc 0 t C (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).2.2
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
  | succ k ih =>
    intro S u t C hu hu' hpc h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    obtain ⟨j, rfl⟩ : ∃ j, u = j + 4 := ⟨u - 4, by omega⟩
    have hk : k + 1 + 1 < 2 ^ 64 := by omega
    have rx0 := xr hc (j + 4) j (by omega) (by omega) hf
    have rx1 := xr hc (j + 4) (j + 1) (by omega) (by omega) hf
    have rx2 := xr hc (j + 4) (j + 2) (by omega) (by omega) hf
    have rx3 := xr hc (j + 4) (j + 3) (by omega) (by omega) hf
    janus_run until [body4, fin]
    simp only [show x + 8 * (j + 4) - 32 = x + 8 * j by omega, show x + 8 * (j + 4) - 24 = x + 8 * (j + 1) by omega,
      show x + 8 * (j + 4) - 16 = x + 8 * (j + 2) by omega, show x + 8 * (j + 4) - 8 = x + 8 * (j + 3) by omega,
      show z + 8 * (j + 4 + 1) - 32 = z + 8 * (j + 1) by omega,
      show z + 8 * (j + 4 + 1) - 24 = z + 8 * (j + 1) + 8 by omega,
      show z + 8 * (j + 4 + 1) - 16 = z + 8 * (j + 1) + 16 by omega,
      show z + 8 * (j + 4 + 1) - 8 = z + 8 * (j + 1) + 24 by omega, rx0, rx1, rx2, rx3, hsh]
    refine ih _ j (t + 4) C (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
    case hC => exact (blk_inv hc j t C (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).1
    case hI => exact (blk_inv hc j t C (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).2.1
    case hf => exact (blk_inv hc j t C (by omega) hC hI hf _ _ _ _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega)) (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).2.2
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

theorem h4_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) :
    ∀ (q : Nat) (S : State) (u t C : Nat), u + 1 + t = n → u = 4 * q →
      S.pc = BitVec.ofNat 64 head4 → S.regs 0 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 sh → S.regs 5 = 64#64 - BitVec.ofNat 64 sh →
      S.regs 2 = BitVec.ofNat 64 (x + 8 * u) → S.regs 3 = BitVec.ofNat 64 (z + 8 * (u + 1)) →
      S.regs 4 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * u) 8 * 2 ^ sh) →
      S.mem.readLE (s.sp.toNat + 64) 8 = C → LInv s.mem S.mem x z n sh u t C →
      MemFrame s.mem S.mem [(z + 8 * (u + 1), z + 8 * n), (s.sp.toNat + 64, s.sp.toNat + 72)] →
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
  intro q
  rcases q with _ | k
  · intro S u t C hu hu' hpc h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    have hu0 : u = 0 := by omega
    subst hu0
    janus_run until [fin]
    refine fin_lem s hc _ t C (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (with_reducible rfl) | (with_reducible assumption) | (janus_simp; done) | (janus_simp; assumption) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
  · intro S u t C hu hu' hpc h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    janus_run until [body4]
    refine blk_lem s hc k _ u t C hu (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (with_reducible rfl) | (with_reducible assumption) | (janus_simp; done) | (janus_simp; assumption) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

theorem one_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) (q : Nat) :
    ∀ j (S : State) (u t C : Nat), u + 1 + t = n → u = (j + 1) + 4 * q →
      S.pc = BitVec.ofNat 64 body1 → S.regs 6 = BitVec.ofNat 64 (j + 1) → S.regs 0 = BitVec.ofNat 64 q →
      S.regs 1 = BitVec.ofNat 64 sh → S.regs 5 = 64#64 - BitVec.ofNat 64 sh →
      S.regs 2 = BitVec.ofNat 64 (x + 8 * u) → S.regs 3 = BitVec.ofNat 64 (z + 8 * (u + 1)) →
      S.regs 4 = BitVec.ofNat 64 (s.mem.readLE (x + 8 * u) 8 * 2 ^ sh) →
      S.mem.readLE (s.sp.toNat + 64) 8 = C → LInv s.mem S.mem x z n sh u t C →
      MemFrame s.mem S.mem [(z + 8 * (u + 1), z + 8 * n), (s.sp.toNat + 64, s.sp.toNat + 72)] →
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
  intro j
  induction j with
  | zero =>
    intro S u t C hu hu' hpc h6 h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    obtain ⟨j, rfl⟩ : ∃ j, u = j + 1 := ⟨u - 1, by omega⟩
    have rx0 := xr hc (j + 1) j (by omega) (by omega) hf
    have rx1 := xr hc (j + 1) (j + 1) (by omega) (by omega) hf
    janus_run until [body1, head4]
    simp only [show x + 8 * (j + 1) - 8 = x + 8 * j by omega, show z + 8 * (j + 1 + 1) - 8 = z + 8 * (j + 1) by omega,
      rx0, hsh]
    refine h4_lem s hc q _ j (t + 1) C (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
    case hC => exact (one_inv hc j t C (by omega) hC hI hf _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).1
    case hI => exact (one_inv hc j t C (by omega) hC hI hf _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).2.1
    case hf => exact (one_inv hc j t C (by omega) hC hI hf _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).2.2
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
  | succ j ih =>
    intro S u t C hu hu' hpc h6 h0 h1 h5 h2 h3 h4 hC hI hf hsp h18 h28 h29 h30 hfp htp hdc hex hep
    obtain ⟨j', rfl⟩ : ∃ j', u = j' + 1 := ⟨u - 1, by omega⟩
    have rx0 := xr hc (j' + 1) j' (by omega) (by omega) hf
    have rx1 := xr hc (j' + 1) (j' + 1) (by omega) (by omega) hf
    janus_run until [body1, head4]
    simp only [show x + 8 * (j' + 1) - 8 = x + 8 * j' by omega, show z + 8 * (j' + 1 + 1) - 8 = z + 8 * (j' + 1) by omega,
      rx0, hsh]
    refine ih _ j' (t + 1) C (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf rfl ?_ ?_ ?_ ?_ rfl htp hdc hex hep
    case hC => exact (one_inv hc j' t C (by omega) hC hI hf _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).1
    case hI => exact (one_inv hc j' t C (by omega) hC hI hf _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).2.1
    case hf => exact (one_inv hc j' t C (by omega) hC hI hf _ (ow sh1 sh63 _ _ _ (limb_lt _ _) (by omega))).2.2
    all_goals first | (with_reducible rfl) | (janus_simp; done) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)

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
  have hC0 : (s.mem.writeLE (s.sp.toNat + 64) 8 (BitVec.ofNat 64 (s.mem.readLE (x + 8 * (m + 1) - 8) 8) >>>
        ((18446744073709551616 - sh - 18446744073709551552) % 64)).toNat).readLE (s.sp.toNat + 64) 8 =
      s.mem.readLE (x + 8 * m) 8 / 2 ^ (64 - sh) := by
    rw [Memory.readLE_writeLE_self, show x + 8 * (m + 1) - 8 = x + 8 * m by omega,
      show (18446744073709551616 - sh - 18446744073709551552) % 64 = 64 - sh by omega, BitVec.toNat_ushiftRight,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (limb_lt _ _), Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (limb_lt _ _))
  janus_run until [body1, head4]
  all_goals simp only [hz, hn, hx, hs, hsh, sub1 m hn64, show x + (m + 1) * 8 - 8 = x + 8 * m by omega,
    show (m + 1) * 8 = 8 * (m + 1) by omega] at hbr ⊢
  · refine h4_lem s hc (m / 4) _ m 0 (s.mem.readLE (x + 8 * m) 8 / 2 ^ (64 - sh)) (by omega) (by omega)
      ?_ ?r0 ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case r0 =>
      janus_simp; apply BitVec.eq_of_toNat_eq; rw [lsr2_toNat m (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hI => exact linv_init _ _ x z m sh sh1 sh63
    case hC => exact hC0
    case hf => exact MemFrame.writeLE (MemFrame.refl _ _) _ (r := (s.sp.toNat + 64, s.sp.toNat + 72)) (by simp) (Nat.le_refl _) (by omega)
    all_goals first | (with_reducible rfl) | (with_reducible assumption) | (janus_simp; done) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega) | (janus_simp; simp only [show x + 8 * (m + 1) - 8 = x + 8 * m by omega]; done)
  · obtain ⟨j, hj⟩ : ∃ j, m % 4 = j + 1 := ⟨m % 4 - 1, by omega⟩
    refine one_lem s hc (m / 4) j _ m 0 (s.mem.readLE (x + 8 * m) 8 / 2 ^ (64 - sh)) (by omega) (by omega)
      ?_ ?r6 ?r0 ?_ ?_ ?_ ?_ ?_ ?hC ?hI ?hf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case r6 =>
      janus_simp; apply BitVec.eq_of_toNat_eq; rw [and3_toNat, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case r0 =>
      janus_simp; apply BitVec.eq_of_toNat_eq; rw [lsr2_toNat m (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    case hI => exact linv_init _ _ x z m sh sh1 sh63
    case hC => exact hC0
    case hf => exact MemFrame.writeLE (MemFrame.refl _ _) _ (r := (s.sp.toNat + 64, s.sp.toNat + 72)) (by simp) (Nat.le_refl _) (by omega)
    all_goals first | (with_reducible rfl) | (with_reducible assumption) | (janus_simp; done) | (janus_simp; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega) | (janus_simp; simp only [show x + 8 * (m + 1) - 8 = x + 8 * m by omega]; done)

theorem main_lem {z x n sh : Nat} (s : State) (hc : Ctx s z x n sh) (hpc : s.pc = BitVec.ofNat 64 entry) :
    ReachesRet program (s.regs 30) s (fun s' => Ret0 s s' (Q s)) := by
  rcases n with _ | m
  · exact zero_lem s hc hpc
  · exact pos_lem s hc hpc

/-- `lshVU.abi0` as a callee (library summary). -/
theorem lshVU_summary : Summary0 program entry Pre Q :=
  fun s hpc hpre => main_lem s hpre hpc

/-- the standalone contract, for every frame (`lshVU(z, x []Word, s uint) (c Word)`) -/
theorem ensures (z zl zc x xl xc sh : BitVec 64) :
    Ensures0 program entry [z, zl, zc, x, xl, xc, sh] 1
      (fun s => Ptr s.mem z (8 * zl.toNat) true ∧ Ptr s.mem x (8 * zl.toNat) false ∧
        1 ≤ sh.toNat ∧ sh.toNat ≤ 63 ∧
        (x.toNat ≤ z.toNat ∨ Apart z.toNat (8 * zl.toNat) x.toNat (8 * zl.toNat)) ∧
        Apart z.toNat (8 * zl.toNat) (s.sp.toNat + 64) 8 ∧ Apart x.toNat (8 * zl.toNat) (s.sp.toNat + 64) 8)
      (fun s s' =>
        lv s'.mem z.toNat zl.toNat = (lv s.mem x.toNat zl.toNat * 2 ^ sh.toNat) % 2 ^ (64 * zl.toNat) ∧
        results0 s s' 7 1 = [BitVec.ofNat 64 ((lv s.mem x.toNat zl.toNat * 2 ^ sh.toNat) / 2 ^ (64 * zl.toNat))] ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 8 * zl.toNat), (s.sp.toNat + 64, s.sp.toNat + 72)]) := by
  refine Ensures0.of_summary0 lshVU_summary ?_ ?_
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

end FvModexp.Arm64.LshVUSum
