import FvModexp.Proofs.Arm64.Exp.LibExp
import FvModexp.Proofs.Common.ExpMont

/-!
# window-2 (arm64): the inlined `computeMontgomeryk0` Newton loop (nat.go:1273-1284, fn+0x36c .. fn+0x374)

Loop head `kHead` = fn+0x36c (`CMP $64, R1; BLT body`), body fn+0x35c (`R9 *= R9; R14 = R9 + 1; R1 += R1; R13 *= R14`),
exit `kExit` = fn+0x374 with `R13 = newton 64 m0` (the value before the final negation, `Exp.newtonLoop`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

abbrev kHead : Nat := 1802780
abbrev kExit : Nat := 1802788

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- one test of the Newton loop -/
theorem kIter (impl : List Segment) (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (S : State) (j t k : Nat) (hj : j ≤ 6) (ht : t < 2 ^ 64) (hk : k < 2 ^ 64)
    (hpc : S.pc = BitVec.ofNat 64 kHead) (h1 : S.regs 1 = BitVec.ofNat 64 (2 ^ j))
    (h9 : S.regs 9 = BitVec.ofNat 64 t) (h13 : S.regs 13 = BitVec.ofNat 64 k)
    (KE : ∀ S' : State, ¬ 2 ^ j < 64 → S'.pc = BitVec.ofNat 64 kExit → S'.sp = S.sp → S'.mem = S.mem →
      S'.regs 13 = BitVec.ofNat 64 k →
      (∀ i, i ≠ 1 → i ≠ 9 → i ≠ 13 → i ≠ 14 → S'.regs i = S.regs i) →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q)
    (KL : ∀ S' : State, 2 ^ j < 64 → S'.pc = BitVec.ofNat 64 kHead → S'.sp = S.sp → S'.mem = S.mem →
      S'.regs 1 = BitVec.ofNat 64 (2 ^ (j + 1)) → S'.regs 9 = BitVec.ofNat 64 (t * t % 2 ^ 64) →
      S'.regs 13 = BitVec.ofNat 64 (k * ((t * t % 2 ^ 64 + 1) % 2 ^ 64) % 2 ^ 64) →
      (∀ i, i ≠ 1 → i ≠ 9 → i ≠ 13 → i ≠ 14 → S'.regs i = S.regs i) →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have hp : 2 ^ j ≤ 64 := by
    calc 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) hj
      _ = 64 := by rfl
  by_cases hlt : 2 ^ j < 64
  · have hbr : (BitVec.ofNat 64 (2 ^ j)).toInt < (64 : Int) := by
      have e : (BitVec.ofNat 64 (2 ^ j)).toNat = 2 ^ j := Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toInt_eq_toNat_cond, e]; split <;> omega
    janus_run [hbr] until [kHead]
    refine KL _ hlt ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip
    · janus_simp; apply BitVec.eq_of_toNat_eq; simp [Nat.pow_succ]; omega
    · janus_simp; apply BitVec.eq_of_toNat_eq; simp
    · janus_simp; apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]
    · intro i a1 a2 a3 a4; first | (janus_simp; done) | (janus_simp; simp [a1, a2, a3, a4])
  · janus_run until [kExit]
    refine KE _ hlt ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip
    · intro i a1 a2 a3 a4; first | (janus_simp; done) | (janus_simp; simp [a1, a2, a3, a4])

/-- the whole Newton loop from its head (`j` doublings done) -/
theorem kLoop (impl : List Segment) (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop) :
    ∀ (d j t k : Nat) (S : State), j + d = 6 → t < 2 ^ 64 → k < 2 ^ 64 →
      S.pc = BitVec.ofNat 64 kHead → S.regs 1 = BitVec.ofNat 64 (2 ^ j) →
      S.regs 9 = BitVec.ofNat 64 t → S.regs 13 = BitVec.ofNat 64 k →
      (∀ S' : State, S'.pc = BitVec.ofNat 64 kExit → S'.sp = S.sp → S'.mem = S.mem →
        S'.regs 13 = BitVec.ofNat 64 (Exp.newtonLoop 64 j t k) →
        (∀ i, i ≠ 1 → i ≠ 9 → i ≠ 13 → i ≠ 14 → S'.regs i = S.regs i) →
        Reaches ((LibExp.program.link impl).withExit ret) S' Q) →
      Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  intro d
  induction d with
  | zero =>
    intro j t k S hd ht hk hpc h1 h9 h13 KE
    refine kIter impl ret hret Q S j t k (by omega) ht hk hpc h1 h9 h13 ?_ ?_
    · intro S' hn a1 a2 a3 a4 a5
      refine KE S' a1 a2 a3 ?_ a5
      have e : Exp.newtonLoop 64 j t k = k := by rw [Exp.newtonLoop, dif_neg hn]
      rw [a4, e]
    · intro S' hn; subst hd; exact absurd hn (by decide)
  | succ d ih =>
    intro j t k S hd ht hk hpc h1 h9 h13 KE
    refine kIter impl ret hret Q S j t k (by omega) ht hk hpc h1 h9 h13 ?_ ?_
    · intro S' hn
      have : 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right (by omega) (by omega)
      exact absurd this hn
    · intro S' hn a1 a2 a3 a4 a5 a6 a7
      refine ih (j + 1) _ _ S' (by omega) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) a1 a4 a5 a6 ?_
      intro S'' b1 b2 b3 b4 b5
      refine KE S'' b1 (b2.trans a2) (b3.trans a3) ?_ (fun i c1 c2 c3 c4 => (b5 i c1 c2 c3 c4).trans (a7 i c1 c2 c3 c4))
      have e : Exp.newtonLoop 64 j t k = Exp.newtonLoop 64 (j + 1) (t * t % Exp.B)
          (k * ((t * t % Exp.B + 1) % Exp.B) % Exp.B) := by rw [Exp.newtonLoop, dif_pos hn]
      rw [b4, e]
      simp only [Exp.B_def]

end FvModexp.Arm64.W2Pro
