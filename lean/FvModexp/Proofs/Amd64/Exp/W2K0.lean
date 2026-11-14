import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.W2Seg
import FvModexp.Proofs.Common.ExpMont

set_option autoImplicit false

/-!
# window-2 (amd64): the inlined `computeMontgomeryk0` Newton loop (nat.go:1273-1284; agent expmc s47)

Port of `Amd64.W4Pro.kLoop` (expmc s62). Loop head `kHead` = fn+0x4ec (`CMPQ R15, $0x40; JL body`), body fn+0x4d4
(`IMULQ R12, R12; LEAQ 1(R12), R11; ADDQ R15, R15; IMULQ R11, R13; MOVQ 0x280(SP), R11` — the window-2 code hoists
the `len y` reload into the loop: R11 is dead), exit `kExit` = fn+0x4f2 with `R13 = newton 64 m0` (the value before the
final negation, `Exp.newtonLoop`). Entered from fn+0x458 (`JMP kHead`) with `R15 = 1`, `R12 = m0 - 1`, `R13 = 2 - m0`.
The reload needs the frame readable: `sp`, `hsp`, `hacc`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

abbrev kHead : Nat := 6211820
abbrev kExit : Nat := 6211826

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- one test of the Newton loop -/
theorem kIter {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    (S : State) (j t k : Nat) (hj : j ≤ 6) (ht : t < 2 ^ 64) (hk : k < 2 ^ 64)
    (hpc : S.rip = BitVec.ofNat 64 kHead) (sp : Nat) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (hs1 : 4296 ≤ sp) (hs2 : sp + 0x2a8 ≤ 2 ^ 48) (hacc : S.mem.accessible (sp - 4296) (4296 + 0x2a8) true = true)
    (h13 : S.regs 15 = BitVec.ofNat 64 (2 ^ j))
    (h11 : S.regs 12 = BitVec.ofNat 64 t) (h12 : S.regs 13 = BitVec.ofNat 64 k) (hdf : S.df = false)
    (KE : ∀ S' : State, ¬ 2 ^ j < 64 → S'.rip = BitVec.ofNat 64 kExit → S'.mem = S.mem →
      S'.regs 13 = BitVec.ofNat 64 k → S'.xmm = S.xmm → S'.fsBase = S.fsBase → S'.df = false →
      (∀ i, i ≠ 11 → i ≠ 12 → i ≠ 13 → i ≠ 15 → S'.regs i = S.regs i) →
      ReachesRet (LibW.program.link impl) ret S' Q)
    (KL : ∀ S' : State, 2 ^ j < 64 → S'.rip = BitVec.ofNat 64 kHead → S'.mem = S.mem →
      S'.regs 15 = BitVec.ofNat 64 (2 ^ (j + 1)) → S'.regs 12 = BitVec.ofNat 64 (t * t % 2 ^ 64) →
      S'.regs 13 = BitVec.ofNat 64 (k * ((t * t % 2 ^ 64 + 1) % 2 ^ 64) % 2 ^ 64) →
      S'.xmm = S.xmm → S'.fsBase = S.fsBase → S'.df = false →
      (∀ i, i ≠ 11 → i ≠ 12 → i ≠ 13 → i ≠ 15 → S'.regs i = S.regs i) →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hp : 2 ^ j ≤ 64 := by
    calc 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by omega) hj
      _ = 64 := by rfl
  have e : (BitVec.ofNat 64 (2 ^ j)).toNat = 2 ^ j := Nat.mod_eq_of_lt (by omega)
  by_cases hlt : 2 ^ j < 64
  · have hbr : (BitVec.ofNat 64 (2 ^ j)).toInt < (64 : Int) := by
      rw [BitVec.toInt_eq_toNat_cond, e]; split <;> omega
    janus64_step [hbr]
    refine SegProg.lift W2Seg.codeIn (r := BitVec.ofNat 64 kHead) ?_
    janus64_run [hbr] until [kHead]
    refine KL _ hlt rfl rfl ?_ ?_ ?_ rfl rfl rfl ?_
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.pow_succ]; omega
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp [h11]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp [h11, h12, Nat.mul_comm]
    · intro i a1 a2 a3 a4; simp [setRegF_apply, a1, a2, a3, a4]
  · have hbr : ¬ (BitVec.ofNat 64 (2 ^ j)).toInt < (64 : Int) := by
      rw [BitVec.toInt_eq_toNat_cond, e]; split <;> omega
    refine SegProg.lift W2Seg.codeIn (r := BitVec.ofNat 64 kExit) ?_
    janus64_run [hbr] until [kExit]
    refine KE _ hlt rfl rfl ?_ rfl rfl rfl ?_
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h12
    · intro i a1 a2 a3 a4; simp [setRegF_apply, a1, a2, a3, a4]

/-- the whole Newton loop from its head (`j` doublings done) -/
theorem kLoop {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop} :
    ∀ (d j t k sp : Nat) (S : State), j + d = 6 → t < 2 ^ 64 → k < 2 ^ 64 →
      S.rip = BitVec.ofNat 64 kHead → S.regs 4 = BitVec.ofNat 64 sp → 4296 ≤ sp → sp + 0x2a8 ≤ 2 ^ 48 →
      S.mem.accessible (sp - 4296) (4296 + 0x2a8) true = true → S.regs 15 = BitVec.ofNat 64 (2 ^ j) →
      S.regs 12 = BitVec.ofNat 64 t → S.regs 13 = BitVec.ofNat 64 k → S.df = false →
      (∀ S' : State, S'.rip = BitVec.ofNat 64 kExit → S'.mem = S.mem →
        S'.regs 13 = BitVec.ofNat 64 (Exp.newtonLoop 64 j t k) → S'.xmm = S.xmm → S'.fsBase = S.fsBase →
        S'.df = false → (∀ i, i ≠ 11 → i ≠ 12 → i ≠ 13 → i ≠ 15 → S'.regs i = S.regs i) →
        ReachesRet (LibW.program.link impl) ret S' Q) →
      ReachesRet (LibW.program.link impl) ret S Q := by
  intro d
  induction d with
  | zero =>
    intro j t k sp S hd ht hk hpc hsp hs1 hs2 hacc h13 h11 h12 hdf KE
    refine kIter S j t k (by omega) ht hk hpc sp hsp hs1 hs2 hacc h13 h11 h12 hdf ?_ ?_
    · intro S' hn a1 a2 a3 a4 a5 a6 a7
      refine KE S' a1 a2 ?_ a4 a5 a6 a7
      have e : Exp.newtonLoop 64 j t k = k := by rw [Exp.newtonLoop, dif_neg hn]
      rw [a3, e]
    · intro S' hn; subst hd; exact absurd hn (by decide)
  | succ d ih =>
    intro j t k sp S hd ht hk hpc hsp hs1 hs2 hacc h13 h11 h12 hdf KE
    refine kIter S j t k (by omega) ht hk hpc sp hsp hs1 hs2 hacc h13 h11 h12 hdf ?_ ?_
    · intro S' hn
      have : 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right (by omega) (by omega)
      exact absurd this hn
    · intro S' hn a1 a2 a3 a4 a5 a6 a7 a8 a9
      refine ih (j + 1) _ _ sp S' (by omega) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) a1
        ((a9 4 (by decide) (by decide) (by decide) (by decide)).trans hsp) hs1 hs2 (by rw [a2]; exact hacc) a3 a4 a5 a8 ?_
      intro S'' b1 b2 b3 b4 b5 b6 b7
      refine KE S'' b1 (b2.trans a2) ?_ (b4.trans a6) (b5.trans a7) b6
        (fun i c1 c2 c3 c4 => (b7 i c1 c2 c3 c4).trans (a9 i c1 c2 c3 c4))
      have e : Exp.newtonLoop 64 j t k = Exp.newtonLoop 64 (j + 1) (t * t % Exp.B)
          (k * ((t * t % Exp.B + 1) % Exp.B) % Exp.B) := by rw [Exp.newtonLoop, dif_pos hn]
      rw [b3, e]
      simp only [Exp.B_def]

end FvModexp.Amd64.W2Pro
