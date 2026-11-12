import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2Lsh

/-!
# window-2 prologue (arm64): `RR = RR.setWord(1)` (inline, cap `2n > 0`) and the call setup of `nat.lsh`,
`sn1Ret → lshE` (nat.go:1397-1398)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

/-- return of `stk.nat(2n)` #1 (`CBNZ R2`) -/
abbrev sn1Ret : Nat := 1802820

theorem lsl7r (x : BitVec 64) :
    x.rotateRight 57 &&& 18446744073709551488#64 &&& 18446744073709551615#64 = x <<< 7 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551488#64)[i] = decide (7 ≤ i) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_shiftLeft, c1 i hi, c2 i hi]
  by_cases h : i < 7
  · simp [h]
  · simp [h]; omega

theorem lsl7 {n : Nat} (hn : n ≤ 128) :
    (BitVec.ofNat 64 n).rotateRight 57 &&& 18446744073709551488#64 &&& 18446744073709551615#64 =
      BitVec.ofNat 64 (128 * n) := by
  rw [lsl7r]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toLsh (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (sp rrp n : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 4288 ≤ sp) (hsp2 : sp + 752 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4288) (4288 + 752) true = true)
    (hn : 0 < n) (hn128 : n ≤ 128) (r736 : M.readLE (sp + 736) 8 = n)
    (hracc : M.accessible rrp 8 true = true) (hr48 : rrp + 8 ≤ 2 ^ 48)
    (hrw : rrp + 8 ≤ sp - 4288 ∨ sp + 752 ≤ rrp)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 sn1Ret) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 rrp) (h2 : S.regs 2 = BitVec.ofNat 64 (2 * n)) (hmem : S.mem = M)
    (KL : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 lshE → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 0 → S'.regs 1 = BitVec.ofNat 64 0 → S'.regs 2 = BitVec.ofNat 64 0 →
      S'.regs 3 = BitVec.ofNat 64 rrp → S'.regs 4 = BitVec.ofNat 64 1 → S'.regs 5 = BitVec.ofNat 64 (2 * n) →
      S'.regs 6 = BitVec.ofNat 64 (128 * n) → S'.regs 30 = BitVec.ofNat 64 lshRet →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 176, sp + 184), (sp + 408, sp + 416), (rrp, rrp + 8)] → M'.regions = M.regions →
      M'.readLE (sp + 176) 8 = 2 * n → M'.readLE (sp + 408) 8 = rrp → M'.readLE rrp 8 = 1 →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  generalize e18 : S.regs 18 = x18 at KL
  generalize e28 : S.regs 28 = x28 at KL
  generalize e29 : S.regs 29 = x29 at KL
  have hne : BitVec.ofNat 64 (2 * n) ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus_run [r736, hne, lsl7 hn128] until [lshE]
  refine KL _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?q1 ?q2 ?q3
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 176, sp + 184)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 408, sp + 416)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (rrp, rrp + 8)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow]
  all_goals omega

end FvModexp.Arm64.W2Pro
