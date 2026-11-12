import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4DivR

/-!
# window-4 prologue (arm64): the spills of `zz` and the call setup of `stk.nat(2n)` #2, `lshRet → snE` (nat.go:1398-1399)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

/-- return of `nat.lsh` (`MOVD R0, 400(RSP)`) -/
abbrev lshRet : Nat := 1799496

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toSn2 (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (sp st zzp zzl zzc k2 : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 4288 ≤ sp) (hsp2 : sp + 1040 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4288) (4288 + 1040) true = true)
    (r960 : M.readLE (sp + 960) 8 = st) (r128 : M.readLE (sp + 128) 8 = k2)
    (hzzp : zzp < 2 ^ 64) (hzzl : zzl < 2 ^ 64) (hzzc : zzc < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 lshRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zzp) (h1 : S.regs 1 = BitVec.ofNat 64 zzl) (h2 : S.regs 2 = BitVec.ofNat 64 zzc)
    (hmem : S.mem = M)
    (KS : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 snE → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 1 = BitVec.ofNat 64 k2 → S'.regs 30 = BitVec.ofNat 64 sn2Ret →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 160, sp + 176), (sp + 400, sp + 408)] → M'.regions = M.regions →
      M'.readLE (sp + 400) 8 = zzp → M'.readLE (sp + 168) 8 = zzc → M'.readLE (sp + 160) 8 = zzl →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  generalize e18 : S.regs 18 = x18 at KS
  generalize e28 : S.regs 28 = x28 at KS
  generalize e29 : S.regs 29 = x29 at KS
  janus_run [r960, r128] until [snE]
  refine KS _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?q1 ?q2 ?q3
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 160, sp + 176)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 400, sp + 408)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow]
  all_goals omega

end FvModexp.Arm64.W4Pro
