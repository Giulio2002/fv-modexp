import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2Div

/-!
# window-2 prologue (arm64): the argument loads of the `RR` division, `fn+0x3f0 → divE` (nat.go:1399)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

/-- return of `stk.nat(2n)` #2 (`MOVD 672(RSP), R3`) -/
abbrev sn2Ret : Nat := 1802912

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toDiv (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (sp st rrp zzp zzl zzc mp n mc : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 4288 ≤ sp) (hsp2 : sp + 752 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4288) (4288 + 752) true = true)
    (r672 : M.readLE (sp + 672) 8 = st) (r408 : M.readLE (sp + 408) 8 = rrp) (r176 : M.readLE (sp + 176) 8 = 2 * n)
    (r400 : M.readLE (sp + 400) 8 = zzp) (r160 : M.readLE (sp + 160) 8 = zzl) (r168 : M.readLE (sp + 168) 8 = zzc)
    (r728 : M.readLE (sp + 728) 8 = mp) (r736 : M.readLE (sp + 736) 8 = n) (r744 : M.readLE (sp + 744) 8 = mc)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 sn2Ret) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KD : ∀ (S' : State), S'.pc = BitVec.ofNat 64 divE → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = BitVec.ofNat 64 rrp → S'.regs 5 = BitVec.ofNat 64 1 →
      S'.regs 6 = BitVec.ofNat 64 (2 * n) → S'.regs 7 = BitVec.ofNat 64 zzp → S'.regs 8 = BitVec.ofNat 64 zzl →
      S'.regs 9 = BitVec.ofNat 64 zzc → S'.regs 10 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 n →
      S'.regs 12 = BitVec.ofNat 64 mc → S'.regs 30 = BitVec.ofNat 64 divRet →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  generalize e0 : S.regs 0 = x0 at KD
  generalize e1 : S.regs 1 = x1 at KD
  generalize e2 : S.regs 2 = x2 at KD
  generalize e18 : S.regs 18 = x18 at KD
  generalize e28 : S.regs 28 = x28 at KD
  generalize e29 : S.regs 29 = x29 at KD
  janus_run [r672, r408, r176, r400, r160, r168, r728, r736, r744] until [divE]
  refine KD _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip

end FvModexp.Arm64.W2Pro
