import FvModexp.Proofs.Arm64.Exp.W2Exit
import FvModexp.Proofs.Arm64.Exp.W2Fin

/-!
# window-2 (arm64), after the first `zz.cmp(m)` (nat.go:1476): the two branches

* `exLt`: `cmp < 0` (`X0 = -1`): `zz` reloaded into `X3..X5` → the join `njoin`.
* `exGe`: `cmp ≥ 0`: the arguments of `zz.sub(zz, m)` loaded → the entry of `nat.sub`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Loop

/-- `nat.sub`'s entry -/
abbrev subEntry : Nat := 1781872
/-- the return address of `zz.sub(zz, m)` -/
abbrev subRet : Nat := 1804644
/-- the return address of the second `zz.cmp(m)` -/
abbrev cmp2Ret : Nat := 1804672
/-- `njoin` as a literal -/
abbrev njoinL : Nat := 1804756

theorem njoin_eq : njoin = njoinL := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `cmp < 0`: reload `zz` and jump to the join -/
theorem exLt (impl : List Segment) (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop) (S : State) (sp g zzp n zzc : Nat)
    (r18 r29 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 cmp1Ret) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = 18446744073709551615#64) (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (r400 : M.readLE (sp + 400) 8 = zzp) (r160 : M.readLE (sp + 160) 8 = n) (r168 : M.readLE (sp + 168) 8 = zzc)
    (hal : sp % 16 = 0) (hsp1 : sp + 752 ≤ 2 ^ 48) (hacc : M.accessible sp 752 true = true)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 njoinL → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 zzp → S'.regs 4 = BitVec.ofNat 64 n → S'.regs 5 = BitVec.ofNat 64 zzc →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have fnB := fnBase
  janus_run [r400, r160, r168, fnB] until [njoinL]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals first | rfl | (janus_simp; done) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `cmp ≥ 0`: load the arguments of `zz.sub(zz, m)` and call it -/
theorem exGe (impl : List Segment) (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop) (S : State) (sp g zzp n zzc mp mc v : Nat)
    (r18 r29 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 cmp1Ret) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 v) (hv : v ≤ 1) (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (r400 : M.readLE (sp + 400) 8 = zzp) (r160 : M.readLE (sp + 160) 8 = n) (r168 : M.readLE (sp + 168) 8 = zzc)
    (r728 : M.readLE (sp + 728) 8 = mp) (r736 : M.readLE (sp + 736) 8 = n) (r744 : M.readLE (sp + 744) 8 = mc)
    (hal : sp % 16 = 0) (hsp1 : sp + 752 ≤ 2 ^ 48) (hacc : M.accessible sp 752 true = true)
    (K : ∀ S' : State, S'.pc = BitVec.ofNat 64 subEntry → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 30 = BitVec.ofNat 64 subRet →
      S'.regs 0 = BitVec.ofNat 64 zzp → S'.regs 1 = BitVec.ofNat 64 n → S'.regs 2 = BitVec.ofNat 64 zzc →
      S'.regs 3 = BitVec.ofNat 64 zzp → S'.regs 4 = BitVec.ofNat 64 n → S'.regs 5 = BitVec.ofNat 64 zzc →
      S'.regs 6 = BitVec.ofNat 64 mp → S'.regs 7 = BitVec.ofNat 64 n → S'.regs 8 = BitVec.ofNat 64 mc →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have fnB := fnBase
  have h63 : (BitVec.ofNat 64 v).getLsbD 63 = false := by
    simp only [BitVec.getLsbD_ofNat]; simp [Nat.testBit, Nat.shiftRight_eq_div_pow]; omega
  janus_run [r400, r160, r168, r728, r736, r744, fnB, h63] until [subEntry]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  all_goals first | rfl | (janus_simp; done) | skip

end FvModexp.Arm64.W2Loop
