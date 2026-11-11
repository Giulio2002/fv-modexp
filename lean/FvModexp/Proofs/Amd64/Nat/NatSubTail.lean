import FvModexp.Proofs.Amd64.Nat.NatSubMid

/-!
# `nat.sub` (amd64): `if c != 0 { panic }; return z.norm()` (`+0x220` … return)

`TESTQ R9, R9; JNE panic; MOVQ 0x78(SP), AX; MOVQ 0x50(SP), SI; JMP norm`; the borrow `R9` is `0` here.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatSub

abbrev hTail : Nat := segAddr Extracted.program fn + 0x220

/-- The return site of `subVV.abi0`. -/
abbrev hAfterVV : Nat := segAddr Extracted.program fn + 0x189

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tail (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M)
    (hps : M.readLE ((s.regs 4).toNat - 24) 8 = p) (hms : M.readLE ((s.regs 4).toNat - 64) 8 = xl.toNat)
    (hcs : M.readLE ((s.regs 4).toNat - 56) 8 = c)
    (hv : natVal M p xl.toNat = natVal s.mem xp.toNat xl.toNat - natVal s.mem yp.toNat yl.toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hTail) (h9 : S.regs 9 = 0#64)
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hm : S.mem = M) :
    ReachesRet (LibNatSub.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc; have hp8 := h.p8
  janus64_run [hm, hps, hms] until [hNorm]
  refine norm impl s M p c xl.toNat _ _ (fun s' n' hm' h0' h1' h2' hfs' hn' hv' hnm' =>
      h.post s' n' hm' h0' h1' h2' hfs' hn' hv' hnm') hcap (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega)))
    h.lr h.fp hcs hal hsp0 hsp1 hsacc h.ra47 xl.toNat _ (Nat.le_refl _) rfl ?_ ?_ ?_ h14 ?_ ?_ ?_ rfl hv
  all_goals (try janus64_simp) <;> exact hfs

end FvModexp.Amd64.NatSub
