import FvModexp.Proofs.Arm64.Nat.NatSubMid

/-!
# `nat.sub` (arm64): `if c != 0 { panic }; return z.norm()` (`+0x16c` … return)

At `+0x16c` (join of the `m = n` and the `subVW` paths) the borrow is in `R6` (`CBNZ R6, panic`); it is `0` here.
`MOVD 136(RSP), R0; MOVD 96(RSP), R4; JMP norm`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSub

abbrev hTail : Nat := segAddr Extracted.program fn + 0x16c

/-- The return site of `subVV.abi0`. -/
abbrev hAfterVV : Nat := segAddr Extracted.program fn + 0x104

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tail (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M)
    (hps : M.readLE (s.sp.toNat - 24) 8 = p) (hms : M.readLE (s.sp.toNat - 64) 8 = xl.toNat)
    (hcs : M.readLE (s.sp.toNat - 56) 8 = c)
    (hv : natVal M p xl.toNat = natVal s.mem xp.toNat xl.toNat - natVal s.mem yp.toNat yl.toNat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hTail) (h6 : S.regs 6 = 0#64)
    (hsp : S.sp = s.sp - 160#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 168#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibNatSub.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostR 4304 R b L zp zc xp xl yp yl s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc; have hp8 := h.p8
  janus_run [hm, hps, hms] until [hNorm]
  refine norm impl s M p c xl.toNat _ _ (fun s' n' hm' h0' h1' h2' hn' hv' hnm' =>
      h.post s' n' hm' h0' h1' h2' hn' hv' hnm') hcap (by omega) (by omega)
    (Memory.accessible_weaken _ (Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega)))
    h.lr h.fp hcs hal hsp0 hsp1 hsacc h.lr4 h.lr48 xl.toNat _ (Nat.le_refl _) rfl ?_ ?_ ?_ h28 ?_ h18 rfl hv
  all_goals janus_simp

end FvModexp.Arm64.NatSub
