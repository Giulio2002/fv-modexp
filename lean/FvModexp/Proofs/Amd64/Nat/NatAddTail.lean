import FvModexp.Proofs.Amd64.Nat.NatAddMid

/-!
# `nat.add` (amd64): `z[m] = c; return z.norm()` (`+0x1c1` … return)

At `+0x1c1` (join of the `m = n` and the `addVW` paths) `SI = m`, the carry in `R9`:
`MOVQ 0x68(SP), DX; CMPQ SI, DX; JAE panic; MOVQ 0x78(SP), AX; MOVQ R9, 0(AX)(SI*8); JMP norm`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.NatAdd

abbrev hTail : Nat := segAddr Extracted.program fn + 0x1c1

/-- The return site of `addVV.abi0`. -/
abbrev hAfterVV : Nat := segAddr Extracted.program fn + 0x12a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tail (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hps : M.readLE ((s.regs 4).toNat - 24) 8 = p) (hcs : M.readLE ((s.regs 4).toNat - 64) 8 = c) (cw : Nat)
    (hcw : cw < 2 ^ 64)
    (hv : natVal M p xl.toNat + 2 ^ (64 * xl.toNat) * cw =
      natVal s.mem xp.toNat xl.toNat + natVal s.mem yp.toNat yl.toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hTail) (h9 : S.regs 9 = BitVec.ofNat 64 cw)
    (h6 : S.regs 6 = BitVec.ofNat 64 xl.toNat)
    (hsp : S.regs 4 = s.regs 4 - 144#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hm : S.mem = M) :
    ReachesRet (LibNatAdd.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40
  have r1 := h.sm1; have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc
  have hp8 := h.p8
  have hpw := h.pw
  unfold Apart at hpw
  have hpw8 : M.accessible p (8 * (xl.toNat + 1)) false = true :=
    Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega))
  janus64_run [hm, r1, hps, BitVec.msb_eq_decide] until [hNorm]
  have hst := h.store cw (a := p + 8 * xl.toNat) (by omega) (by omega)
  have hval : natVal (M.writeLE (p + 8 * xl.toNat) 8 cw) p (xl.toNat + 1) =
      natVal s.mem xp.toNat xl.toNat + natVal s.mem yp.toNat yl.toNat := by
    rw [natVal_succ, Janus.Arm64.Memory.readLE_writeLE_self, ← hv, Nat.mod_eq_of_lt (by simpa using hcw)]
    congr 1
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine norm impl s _ p c (xl.toNat + 1) _ _ (fun s' n' hm' h0' h1' h2' hfs' hn' hv' hnm' =>
      hst.post hyx hy0 s' n' hm' h0' h1' h2' hfs' hn' hv' hnm') hcap (by omega) (by omega)
    (by simpa only [Janus.Arm64.Memory.accessible_writeLE] using hpw8)
    hst.lr hst.fp (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hcs)
    hal hsp0 hsp1 hst.sacc h.ra47 (xl.toNat + 1) _ (Nat.le_refl _) rfl ?_ ?_ ?_ h14 ?_ ?_ ?_
    (by show M.writeLE _ 8 cw = _; rw [Nat.mul_comm xl.toNat 8]) hval
  all_goals (try janus64_simp) <;> exact hfs

end FvModexp.Amd64.NatAdd
