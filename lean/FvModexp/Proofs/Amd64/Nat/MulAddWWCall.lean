import FvModexp.Proofs.Amd64.Nat.MulAddWWNorm

/-!
# `nat.mulAddWW` (amd64): after `mulAddVWW.abi0` returns (`+0xed`) … return

`XORPS X15, X15; MOVQ FS:-8, R14`, `AX = m`, `CX = m + 1`, `CMPQ AX, CX; JAE panic`, `z[m] = carry`
(`0x40(RSP') = RSP - 40`), `JMP norm` (`CX = m + 1`, `SI = p`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.MulAddWW

/-- The return site of `mulAddVWW.abi0`. -/
abbrev hAfter : Nat := segAddr Extracted.program fn + 0xed

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tail (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Janus.Arm64.Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0)
    (hps : M.readLE ((s.regs 4).toNat - 16) 8 = p) (hcs : M.readLE ((s.regs 4).toNat - 32) 8 = c)
    (hv : natVal M p xl.toNat + 2 ^ (64 * xl.toNat) * M.readLE ((s.regs 4).toNat - 40) 8 =
      natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hAfter)
    (hsp : S.regs 4 = s.regs 4 - 104#64) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ Post R b L zp zc xp xl y r s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hpw := h.pw
  unfold Apart at hpw
  have r1 := h.sm; have r2 := h.sm1; have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc
  have hp8 := h.p8; have htls := h.tls; have htacc := h.tacc
  have htb := h.tlsg.base
  have hcw := Janus.Spec.MemHash.readLE_lt64 M ((s.regs 4).toNat - 40) 8 (by decide)
  obtain ⟨cw, hcwv⟩ : ∃ cw, M.readLE ((s.regs 4).toNat - 40) 8 = cw := ⟨_, rfl⟩
  rw [hcwv] at hv hcw
  have hpw8 : M.accessible p (8 * (xl.toNat + 1)) false = true :=
    Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega))
  janus64_run [hm, r1, r2, hps, hcwv, htls, hfs, BitVec.msb_eq_decide,
    (show (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 by omega)] until [hNorm]
  have hst := h.frame0 (ws := [(p + 8 * xl.toNat, p + 8 * xl.toNat + 8)])
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; simp only; omega)
    (M2 := M.writeLE (p + 8 * xl.toNat) 8 cw) (by janus_frame)
  have hval : natVal (M.writeLE (p + 8 * xl.toNat) 8 cw) p (xl.toNat + 1) =
      natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat := by
    rw [natVal_succ, Janus.Arm64.Memory.readLE_writeLE_self, ← hv, Nat.mod_eq_of_lt (by simpa using hcw)]
    congr 1
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine norm impl s _ p c (xl.toNat + 1) _ _ (fun s' n' hm' h0' h1' h2' hfs' hn' hv' hnm' =>
      hst.post hx0 hy0 s' n' hm' h0' h1' h2' hfs' hn' hv' hnm') hcap (by omega) (by omega)
    (by simpa only [Janus.Arm64.Memory.accessible_writeLE] using hpw8)
    hst.lr hst.fp (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hcs)
    hal hsp0 hsp1 hst.sacc h.ra47 (xl.toNat + 1) _ (Nat.le_refl _) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by show M.writeLE _ 8 cw = _; rw [Nat.mul_comm xl.toNat 8]) hval
  all_goals try janus64_simp
  all_goals first | exact hfs | exact h.x15.symm

end FvModexp.Amd64.MulAddWW
