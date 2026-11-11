import FvModexp.Proofs.Arm64.Nat.NatAddMid

/-!
# `nat.add` (arm64): `z[m] = c; return z.norm()` (`+0x11c` … return)

At `+0x11c` (the join of the `m = n` and the `addVW` paths) `R0 = m`, the carry is in `R6`, `z[:m]` holds `(X + Y) mod B^m` with carry `c` (`X + Y = z[:m] + B^m·c`).
`MOVD 128(RSP), R3; CMP R3, R0; BCS panic; MOVD 136(RSP), R4; MOVD R6, (R4)(R0<<3); JMP norm`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatAdd

abbrev hTail : Nat := segAddr Extracted.program fn + 0x11c

/-- The return site of `addVV.abi0`. -/
abbrev hAfterVV : Nat := segAddr Extracted.program fn + 0xbc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tail (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc xp xl xc yp yl s p c L' b' M) (hyx : yl.toNat ≤ xl.toNat) (hy0 : 0 < yl.toNat)
    (hps : M.readLE (s.sp.toNat - 24) 8 = p) (hcs : M.readLE (s.sp.toNat - 64) 8 = c) (cw : Nat) (hcw : cw < 2 ^ 64)
    (hv : natVal M p xl.toNat + 2 ^ (64 * xl.toNat) * cw =
      natVal s.mem xp.toNat xl.toNat + natVal s.mem yp.toNat yl.toNat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hTail) (h6 : S.regs 6 = BitVec.ofNat 64 cw)
    (h0 : S.regs 0 = BitVec.ofNat 64 xl.toNat)
    (hsp : S.sp = s.sp - 160#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 168#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibNatAdd.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostR 4304 R b L zp zc xp xl yp yl s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40
  have r1 := h.sxl; have r2 := h.sm1; have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc
  have hp8 := h.p8
  janus_run [hm, r1, r2, hps] until [hNorm]
  -- the store `z[m] = c`, then the norm loop from `i = m + 1`
  have hst := h.store cw (a := p + 8 * xl.toNat) (by omega) (by omega)
  have hval : natVal (M.writeLE (p + 8 * xl.toNat) 8 cw) p (xl.toNat + 1) =
      natVal s.mem xp.toNat xl.toNat + natVal s.mem yp.toNat yl.toNat := by
    rw [natVal_succ, Memory.readLE_writeLE_self, ← hv, Nat.mod_eq_of_lt (by simpa using hcw)]
    congr 1
    exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine norm impl s _ p c (xl.toNat + 1) _ _ (fun s' n' hm' h0' h1' h2' hn' hv' hnm' =>
      hst.post hyx hy0 s' n' hm' h0' h1' h2' hn' hv' hnm') hcap (by omega) (by omega)
    (by simpa only [Memory.accessible_writeLE] using Memory.accessible_weaken _ (Memory.accessible_mono _ hpacc
      (Nat.le_refl _) (by omega)))
    hst.lr hst.fp (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by have := h.pw; unfold Apart at this; omega)]; exact hcs)
    hal hsp0 hsp1 hst.sacc h.lr4 h.lr48 (xl.toNat + 1) _ (Nat.le_refl _) rfl ?_ ?_ ?_ h28 ?_ h18 rfl hval
  all_goals janus_simp
end FvModexp.Arm64.NatAdd
