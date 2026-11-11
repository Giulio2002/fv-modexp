import FvModexp.Proofs.Arm64.Nat.MulAddWWNorm

/-!
# `nat.mulAddWW` (arm64): `z[m] = mulAddVWW(z[0:m], x, y, r); return z.norm()` (`+0x7c` … return)

At `+0x7c` (the join of the reuse and `makeslice` paths of `z.make(m + 1)`): `R0 = p`, `R1 = m + 1`, `R2 = c`,
`R3 = xp`, `R4 = m`, `R5 = xc`, `R6 = y`, `R7 = r`. `CMP R2, R4; BHI panic; MOVD R2, 80(RSP); MOVD R0, 96(RSP)`, the
ABI0 argument frame `8(RSP) … 72(RSP)` (`SP - 104 … SP - 40`), `CALL mulAddVWW.abi0` (result `72(RSP) = SP - 40`).
After the call (`+0xa0`): `R0 = m`, `R1 = m + 1`, `CMP R1, R0; BCS panic`, `z[m] = carry`, `JMP norm` (`R1 = m + 1`,
`R4 = p`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.MulAddWW

/-- The return site of `mulAddVWW.abi0`. -/
abbrev hAfter : Nat := segAddr Extracted.program fn + 0xa0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tail (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0)
    (hps : M.readLE (s.sp.toNat - 16) 8 = p) (hcs : M.readLE (s.sp.toNat - 32) 8 = c)
    (hv : natVal M p xl.toNat + 2 ^ (64 * xl.toNat) * M.readLE (s.sp.toNat - 40) 8 =
      natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hAfter)
    (hsp : S.sp = s.sp - 112#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hpw := h.pw
  unfold Apart at hpw
  have r1 := h.sm; have r2 := h.sm1; have hsacc := h.sacc; have hal := h.al; have hpacc := h.pacc
  have hp8 := h.p8
  have hcw := Janus.Spec.MemHash.readLE_lt64 M (s.sp.toNat - 40) 8 (by decide)
  obtain ⟨cw, hcwv⟩ : ∃ cw, M.readLE (s.sp.toNat - 40) 8 = cw := ⟨_, rfl⟩
  rw [hcwv] at hv hcw
  janus_run [hm, r1, r2, hps, hcwv] until [hNorm]
  -- the store `z[m] = c`, then the norm loop from `i = m + 1`
  have hst := h.frame0 (ws := [(p + 8 * xl.toNat, p + 8 * xl.toNat + 8)])
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; simp only; omega)
    (M2 := M.writeLE (p + 8 * xl.toNat) 8 cw) (by janus_frame)
  have hval : natVal (M.writeLE (p + 8 * xl.toNat) 8 cw) p (xl.toNat + 1) =
      natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat := by
    rw [natVal_succ, Memory.readLE_writeLE_self, ← hv, Nat.mod_eq_of_lt (by simpa using hcw)]
    congr 1
    exact Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine norm impl s _ p c (xl.toNat + 1) _ _ (fun s' n' hm' h0' h1' h2' hn' hv' hnm' =>
      hst.post hx0 hy0 s' n' hm' h0' h1' h2' hn' hv' hnm') hcap (by omega) (by omega)
    (by simpa only [Memory.accessible_writeLE] using Memory.accessible_weaken _ (Memory.accessible_mono _ hpacc
      (Nat.le_refl _) (by omega)))
    hst.lr hst.fp (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hcs)
    hal hsp0 hsp1 hst.sacc h.lr4 h.lr48 (xl.toNat + 1) _ (Nat.le_refl _) rfl ?_ ?_ ?_ h28 ?_ h18 rfl hval
  all_goals janus_simp

end FvModexp.Arm64.MulAddWW
