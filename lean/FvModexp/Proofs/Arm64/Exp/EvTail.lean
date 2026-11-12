import FvModexp.Proofs.Arm64.Exp.EvDefs
import FvModexp.Proofs.Arm64.Exp.Defer
import FvModexp.Proofs.Common.Link

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): `addR` → deferred `stk.restore(len₀)` → `RET` (agent infra; pattern of `P2W2Tail`)

At `addR` (`0x1b52c8`): `MOVD R0, 232(RSP)`; `STP (R1, R2), 240(RSP)`; `MOVB ZR, 127(RSP)` (defer bit);
`R26 = [320] = sp + 296` (the closure record: `[296] = deferwrap1`, `[304] = st`, `[312] = len₀`), `CALL (R10)`
(ret `dwR`); reload `R2 = [248]`, `(R0, R1) = [232]`; `LDP -8(RSP), (R29, R30)`; `ADD $336, RSP`; `RET`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the closure (`Defer.sum`, proved on `LibDefer`) as a callee in `LibNE` -/
theorem dfrSum (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibNE.program.link impl) dwE Defer.Pre Defer.Post := by
  have hsub : ∀ x, LibDefer.names.contains x = true → LibNE.names.contains x = true := by
    have h : LibDefer.names.Sublist LibNE.names := by decide +kernel
    intro x hx
    simp only [List.contains_iff_mem] at hx ⊢
    exact h.subset hx
  have hc := codeIn_restrict_mono hap hsub
  rw [← LibDefer.eq_only, ← LibNE.eq_only] at hc
  have h := Janus.Contracts.EqHashModel.Summary.of_codeIn hc (Defer.sum impl fnDw (by simp [fnDw]))
  have e : segAddr LibDefer.program fnDw = dwE := by decide
  rw [e] at h
  exact h

/-- the static facts of the tail at memory `M` (frame `sp`, closure record at `sp + 296`, entry stack length `n0`) -/
@[reducible] def TEnv (sp g st n0 : Nat) (r29 : BitVec 64) (ret : Nat) (M : Memory) : Prop :=
  sp % 16 = 0 ∧ 4304 ≤ sp ∧ sp + 448 ≤ 2 ^ 48 ∧ M.accessible (sp - 4304) (4304 + 448) true = true ∧
    g + 24 ≤ 2 ^ 48 ∧ M.accessible (g + 16) 8 false = true ∧ M.readLE (g + 16) 8 + 4304 < sp ∧
    Apart (g + 16) 8 (sp - 4304) (4304 + 448) ∧
    M.readLE (sp + 320) 8 = sp + 296 ∧ M.readLE (sp + 296) 8 = dwE ∧
    M.readLE (sp + 304) 8 = st ∧ M.readLE (sp + 312) 8 = n0 ∧
    st + 24 ≤ 2 ^ 48 ∧ M.accessible st 24 true = true ∧ n0 ≤ M.readLE (st + 16) 8 ∧
    Apart st 24 (sp - 4304) (4304 + 448) ∧ Apart st 24 (g + 16) 8 ∧
    M.readLE (sp - 8) 8 = r29.toNat ∧ M.readLE sp 8 = ret ∧ ret % 4 = 0 ∧ ret < 2 ^ 48

/-- the tail's writes -/
@[reducible] def TW (sp st : Nat) : List (Nat × Nat) :=
  [(sp - 24, sp - 8), (sp + 127, sp + 128), (sp + 232, sp + 256), (st + 8, st + 16)]

/-- what the tail guarantees (memory relative to `M`) -/
@[reducible] def TPost (sp g st n0 p l c : Nat) (r18 r29 : BitVec 64) (M : Memory) (s' : State) : Prop :=
  s'.sp = BitVec.ofNat 64 (sp + 336) ∧ s'.regs 18 = r18 ∧ s'.regs 28 = BitVec.ofNat 64 g ∧ s'.regs 29 = r29 ∧
    s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    s'.mem.readLE (st + 8) 8 = n0 ∧ MemFrame M s'.mem (TW sp st)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem tailE {impl : List Segment} (hap : ImplApart Extracted.program impl) (Q : State → Prop)
    (S : State) (sp g st n0 p l c ret : Nat) (r18 r29 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 addR) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h1 : S.regs 1 = BitVec.ofNat 64 l) (h2 : S.regs 2 = BitVec.ofNat 64 c)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (hp : p < 2 ^ 64) (hl : l < 2 ^ 64) (hc : c < 2 ^ 64) (he : TEnv sp g st n0 r29 ret M)
    (KF : ∀ s', TPost sp g st n0 p l c r18 r29 M s' → Q s') :
    ReachesRet (LibNE.program.link impl) (BitVec.ofNat 64 ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hacc, hg1, hg2, hg3, hgw, r320, r296, r304, r312, hst1, hst2, hn0, hstw, hstg, rfp, rlr,
    hr4, hr48⟩ := he
  have hD := dfrSum impl hap
  rw [show dwE = 1790848 from rfl] at hD r296
  janus_run [r320, r296, r304, r312, rfp, rlr] calls [hD]
  rename_i _ e1 e2 e3 e4 e5 e6 _
  refine KF _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, e5, ?_⟩
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e2]; janus_simp
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e3]; janus_simp
  all_goals first | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | skip
  unfold TW
  janus_frame

end FvModexp.Arm64.ExpEven
