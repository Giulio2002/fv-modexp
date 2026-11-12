import FvModexp.Proofs.Arm64.Exp.P2W2Defs
import FvModexp.Proofs.Arm64.Exp.Defer
import FvModexp.Proofs.Common.Link

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the two result exits → `RET` (agent infra)

Both exits store the result `(p, l, c)` into the named results `256/264/272`, clear the defer flag `95`, call the
open-coded closure `deferwrap1` (`stk.restore(len₀)`, `CALL (R0)` / `CALL (R1)` through the record `448 → 416`),
reload the results, pop the frame and `RET`:
* `tA` = `0x1b6aac = 1796780` (main exit, after `z.norm()`): `R0 = p`, `R1 = l`, `R15 = c`;
* `tB` = `0x1b6b04 = 1796868` (`return 1` via `setWord`): `R0 = p`, `R2 = l`, `R1 = c`.
The newobject `return 1` (`0x1b66c4..`) stores its own results; it shares `TEnv`/`TPost`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- the closure (`Defer.sum`, proved on `LibDefer`) as a callee in `LibW` (as agent expmc's `DeferW.sum`) -/
theorem dfrSum (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibW.program.link impl) dwE Defer.Pre Defer.Post := by
  have hsub : ∀ x, LibDefer.names.contains x = true → LibW.names.contains x = true := by
    have h : LibDefer.names.all LibW.names.contains = true := by decide
    intro x hx
    rw [List.all_eq_true] at h
    exact h x (by simpa using hx)
  have hc := codeIn_restrict_mono hap hsub
  rw [← LibDefer.eq_only, ← LibW.eq_only] at hc
  have h := Janus.Contracts.EqHashModel.Summary.of_codeIn hc (Defer.sum impl
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2.deferwrap1" (by simp))
  have e : segAddr LibDefer.program
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2.deferwrap1" = dwE := by decide
  rw [e] at h
  exact h

abbrev tA : Nat := 1796780
abbrev tB : Nat := 1796868
/-- after the `newobject` result store (`0x1b66c4`) -/
abbrev tN : Nat := 1795780

/-- the static facts of the tail at memory `M` (frame `sp`, closure record at `sp + 416`, entry stack length `n0`) -/
@[reducible] def TEnv (sp g st n0 : Nat) (r29 : BitVec 64) (ret : Nat) (M : Memory) : Prop :=
  sp % 16 = 0 ∧ 4304 ≤ sp ∧ sp + 560 ≤ 2 ^ 48 ∧ M.accessible (sp - 4304) (4304 + 560) true = true ∧
    g + 24 ≤ 2 ^ 48 ∧ M.accessible (g + 16) 8 false = true ∧ M.readLE (g + 16) 8 + 4304 < sp ∧
    Apart (g + 16) 8 (sp - 4304) (4304 + 560) ∧
    M.readLE (sp + 448) 8 = sp + 416 ∧ M.readLE (sp + 416) 8 = dwE ∧
    M.readLE (sp + 424) 8 = st ∧ M.readLE (sp + 432) 8 = n0 ∧
    st + 24 ≤ 2 ^ 48 ∧ M.accessible st 24 true = true ∧ n0 ≤ M.readLE (st + 16) 8 ∧
    Apart st 24 (sp - 4304) (4304 + 560) ∧ Apart st 24 (g + 16) 8 ∧
    M.readLE (sp - 8) 8 = r29.toNat ∧ M.readLE sp 8 = ret ∧ ret % 4 = 0 ∧ ret < 2 ^ 48

/-- what the tail guarantees (memory relative to `M`) -/
@[reducible] def TPost (sp g st n0 p l c : Nat) (r18 r29 : BitVec 64) (M : Memory) (s' : State) : Prop :=
  s'.sp = BitVec.ofNat 64 (sp + 464) ∧ s'.regs 18 = r18 ∧ s'.regs 28 = BitVec.ofNat 64 g ∧ s'.regs 29 = r29 ∧
    s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 1 = BitVec.ofNat 64 l ∧ s'.regs 2 = BitVec.ofNat 64 c ∧
    s'.mem.readLE (st + 8) 8 = n0 ∧
    MemFrame M s'.mem [(sp - 24, sp - 8), (sp + 95, sp + 96), (sp + 256, sp + 280), (st + 8, st + 16)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem tailA {impl : List Segment} (hap : ImplApart Extracted.program impl) (Q : State → Prop)
    (S : State) (sp g st n0 p l c ret : Nat) (r18 r29 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 tA) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h1 : S.regs 1 = BitVec.ofNat 64 l) (h15 : S.regs 15 = BitVec.ofNat 64 c)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (hp : p < 2 ^ 64) (hl : l < 2 ^ 64) (hc : c < 2 ^ 64) (he : TEnv sp g st n0 r29 ret M)
    (KF : ∀ s', TPost sp g st n0 p l c r18 r29 M s' → Q s') :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hacc, hg1, hg2, hg3, hgw, r448, r416, r424, r432, hst1, hst2, hn0, hstw, hstg, rfp, rlr,
    hr4, hr48⟩ := he
  have hD := dfrSum impl hap
  rw [show dwE = 1797024 from rfl] at hD r416
  janus_run [r448, r416, r424, r432, rfp, rlr] calls [hD]
  rename_i _ e1 e2 e3 e4 e5 e6 _
  refine KF _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, e5, ?_⟩
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e2]; janus_simp
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e3]; janus_simp
  all_goals first | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | skip
  janus_frame

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem tailB {impl : List Segment} (hap : ImplApart Extracted.program impl) (Q : State → Prop)
    (S : State) (sp g st n0 p l c ret : Nat) (r18 r29 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 tB) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h2 : S.regs 2 = BitVec.ofNat 64 l) (h1 : S.regs 1 = BitVec.ofNat 64 c)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (hp : p < 2 ^ 64) (hl : l < 2 ^ 64) (hc : c < 2 ^ 64) (he : TEnv sp g st n0 r29 ret M)
    (KF : ∀ s', TPost sp g st n0 p l c r18 r29 M s' → Q s') :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hacc, hg1, hg2, hg3, hgw, r448, r416, r424, r432, hst1, hst2, hn0, hstw, hstg, rfp, rlr,
    hr4, hr48⟩ := he
  have hD := dfrSum impl hap
  rw [show dwE = 1797024 from rfl] at hD r416
  janus_run [r448, r416, r424, r432, rfp, rlr] calls [hD]
  rename_i _ e1 e2 e3 e4 e5 e6 _
  refine KF _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, e5, ?_⟩
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e2]; janus_simp
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e3]; janus_simp
  all_goals first | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | skip
  janus_frame


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem tailN {impl : List Segment} (hap : ImplApart Extracted.program impl) (Q : State → Prop)
    (S : State) (sp g st n0 p ret : Nat) (r18 r29 : BitVec 64) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 tN) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) 
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (hp : p < 2 ^ 64) (he : TEnv sp g st n0 r29 ret M)
    (KF : ∀ s', TPost sp g st n0 p 1 1 r18 r29 M s' → Q s') :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 ret) S Q := by
  obtain ⟨hal, hsp1, hsp2, hacc, hg1, hg2, hg3, hgw, r448, r416, r424, r432, hst1, hst2, hn0, hstw, hstg, rfp, rlr,
    hr4, hr48⟩ := he
  have hD := dfrSum impl hap
  rw [show dwE = 1797024 from rfl] at hD r416
  janus_run [r448, r416, r424, r432, rfp, rlr] calls [hD]
  rename_i _ e1 e2 e3 e4 e5 e6 _
  refine KF _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, e5, ?_⟩
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e2]; janus_simp
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e3]; janus_simp
  all_goals first | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; done) | skip
  janus_frame


end FvModexp.Arm64.P2W2
