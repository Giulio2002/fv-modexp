import FvModexp.Proofs.Amd64.Exp.EvDefs
import FvModexp.Proofs.Amd64.Exp.DeferX
import FvModexp.Proofs.Common.Link

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): `addR` → deferred `stk.restore(len₀)` → `RET` (asm s64; twin of infra's arm64 `EvTail`,
pattern of expmc's amd64 `W2Fin.atD`/`tail`)

At `addR` (`0x5e87c9`): `MOVQ AX/BX/CX → 0xe0/0xe8/0xf0(SP)`; `MOVB $0, 0x77(SP)` (defer bit); `DX = [0x138] = sp +
0x120` (the closure record: `[0x120] = deferwrap1`, `[0x128] = st`, `[0x130] = len₀`), `R12 = [DX]`, `CALL R12` (ret
`dwR`; `Defer.sumX0` lifted to `LibNE`: `dfrSum`); reload `AX/BX/CX`, `ADDQ $0x140, SP`, `POPQ BP`, `RET`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- the closure (`Defer.sumX0`, proved on `LibDefer`) as a callee in `LibNE` -/
theorem dfrSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    Summary (LibNE.program.link impl) dwE Defer.Pre Defer.PostX := by
  have hsub : ∀ x, LibDefer.names.contains x = true → LibNE.names.contains x = true := by
    have h : LibDefer.names.Sublist LibNE.names := by decide +kernel
    intro x hx
    simp only [List.contains_iff_mem] at hx ⊢
    exact h.subset hx
  have hc := A64.codeIn_restrict_mono64 hap hsub
  rw [← LibDefer.eq_only, ← LibNE.eq_only] at hc
  have h := Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc (Defer.sumX0 impl fnDw (by simp [fnDw]))
  have e : segAddr LibDefer.program fnDw = dwE := by decide
  rw [e] at h
  exact h

theorem tN8 {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem evsub8 {sp : Nat} (h1 : 8 ≤ sp) (h2 : sp < 2 ^ 64) :
    BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem evadd8 {sp : Nat} (h1 : 8 ≤ sp) (h2 : sp < 2 ^ 64) :
    BitVec.ofNat 64 (sp - 8) + 8#64 = BitVec.ofNat 64 sp := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- the static facts of the tail at memory `M` (frame `sp`, closure record at `sp + 0x120`, entry stack length `n0`,
`bp` the caller's `RBP`, `r` the return address) -/
@[reducible] def TEnv (sp st n0 bp r : Nat) (M : Memory) : Prop :=
  sp % 8 = 0 ∧ 16 ≤ sp ∧ sp + 0x1b8 ≤ 2 ^ 48 ∧ M.accessible (sp - 16) (16 + 0x1b8) true = true ∧
    M.readLE (sp + 0x138) 8 = sp + 0x120 ∧ M.readLE (sp + 0x120) 8 = dwE ∧
    M.readLE (sp + 0x128) 8 = st ∧ M.readLE (sp + 0x130) 8 = n0 ∧
    st + 24 ≤ 2 ^ 48 ∧ M.accessible st 24 true = true ∧ n0 ≤ M.readLE (st + 16) 8 ∧
    Apart st 24 (sp - 16) (16 + 0x1b8) ∧ M.readLE (sp + 0x140) 8 = bp ∧ M.readLE (sp + 0x148) 8 = r ∧ r < 2 ^ 47

/-- the stack ranges the tail writes before the defer call -/
@[reducible] def ftw (sp : Nat) : List (Nat × Nat) := [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0xe0, sp + 0xf8)]

/-- the tail's writes -/
@[reducible] def TW (sp st : Nat) : List (Nat × Nat) :=
  [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0xe0, sp + 0xf8), (st + 8, st + 16)]

/-- what the tail guarantees (memory relative to `M`) -/
@[reducible] def TPost (sp g fs st n0 bp p l c : Nat) (M : Memory) (s' : State) : Prop :=
  s'.regs 4 = BitVec.ofNat 64 (sp + 0x150) ∧ s'.regs 5 = BitVec.ofNat 64 bp ∧ s'.regs 14 = BitVec.ofNat 64 g ∧
    s'.fsBase.toNat = fs ∧ s'.xmm 15 = 0 ∧ s'.df = false ∧
    s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
    s'.mem.readLE (st + 8) 8 = n0 ∧ MemFrame M s'.mem (TW sp st)

theorem dPre {s : State} {sp st n0 : Nat} (h4 : s.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h2 : s.regs 2 = BitVec.ofNat 64 (sp + 0x120)) (hs1 : 16 ≤ sp) (hs2 : sp + 0x1b8 ≤ 2 ^ 48)
    (hal : sp % 8 = 0) (hacc : s.mem.accessible (sp - 16) (16 + 0x1b8) true = true)
    (rra : s.mem.readLE (sp - 8) 8 = dwR) (r128 : s.mem.readLE (sp + 0x128) 8 = st)
    (r130 : s.mem.readLE (sp + 0x130) 8 = n0) (hst1 : st + 24 ≤ 2 ^ 48) (hsta : s.mem.accessible st 24 true = true)
    (hn0 : n0 ≤ s.mem.readLE (st + 16) 8) (hstw : Apart st 24 (sp - 16) (16 + 0x1b8)) : Defer.Pre s := by
  have t4 : (s.regs 4).toNat = sp - 8 := by rw [h4]; exact tN8 (by omega)
  have t2 : (s.regs 2).toNat = sp + 0x120 := by rw [h2]; exact tN8 (by omega)
  unfold Defer.Pre StackWritable
  simp only [regSP, t4, t2, show sp + 0x120 + 8 = sp + 0x128 by omega, show sp + 0x120 + 16 = sp + 0x130 by omega,
    r128, r130, rra]
  unfold Apart at hstw ⊢
  refine ⟨⟨by omega, by omega, s.mem.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)⟩, by omega,
    by simp only [dwR]; omega, by omega, s.mem.accessible_sub hacc (Or.inl rfl) (by omega) (by omega), by omega,
    hsta, hn0, by omega, by omega⟩

theorem ftw_wr {M M' : Memory} {sp a k : Nat} (h : MemFrame M M' (ftw sp)) (v : Nat)
    (hw : (sp - 16 ≤ a ∧ a + k ≤ sp) ∨ (sp + 0x77 ≤ a ∧ a + k ≤ sp + 0x78) ∨
      (sp + 0xe0 ≤ a ∧ a + k ≤ sp + 0xf8)) : MemFrame M (M'.writeLE a k v) (ftw sp) := by
  refine h.writeLE_inRanges v ?_
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, List.mem_cons_self .., h1, h2⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h1, h2⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h1, h2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- at the defer closure's entry: the call, the reload of the results, the return -/
theorem atD {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (S : State) (sp g fs st n0 bp r p l c : Nat) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 dwE) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h2 : S.regs 2 = BitVec.ofNat 64 (sp + 0x120))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hs1 : 16 ≤ sp) (hs2 : sp + 0x1b8 ≤ 2 ^ 48) (hal : sp % 8 = 0)
    (hacc : S.mem.accessible (sp - 16) (16 + 0x1b8) true = true)
    (rra : S.mem.readLE (sp - 8) 8 = dwR) (r128 : S.mem.readLE (sp + 0x128) 8 = st)
    (r130 : S.mem.readLE (sp + 0x130) 8 = n0) (hst1 : st + 24 ≤ 2 ^ 48) (hsta : S.mem.accessible st 24 true = true)
    (hn0 : n0 ≤ S.mem.readLE (st + 16) 8) (hstw : Apart st 24 (sp - 16) (16 + 0x1b8))
    (re0 : S.mem.readLE (sp + 0xe0) 8 = p) (re8 : S.mem.readLE (sp + 0xe8) 8 = l)
    (rf0 : S.mem.readLE (sp + 0xf0) 8 = c) (r140 : S.mem.readLE (sp + 0x140) 8 = bp)
    (r148 : S.mem.readLE (sp + 0x148) 8 = r) (hr47 : r < 2 ^ 47) (hF : MemFrame M S.mem (ftw sp)) :
    ReachesRet (LibNE.program.link impl) (BitVec.ofNat 64 r) S (TPost sp g fs st n0 bp p l c M) := by
  have hD := dfrSum impl hap
  have u := hstw; unfold Apart at u
  refine ReachesRet.call hD hpc (dPre h4 h2 hs1 hs2 hal hacc rra r128 r130 hst1 hsta hn0 hstw) ?_
  intro s' hr hq
  obtain ⟨⟨e4, e5, e14, ex, hst8, hf⟩, efs, edf⟩ := hq
  have t4 : (S.regs 4).toNat = sp - 8 := by rw [h4]; exact tN8 (by omega)
  have t2 : (S.regs 2).toNat = sp + 0x120 := by rw [h2]; exact tN8 (by omega)
  simp only [t2, t4, show sp + 0x120 + 8 = sp + 0x128 by omega, show sp + 0x120 + 16 = sp + 0x130 by omega, r128,
    r130] at hst8 hf
  have rd : ∀ a, sp ≤ a → a + 8 ≤ sp + 0x1b8 → s'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2
    refine hf.readLE _ _ ?_
    simp only [outside_cons, outside_nil, and_true]
    omega
  have qe0 := (rd _ (by omega) (by omega)).trans re0
  have qe8 := (rd _ (by omega) (by omega)).trans re8
  have qf0 := (rd _ (by omega) (by omega)).trans rf0
  have q140 := (rd _ (by omega) (by omega)).trans r140
  have q148 := (rd _ (by omega) (by omega)).trans r148
  have hrip : s'.rip = BitVec.ofNat 64 dwR := by rw [hr, retAddrOf_eq, t4, rra]
  have e4' : s'.regs 4 = BitVec.ofNat 64 sp := by rw [e4, h4]; exact evadd8 (by omega) (by omega)
  have hacc' : s'.mem.accessible (sp - 16) (16 + 0x1b8) true = true := by rw [hf.accessible]; exact hacc
  clear e4 rd hr
  janus64_run [qe0, qe8, qf0, q140, q148, Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e14, h14]
  · rw [efs, hfs]
  · rw [ex, hx15]
  · rfl
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · exact hst8
  · refine hF.trans hf (fun a k ho => ?_)
    simp only [ftw, outside_cons, outside_nil, and_true] at ho ⊢
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- **`addR` → `RET`** -/
theorem tailE {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (S : State) (sp g fs st n0 bp r p l c : Nat) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 addR) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h3 : S.regs 3 = BitVec.ofNat 64 l) (h1 : S.regs 1 = BitVec.ofNat 64 c)
    (hmem : S.mem = M) (hp : p < 2 ^ 64) (hl : l < 2 ^ 64) (hc : c < 2 ^ 64)
    (he : TEnv sp st n0 bp r M) :
    ReachesRet (LibNE.program.link impl) (BitVec.ofNat 64 r) S (TPost sp g fs st n0 bp p l c M) := by
  obtain ⟨hal, hs1, hs2, hacc, r138, r120, r128, r130, hst1, hsta, hn0, hstw, r140, r148, hr47⟩ := he
  subst hmem
  have u := hstw; unfold Apart at u
  have e8 := evsub8 (show 8 ≤ sp by omega) (show sp < 2 ^ 64 by omega)
  have hdw : dwE < 2 ^ 47 := by decide
  janus64_run [r138, r120, e8] until [6195392]
  refine atD hap _ sp g fs st n0 bp r p l c _ rfl ?_ ?_ ?_ hfs hx15 (by first | rfl | (show S.df = false; exact hdf)) hs1 hs2 hal ?_ ?_ ?_ ?_ hst1 ?_ ?_ hstw
    ?_ ?_ ?_ ?_ ?_ hr47 ?_
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  all_goals try simp only [Janus.Arm64.Memory.accessible_writeLE]
  all_goals try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  all_goals first
    | janus_assumption
    | exact ftw_wr (ftw_wr (ftw_wr (ftw_wr (ftw_wr (MemFrame.refl _ _) _ (by omega)) _ (by omega)) _ (by omega)) _
        (by omega)) _ (by omega)
    | skip

end FvModexp.Amd64.ExpEven
