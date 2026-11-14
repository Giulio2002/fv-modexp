import FvModexp.Proofs.Amd64.Exp.P2W2Defs
import FvModexp.Proofs.Amd64.Exp.DeferX

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the three result exits → `RET` (agent divmc s69; amd64 twin of agent infra's
`Arm64.P2W2Tail`, shaped like agent expmc's amd64 `W2Fin.atD`/`tail`)

Every exit stores the result `(p, l, c)` into the named results `0x100/0x108/0x110`, clears the defer flag `0x57`, calls
the open-coded closure `deferwrap1` (`dwE`; record `[sp + 0x1c0] = sp + 0x1a0`, code word `[sp + 0x1a0] = dwE`;
`Defer.sumX`), reloads the results into `AX/BX/CX`, `ADDQ $0x1c8, SP; POPQ BP; RET`:
* `tM` = fn+0x8ef (main exit after `z.norm()`, `CMPQ SI, R15`): `R8 = p`, `SI = l`, `R15 = c`; closure `CALL AX` +0x91c;
* `tS` = fn+0x368 (`return 1` via `setWord`, after `[SI] = 1`): `SI = p`, `DI = c`; inline `norm` of the 1-word nat
  (+0x952), `CALL AX` +0x992;
* `tN` = fn+0x385 (`return 1` via `newobject`, after `[AX] = 1`): `AX = p`, `l = c = 1`; `CALL CX` +0x3b5.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

abbrev tM : Nat := 6203151
abbrev tS : Nat := 6201736
abbrev tN : Nat := 6201765

def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2.deferwrap1"

theorem dE_eq : segAddr LibW.program fnD = dwE := by decide

theorem toNat_of {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bv_sub8 {sp : Nat} (h1 : 8 ≤ sp) (h2 : sp < 2 ^ 64) :
    BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem sp_add8 {sp : Nat} (h1 : 8 ≤ sp) (h2 : sp < 2 ^ 64) :
    BitVec.ofNat 64 (sp - 8) + 8#64 = BitVec.ofNat 64 sp := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- read-after-write closer for concrete frame offsets -/
macro "rdwP" : tactic => `(tactic| (
  simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
    show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]))

/-- the static facts of the tail at memory `M` (frame `sp`, closure record at `sp + 0x1a0`, entry stack length `n0`) -/
@[reducible] def TEnv (sp st n0 bp r : Nat) (M : Memory) : Prop :=
  sp % 8 = 0 ∧ 16 ≤ sp ∧ sp + 0x1d8 ≤ 2 ^ 48 ∧ M.accessible (sp - 16) 0x1e8 true = true ∧
    M.readLE (sp + 0x1c0) 8 = sp + 0x1a0 ∧ M.readLE (sp + 0x1a0) 8 = dwE ∧
    M.readLE (sp + 0x1a8) 8 = st ∧ M.readLE (sp + 0x1b0) 8 = n0 ∧
    st + 24 ≤ 2 ^ 48 ∧ M.accessible st 24 true = true ∧ n0 ≤ M.readLE (st + 16) 8 ∧
    Apart st 24 (sp - 16) 0x1e8 ∧ M.readLE (sp + 0x1c8) 8 = bp ∧ M.readLE (sp + 0x1d0) 8 = r ∧ r < 2 ^ 47

/-- the tail's writes -/
@[reducible] def TW (sp st : Nat) : List (Nat × Nat) :=
  [(sp - 16, sp), (sp + 0x57, sp + 0x58), (sp + 0x100, sp + 0x118), (st + 8, st + 16)]

/-- what the tail guarantees (memory relative to the memory `M` at the tail) -/
@[reducible] def TPost (sp g st n0 bp p l c : Nat) (fsB : W64) (M : Memory) (s' : State) : Prop :=
  s'.regs 4 = BitVec.ofNat 64 (sp + 0x1d8) ∧ s'.regs 5 = BitVec.ofNat 64 bp ∧ s'.regs 14 = BitVec.ofNat 64 g ∧
    s'.fsBase = fsB ∧ s'.xmm 15 = 0 ∧ s'.df = false ∧
    s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
    s'.mem.readLE (st + 8) 8 = n0 ∧ MemFrame M s'.mem (TW sp st)

theorem dPre {s : State} {sp st n0 ra : Nat} (h4 : s.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h2 : s.regs 2 = BitVec.ofNat 64 (sp + 0x1a0)) (hs1 : 16 ≤ sp) (hs2 : sp + 0x1d8 ≤ 2 ^ 48)
    (hal : sp % 8 = 0) (hacc : s.mem.accessible (sp - 16) 0x1e8 true = true)
    (rra : s.mem.readLE (sp - 8) 8 = ra) (hra : ra < 2 ^ 47) (r1a8 : s.mem.readLE (sp + 0x1a8) 8 = st)
    (r1b0 : s.mem.readLE (sp + 0x1b0) 8 = n0) (hst1 : st + 24 ≤ 2 ^ 48) (hsta : s.mem.accessible st 24 true = true)
    (hn0 : n0 ≤ s.mem.readLE (st + 16) 8) (hstw : Apart st 24 (sp - 16) 0x1e8) : Defer.Pre s := by
  have t4 : (s.regs 4).toNat = sp - 8 := by rw [h4]; exact toNat_of (by omega)
  have t2 : (s.regs 2).toNat = sp + 0x1a0 := by rw [h2]; exact toNat_of (by omega)
  unfold Defer.Pre StackWritable
  simp only [regSP, t4, t2, show sp + 0x1a0 + 8 = sp + 0x1a8 by omega, show sp + 0x1a0 + 16 = sp + 0x1b0 by omega,
    r1a8, r1b0, rra]
  unfold Apart at hstw ⊢
  refine ⟨⟨by omega, by omega, s.mem.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)⟩, by omega, by omega,
    by omega, s.mem.accessible_sub hacc (Or.inl rfl) (by omega) (by omega), by omega,
    hsta, hn0, by omega, by omega⟩

theorem tw_wr {M M' : Memory} {sp st a k : Nat} (h : MemFrame M M' (TW sp st)) (v : Nat)
    (hw : (sp + 0x57 ≤ a ∧ a + k ≤ sp + 0x58) ∨ (sp + 0x100 ≤ a ∧ a + k ≤ sp + 0x118) ∨
      (sp - 16 ≤ a ∧ a + k ≤ sp)) : MemFrame M (M'.writeLE a k v) (TW sp st) := by
  refine h.writeLE_inRanges v ?_
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h1, h2⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h1, h2⟩
  · exact ⟨_, List.mem_cons_self .., h1, h2⟩

/-- the three closure return sites (`+0x3b7`, `+0x994`, `+0x91e`) -/
@[reducible] def RaD (ra : Nat) : Prop := ra = 6201815 ∨ ra = 6203316 ∨ ra = 6203198

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- at the defer closure's entry (from any of the three exits): the call, the reload of the results, the return -/
theorem atD {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (S : State) (sp g st n0 bp r p l c ra : Nat) (fsB : W64) (M : Memory) (hra : RaD ra)
    (hpc : S.rip = BitVec.ofNat 64 dwE) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h2 : S.regs 2 = BitVec.ofNat 64 (sp + 0x1a0))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = fsB) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hs1 : 16 ≤ sp) (hs2 : sp + 0x1d8 ≤ 2 ^ 48) (hal : sp % 8 = 0)
    (hacc : S.mem.accessible (sp - 16) 0x1e8 true = true)
    (rra : S.mem.readLE (sp - 8) 8 = ra) (r1a8 : S.mem.readLE (sp + 0x1a8) 8 = st)
    (r1b0 : S.mem.readLE (sp + 0x1b0) 8 = n0) (hst1 : st + 24 ≤ 2 ^ 48) (hsta : S.mem.accessible st 24 true = true)
    (hn0 : n0 ≤ S.mem.readLE (st + 16) 8) (hstw : Apart st 24 (sp - 16) 0x1e8)
    (r100 : S.mem.readLE (sp + 0x100) 8 = p) (r108 : S.mem.readLE (sp + 0x108) 8 = l)
    (r110 : S.mem.readLE (sp + 0x110) 8 = c) (r1c8 : S.mem.readLE (sp + 0x1c8) 8 = bp)
    (r1d0 : S.mem.readLE (sp + 0x1d0) 8 = r) (hr47 : r < 2 ^ 47) (hF : MemFrame M S.mem (TW sp st)) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (TPost sp g st n0 bp p l c fsB M) := by
  have hD := Defer.sumX impl hap fnD (by simp [fnD])
  rw [dE_eq] at hD
  have u := hstw; unfold Apart at u
  have hra47 : ra < 2 ^ 47 := by rcases hra with h | h | h <;> omega
  refine ReachesRet.call hD hpc (dPre h4 h2 hs1 hs2 hal hacc rra hra47 r1a8 r1b0 hst1 hsta hn0 hstw) ?_
  intro s' hr hq
  obtain ⟨⟨e4, e5, e14, ex, hst8, hf⟩, efs, edf⟩ := hq
  have t4 : (S.regs 4).toNat = sp - 8 := by rw [h4]; exact toNat_of (by omega)
  have t2 : (S.regs 2).toNat = sp + 0x1a0 := by rw [h2]; exact toNat_of (by omega)
  simp only [t2, t4, show sp + 0x1a0 + 8 = sp + 0x1a8 by omega, show sp + 0x1a0 + 16 = sp + 0x1b0 by omega, r1a8,
    r1b0] at hst8 hf
  have rd : ∀ a, sp - 8 ≤ a → a + 8 ≤ sp + 0x1d8 → s'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2
    refine hf.readLE _ _ ?_
    simp only [outside_cons, outside_nil, and_true]
    omega
  have q100 := (rd _ (by omega) (by omega)).trans r100
  have q108 := (rd _ (by omega) (by omega)).trans r108
  have q110 := (rd _ (by omega) (by omega)).trans r110
  have q1c8 := (rd _ (by omega) (by omega)).trans r1c8
  have q1d0 := (rd _ (by omega) (by omega)).trans r1d0
  have hrip : s'.rip = BitVec.ofNat 64 ra := by rw [hr, retAddrOf_eq, t4, rra]
  have e4' : s'.regs 4 = BitVec.ofNat 64 sp := by rw [e4, h4]; exact sp_add8 (by omega) (by omega)
  have hacc' : s'.mem.accessible (sp - 16) 0x1e8 true = true := by rw [hf.accessible]; exact hacc
  have hfr : MemFrame M s'.mem (TW sp st) := hF.trans hf (fun a k ho => by
    simp only [TW, outside_cons, outside_nil, and_true] at ho ⊢
    omega)
  have efs' : s'.fsBase = fsB := efs.trans hfs
  have ex' : s'.xmm 15 = 0 := ex.trans hx15
  have e14' : s'.regs 14 = BitVec.ofNat 64 g := e14.trans h14
  have edf' : s'.df = false := edf.trans hdf
  clear e4 rd hr efs ex e14 edf hf hF
  rcases hra with rfl | rfl | rfl
  all_goals
    janus64_run [q100, q108, q110, q1c8, q1d0, Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega)]
    refine ⟨?_, ?_, ?_, efs', ex', ?_, ?_, ?_, ?_, hst8, hfr⟩
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact e14'
    · rfl
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]

end FvModexp.Amd64.P2W2
