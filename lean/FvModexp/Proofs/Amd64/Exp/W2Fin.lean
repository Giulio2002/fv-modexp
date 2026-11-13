import FvModexp.Proofs.Amd64.Exp.W2ExB
import FvModexp.Proofs.Amd64.Exp.DeferX
import FvModexp.Proofs.Common.ExpNorm

set_option autoImplicit false

/-!
# window-2 (amd64), the end: `return zz.norm()` (nat.go:1490) with the deferred `stk.restore` (agent expmc s60, ported from the window-4 twin)

Twin of `Arm64.W2Loop.fin`/`tail`. From the join point `njoin` (+0x1140: `zz` in `DI, SI, R8` after the final
reduction) the inline `norm` loop (`TESTQ SI, SI; JLE; MOVQ -8(DI)(SI*8), AX; TESTQ AX, AX; JE → DECQ SI`), the bounds
check `CMPQ SI, R8; JA panic` (+0x114f), the named-result stores `0x178/0x180/0x188`, `MOVB $0, 0x77(SP)`, the call of
the open-coded defer closure (`[sp + 0x260] = sp + 0x228`, code word `[sp + 0x228]` = the closure entry `0x5ed6a0`;
`Defer.sumX`), the reload of the results, `ADDQ $0x268, SP; POPQ BP; RET`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Loop

/-- after the norm loop: `CMPQ SI, R8` -/
abbrev tailPc : Nat := fnE + 0x114f

def fnD : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2.deferwrap1"

theorem dE_eq : segAddr LibW.program fnD = 6215328 := by decide

/-- the static facts of the end (memory `M` at the join point; `bp` the caller's frame pointer, `r` the return
address) -/
@[reducible] def FinEnv (sp st n0 bp r : Nat) (M : Memory) : Prop :=
  sp % 16 = 0 ∧ 4296 ≤ sp ∧ sp + 0x2a8 ≤ 2 ^ 48 ∧ M.accessible (sp - 4296) (4296 + 0x2a8) true = true ∧
    M.readLE (sp + 0x260) 8 = sp + 0x228 ∧ M.readLE (sp + 0x228) 8 = 6215328 ∧
    M.readLE (sp + 0x230) 8 = st ∧ M.readLE (sp + 0x238) 8 = n0 ∧
    st + 24 ≤ 2 ^ 48 ∧ M.accessible st 24 true = true ∧ n0 ≤ M.readLE (st + 16) 8 ∧
    Apart st 24 (sp - 4296) (4296 + 0x2a8) ∧ M.readLE (sp + 0x268) 8 = bp ∧ M.readLE (sp + 0x270) 8 = r ∧ r < 2 ^ 47

/-- what the end guarantees (memory relative to the memory `M` at the join point) -/
@[reducible] def FinPost (sp g fs st n0 bp p l c : Nat) (M : Memory) (s' : State) : Prop :=
  s'.regs 4 = BitVec.ofNat 64 (sp + 0x278) ∧ s'.regs 5 = BitVec.ofNat 64 bp ∧ s'.regs 14 = BitVec.ofNat 64 g ∧
    s'.fsBase.toNat = fs ∧ s'.xmm 15 = 0 ∧ s'.df = false ∧
    s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 c ∧
    s'.mem.readLE (st + 8) 8 = n0 ∧
    MemFrame M s'.mem [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x178, sp + 0x190), (st + 8, st + 16)]

theorem dPre {s : State} {sp st n0 : Nat} (h4 : s.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h2 : s.regs 2 = BitVec.ofNat 64 (sp + 0x228)) (hs1 : 4296 ≤ sp) (hs2 : sp + 0x2a8 ≤ 2 ^ 48)
    (hal : sp % 16 = 0) (hacc : s.mem.accessible (sp - 4296) (4296 + 0x2a8) true = true)
    (rra : s.mem.readLE (sp - 8) 8 = 6215038) (r348 : s.mem.readLE (sp + 0x230) 8 = st)
    (r350 : s.mem.readLE (sp + 0x238) 8 = n0) (hst1 : st + 24 ≤ 2 ^ 48) (hsta : s.mem.accessible st 24 true = true)
    (hn0 : n0 ≤ s.mem.readLE (st + 16) 8) (hstw : Apart st 24 (sp - 4296) (4296 + 0x2a8)) : Defer.Pre s := by
  have t4 : (s.regs 4).toNat = sp - 8 := by rw [h4]; exact MontW.toNat_of (by omega)
  have t2 : (s.regs 2).toNat = sp + 0x228 := by rw [h2]; exact MontW.toNat_of (by omega)
  unfold Defer.Pre StackWritable
  simp only [regSP, t4, t2, show sp + 0x228 + 8 = sp + 0x230 by omega, show sp + 0x228 + 16 = sp + 0x238 by omega,
    r348, r350, rra]
  unfold Apart at hstw ⊢
  refine ⟨⟨by omega, by omega, s.mem.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)⟩, by omega, by omega,
    by omega, s.mem.accessible_sub hacc (Or.inl rfl) (by omega) (by omega), by omega,
    hsta, hn0, by omega, by omega⟩

/-- the stack ranges written by the end before the defer call -/
@[reducible] def ftw (sp : Nat) : List (Nat × Nat) := [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x178, sp + 0x190)]

theorem ftw_wr {M M' : Memory} {sp a k : Nat} (h : MemFrame M M' (ftw sp)) (v : Nat)
    (hw : (sp - 16 ≤ a ∧ a + k ≤ sp) ∨ (sp + 0x77 ≤ a ∧ a + k ≤ sp + 0x78) ∨
      (sp + 0x178 ≤ a ∧ a + k ≤ sp + 0x190)) : MemFrame M (M'.writeLE a k v) (ftw sp) := by
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
    (hpc : S.rip = BitVec.ofNat 64 6215328) (h4 : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h2 : S.regs 2 = BitVec.ofNat 64 (sp + 0x228))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hs1 : 4296 ≤ sp) (hs2 : sp + 0x2a8 ≤ 2 ^ 48) (hal : sp % 16 = 0)
    (hacc : S.mem.accessible (sp - 4296) (4296 + 0x2a8) true = true)
    (rra : S.mem.readLE (sp - 8) 8 = 6215038) (r348 : S.mem.readLE (sp + 0x230) 8 = st)
    (r350 : S.mem.readLE (sp + 0x238) 8 = n0) (hst1 : st + 24 ≤ 2 ^ 48) (hsta : S.mem.accessible st 24 true = true)
    (hn0 : n0 ≤ S.mem.readLE (st + 16) 8) (hstw : Apart st 24 (sp - 4296) (4296 + 0x2a8))
    (r170 : S.mem.readLE (sp + 0x178) 8 = p) (r178 : S.mem.readLE (sp + 0x180) 8 = l)
    (r180 : S.mem.readLE (sp + 0x188) 8 = c) (r380 : S.mem.readLE (sp + 0x268) 8 = bp)
    (r388 : S.mem.readLE (sp + 0x270) 8 = r) (hr47 : r < 2 ^ 47) (hF : MemFrame M S.mem (ftw sp)) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FinPost sp g fs st n0 bp p l c M) := by
  have hD := Defer.sumX impl hap fnD (by simp [fnD])
  rw [dE_eq] at hD
  have u := hstw; unfold Apart at u
  refine ReachesRet.call hD hpc (dPre h4 h2 hs1 hs2 hal hacc rra r348 r350 hst1 hsta hn0 hstw) ?_
  intro s' hr hq
  obtain ⟨⟨e4, e5, e14, ex, hst8, hf⟩, efs, edf⟩ := hq
  have t4 : (S.regs 4).toNat = sp - 8 := by rw [h4]; exact MontW.toNat_of (by omega)
  have t2 : (S.regs 2).toNat = sp + 0x228 := by rw [h2]; exact MontW.toNat_of (by omega)
  simp only [t2, t4, show sp + 0x228 + 8 = sp + 0x230 by omega, show sp + 0x228 + 16 = sp + 0x238 by omega, r348,
    r350] at hst8 hf
  have rd : ∀ a, sp - 8 ≤ a → a + 8 ≤ sp + 0x2a8 → s'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2
    refine hf.readLE _ _ ?_
    simp only [outside_cons, outside_nil, and_true]
    omega
  have q170 := (rd _ (by omega) (by omega)).trans r170
  have q178 := (rd _ (by omega) (by omega)).trans r178
  have q180 := (rd _ (by omega) (by omega)).trans r180
  have q380 := (rd _ (by omega) (by omega)).trans r380
  have q388 := (rd _ (by omega) (by omega)).trans r388
  have hrip : s'.rip = BitVec.ofNat 64 6215038 := by rw [hr, retAddrOf_eq, t4, rra]
  have e4' : s'.regs 4 = BitVec.ofNat 64 sp := by rw [e4, h4]; exact sp_add8 (by omega) (by omega)
  have hacc' : s'.mem.accessible (sp - 4296) (4296 + 0x2a8) true = true := by rw [hf.accessible]; exact hacc
  clear e4 rd hr
  janus64_run [q170, q178, q180, q380, q388, Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega)]
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
/-- one test of the inline `zz.norm()` loop (nat.go:68-74) from `njoin` with `SI = l`: either the loop exits to
`tailPc` (`l = 0` or limb `l-1` nonzero) or it goes back to `njoin` with `SI = l - 1` (limb `l-1` zero) -/
theorem finIter {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    (S : State) (sp g fs p l c : Nat) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 njoin) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h7 : S.regs 7 = BitVec.ofNat 64 p) (h6 : S.regs 6 = BitVec.ofNat 64 l) (h8 : S.regs 8 = BitVec.ofNat 64 c)
    (hmem : S.mem = M) (hl : l < 2 ^ 48) (hp : p < 2 ^ 64)
    (hpa : l = 0 ∨ (p + 8 * l ≤ 2 ^ 48 ∧ M.accessible p (8 * l) false = true))
    (KT : ∀ S' : State, S'.rip = BitVec.ofNat 64 tailPc → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 l → S'.regs 8 = BitVec.ofNat 64 c → S'.mem = M →
      (l = 0 ∨ M.readLE (p + 8 * (l - 1)) 8 ≠ 0) → ReachesRet (LibW.program.link impl) ret S' Q)
    (KL : ∀ S' : State, 0 < l → M.readLE (p + 8 * (l - 1)) 8 = 0 →
      S'.rip = BitVec.ofNat 64 njoin → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 (l - 1) → S'.regs 8 = BitVec.ofNat 64 c →
      S'.mem = M → ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  rw [show njoin = 6214976 by simp only [njoin, fnE_eq]] at hpc
  have eT : tailPc = 6214991 := by simp only [tailPc, fnE_eq]
  have eJ : njoin = 6214976 := by simp only [njoin, fnE_eq]
  rcases hpa with hl0 | ⟨hp48, hacc⟩
  · subst hl0
    have hz : (BitVec.ofNat 64 0 : BitVec 64) = 0#64 := rfl
    janus64_run until [6214976, 6214991]
    refine KT _ ?_ hsp h14 hfs hx15 rfl h7 h6 h8 rfl (Or.inl rfl)
    rw [eT]
  · rcases l with _ | l
    · janus64_run until [6214976, 6214991]
      refine KT _ ?_ hsp h14 hfs hx15 rfl h7 h6 h8 rfl (Or.inl rfl)
      rw [eT]
    · have ea : p + (l + 1) * 8 - 8 = p + 8 * l := by omega
      have hms : (BitVec.ofNat 64 (l + 1)).msb = false := by
        rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
      janus64_run [ea, hms] until [6214976, 6214991]
      · refine KL _ (by omega) (by simpa using hbr) ?_ ?_ ?_ hfs hx15 rfl ?_ ?_ ?_ rfl
        · rw [eJ]
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hsp
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h7
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h8
      · refine KT _ ?_ ?_ ?_ hfs hx15 rfl ?_ ?_ ?_ rfl (Or.inr (by simpa using hbr))
        · rw [eT]
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hsp
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h7
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h6
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h8


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- from the bounds check `+0x114f` to the return -/
theorem tail {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (S : State) (sp g fs st n0 bp r p l c : Nat) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 tailPc) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h7 : S.regs 7 = BitVec.ofNat 64 p) (h6 : S.regs 6 = BitVec.ofNat 64 l) (h8 : S.regs 8 = BitVec.ofNat 64 c)
    (hmem : S.mem = M) (hlc : l ≤ c) (hc : c < 2 ^ 64) (hp : p < 2 ^ 64) (hbp : bp < 2 ^ 64)
    (he : FinEnv sp st n0 bp r M) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FinPost sp g fs st n0 bp p l c M) := by
  obtain ⟨hal, hs1, hs2, hacc, r378, r340, r348, r350, hst1, hsta, hn0, hstw, r380, r388, hr47⟩ := he
  subst hmem
  have u := hstw; unfold Apart at u
  have hlt : ¬ (c < l) := by omega
  rw [show tailPc = 6214991 by simp only [tailPc, fnE_eq]] at hpc
  janus64_run [r378, r340, hlt] until [6215328]
  refine atD hap _ sp g fs st n0 bp r p l c _ rfl ?_ ?_ ?_ hfs hx15 rfl hs1 hs2 hal ?_ ?_ ?_ ?_ hst1 ?_ ?_ hstw
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact bv_sub8 (by omega) (by omega)
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  · simp only [Arm64.Memory.accessible_writeLE]; exact hacc
  · rdw
  · rdw; exact r348
  · rdw; exact r350
  · simp only [Arm64.Memory.accessible_writeLE]; exact hsta
  · rdw; exact hn0
  · rdw
  · rdw
  · rdw
  · rdw; exact r380
  · rdw; exact r388
  · exact hr47
  · exact ftw_wr (ftw_wr (ftw_wr (ftw_wr (ftw_wr (MemFrame.refl _ _) _ (by omega)) _ (by omega)) _ (by omega)) _
      (by omega)) _ (by omega)

end FvModexp.Amd64.W2Loop

namespace FvModexp.Amd64.W2Loop

/-- the inline `zz.norm()` loop (nat.go:68-74) from the join point, then `tail` -/
theorem fin {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (sp g fs st n0 bp r p c : Nat) (M : Memory) (hc : c < 2 ^ 40) (hp : p < 2 ^ 64) (hbp : bp < 2 ^ 64)
    (he : FinEnv sp st n0 bp r M) :
    ∀ (l : Nat) (S : State), S.rip = BitVec.ofNat 64 njoin → S.regs 4 = BitVec.ofNat 64 sp →
      S.regs 14 = BitVec.ofNat 64 g → S.fsBase.toNat = fs → S.xmm 15 = 0 → S.df = false →
      S.regs 7 = BitVec.ofNat 64 p → S.regs 6 = BitVec.ofNat 64 l → S.regs 8 = BitVec.ofNat 64 c → S.mem = M →
      l ≤ c → (l = 0 ∨ (p + 8 * l ≤ 2 ^ 48 ∧ M.accessible p (8 * l) false = true)) →
      ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
        (FinPost sp g fs st n0 bp p (Expmc.normL M p l) c M) := by
  intro l
  induction l with
  | zero =>
    intro S hpc hsp h14 hfs hx15 hdf h7 h6 h8 hmem hlc hpa
    refine finIter S sp g fs p 0 c M hpc hsp h14 hfs hx15 hdf h7 h6 h8 hmem (by omega) hp (Or.inl rfl) ?_ ?_
    · intro S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 _
      exact tail hap S' sp g fs st n0 bp r p 0 c M a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (by omega) (by omega) hp hbp he
    · intro _ h; omega
  | succ l ih =>
    intro S hpc hsp h14 hfs hx15 hdf h7 h6 h8 hmem hlc hpa
    obtain ⟨hp48, hacc⟩ := hpa.resolve_left (by omega)
    refine finIter S sp g fs p (l + 1) c M hpc hsp h14 hfs hx15 hdf h7 h6 h8 hmem (by omega) hp
      (Or.inr ⟨hp48, hacc⟩) ?_ ?_
    · intro S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hnz
      have hN : Expmc.normL M p (l + 1) = l + 1 := by
        simp only [Expmc.normL]; rw [if_neg]; simpa using hnz
      rw [hN]
      exact tail hap S' sp g fs st n0 bp r p (l + 1) c M a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hlc (by omega) hp hbp he
    · intro S' _ hz a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
      have hN : Expmc.normL M p (l + 1) = Expmc.normL M p l := by
        simp only [Expmc.normL]; rw [if_pos (by simpa using hz)]
      rw [hN]
      exact ih S' a1 a2 a3 a4 a5 a6 a7 a8 (by simpa using a9) a10 (by omega)
        (Or.inr ⟨by omega, M.accessible_sub hacc (Or.inl rfl) (Nat.le_refl _) (by omega)⟩)

end FvModexp.Amd64.W2Loop
