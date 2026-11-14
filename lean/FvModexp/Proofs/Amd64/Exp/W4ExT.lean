import FvModexp.Proofs.Amd64.Exp.W4Posts
import FvModexp.Proofs.Amd64.Exp.W4Seg
import FvModexp.Proofs.Amd64.Exp.W4ExB

set_option autoImplicit false

/-!
# window-4 (amd64), after `zz = zz.sub(zz, m)` (nat.go:1484-1485; agent expmc s47)

Twin of `Arm64.W4Loop.exCmp2` / `exSubT`. From `nat.sub`'s return (+0x1130, result `(p, 0, c)` in `AX, BX, CX`): the
spills `zz → 0x188/0x98/0xa0`, the second `zz.cmp(m)` (asm's `cmp_summary`), which is `-1` because the difference has
length `0 < n` (so the `div` fallback is not taken), the reload of `zz` into `DI, SI, R8` and the jumps to the join
`njoin` (+0x11f3). Also the join's postcondition `JoinPost` (the amd64 twin of the arm64 one).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W4Loop

/-- the stack ranges written from `nat.sub`'s return to the join -/
@[reducible] def tw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4296, sp + 0x60), (sp + 0x98, sp + 0xa8), (sp + 0x188, sp + 0x190)]

theorem tw_wr {M M' : Memory} {sp a : Nat} (h : MemFrame M M' (tw sp)) (v : Nat)
    (hw : (sp - 4296 ≤ a ∧ a + 8 ≤ sp + 0x60) ∨ (sp + 0x98 ≤ a ∧ a + 8 ≤ sp + 0xa8) ∨
      (sp + 0x188 ≤ a ∧ a + 8 ≤ sp + 0x190)) : MemFrame M (M'.writeLE a 8 v) (tw sp) := by
  refine h.writeLE_inRanges v ?_
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, List.mem_cons_self .., h1, h2⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h1, h2⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h1, h2⟩

theorem cmp_lt0 {n X Y : Nat} (h : 0 < n) : CmpSum.cmpRes 0 n X Y = 18446744073709551615#64 := by
  simp [CmpSum.cmpRes, h]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- the second `zz.cmp(m)` with `len zz = 0 < len m`: result `-1`, reload `zz`, jump to the join -/
theorem exCmp2 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ret : W64}
    {Q : State → Prop} (S : State) (sp g fs p c mp n : Nat) (r5 : W64)
    (hpc : S.rip = BitVec.ofNat 64 cmpE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (hra : S.mem.readLE (sp - 8) 8 = fnE + 0x1165) (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g)
    (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h3 : S.regs 3 = BitVec.ofNat 64 0)
    (h7 : S.regs 7 = BitVec.ofNat 64 mp) (h6 : S.regs 6 = BitVec.ofNat 64 n)
    (r188 : S.mem.readLE (sp + 0x188) 8 = p) (r98 : S.mem.readLE (sp + 0x98) 8 = 0)
    (ra0 : S.mem.readLE (sp + 0xa0) 8 = c)
    (hs1 : 4296 ≤ sp) (hs2 : sp + 0x3c0 ≤ 2 ^ 48) (hacc : S.mem.accessible (sp - 4296) (4296 + 0x3c0) true = true)
    (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hm48 : mp + 8 * n ≤ 2 ^ 48) (hma : S.mem.accessible mp (8 * n) false = true)
    (hmw : Apart mp (8 * n) (sp - 4296) (4296 + 0x3c0))
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 njoin → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 0 → S'.regs 8 = BitVec.ofNat 64 c →
      MemFrame S.mem S'.mem [(sp - 4296, sp + 0x60)] → S'.mem.regions = S.mem.regions →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have tsp : (S.regs 4).toNat = sp - 8 := by rw [hsp]; exact MontW.toNat_of (by omega)
  have tm : (S.regs 7).toNat = mp := by rw [h7]; exact MontW.toNat_of (by omega)
  have tn6 : (S.regs 6).toNat = n := by rw [h6]; exact MontW.toNat_of (by omega)
  have tn3 : (S.regs 3).toNat = 0 := by rw [h3]; rfl
  have hpre : CmpSum.Pre S := by
    refine ⟨by rw [tsp, hra, fnE_eq]; omega, by omega, by omega, ?_, Or.inl tn3, Or.inr ⟨?_, ?_⟩⟩
    · rw [tsp]; exact S.mem.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)
    · rw [tm, tn6]; exact hma
    · rw [tm, tn6, tsp]; unfold Apart at hmw ⊢; omega
  refine CmpW.call (cmpSum impl hap) hpc hpre ?_
  intro S' hrip e4 e0 eo exm efs edf hf hrg
  rw [tn3, tn6, cmp_lt0 hn] at e0
  have e5 : S'.regs 5 = r5 := by rw [eo 5 (by decide) (by decide) (by decide) (by decide) (by decide), h5]
  have e14 : S'.regs 14 = BitVec.ofNat 64 g := by
    rw [eo 14 (by decide) (by decide) (by decide) (by decide) (by decide), h14]
  have hf' : MemFrame S.mem S'.mem [(sp - 4296, sp + 0x60)] := by
    refine hf.mono fun a k ho => ?_
    simp only [CmpSum.frame, tsp, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  have hrd : ∀ a, sp + 0x60 ≤ a → S'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1
    refine hf'.readLE _ _ ?_
    simp only [outside_cons, outside_nil, and_true]
    omega
  have q188 : S'.mem.readLE (sp + 0x188) 8 = p := by rw [hrd _ (by omega)]; exact r188
  have q98 : S'.mem.readLE (sp + 0x98) 8 = 0 := by rw [hrd _ (by omega)]; exact r98
  have qa0 : S'.mem.readLE (sp + 0xa0) 8 = c := by rw [hrd _ (by omega)]; exact ra0
  have hrip : S'.rip = BitVec.ofNat 64 (fnE + 0x1165) := by rw [hrip, retAddrOf_eq, tsp, hra]
  rw [fnE_eq] at hrip
  have e4' : S'.regs 4 = BitVec.ofNat 64 sp := by rw [e4, hsp]; exact sp_add8 (by omega) (by omega)
  clear e4 hrd eo
  have hm1 : (18446744073709551615#64 : BitVec 64).msb = true := by decide
  refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 6210131) ?_
  janus64_run [hm1, q188, q98, qa0, BitVec.msb_eq_decide] until [njoin]
  refine K _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf' hrg
  · rw [show njoin = 6210131 by simp only [njoin, fnE_eq]]
  · exact e4'
  · exact e5
  · exact e14
  · rw [efs, hfs]
  · rw [exm, hx15]
  · rfl
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- after `zz = zz.sub(zz, m)` (result length 0): spills, the second `zz.cmp(m)`, the join -/
theorem exSubT {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ret : W64}
    {Q : State → Prop} (S : State) (sp g fs p c mp n mc : Nat) (r5 : W64)
    (hpc : S.rip = BitVec.ofNat 64 (fnE + 0x1130)) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (h5 : S.regs 5 = r5)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (h3 : S.regs 3 = BitVec.ofNat 64 0) (h1 : S.regs 1 = BitVec.ofNat 64 c)
    (r3a8 : S.mem.readLE (sp + 0x3a8) 8 = mp) (r3b0 : S.mem.readLE (sp + 0x3b0) 8 = n)
    (r3b8 : S.mem.readLE (sp + 0x3b8) 8 = mc) (hp : p < 2 ^ 64) (hc : c < 2 ^ 64)
    (hs1 : 4296 ≤ sp) (hs2 : sp + 0x3c0 ≤ 2 ^ 48) (hacc : S.mem.accessible (sp - 4296) (4296 + 0x3c0) true = true)
    (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hm48 : mp + 8 * n ≤ 2 ^ 48) (hma : S.mem.accessible mp (8 * n) false = true)
    (hmw : Apart mp (8 * n) (sp - 4296) (4296 + 0x3c0))
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 njoin → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 0 → S'.regs 8 = BitVec.ofNat 64 c →
      MemFrame S.mem S'.mem (tw sp) → S'.mem.regions = S.mem.regions →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  rw [fnE_eq] at hpc
  refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 cmpE) ?_
  janus64_run [r3a8, r3b0, r3b8] until [cmpE]
  have u := hmw; unfold Apart at u
  refine exCmp2 hap _ sp g fs p c mp n r5 rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ hs1 hs2 ?_ hn hn16 hm48 ?_ hmw ?_
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact bv_sub8 (by omega) (by omega)
  · rdw; rw [fnE_eq]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  · exact hfs
  · exact hx15
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h0
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h3
  any_goals (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; done)
  · rdw
  · rdw
  · rdw
  · simp only [Arm64.Memory.accessible_writeLE]; exact hacc
  · simp only [Arm64.Memory.accessible_writeLE]; exact hma
  · intro S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hf hrg
    refine K S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ?_ ?_
    · refine MemFrame.trans (tw_wr (tw_wr (tw_wr (tw_wr (MemFrame.refl _ _) _ (by omega)) _ (by omega)) _
        (by omega)) _ (by omega)) hf (fun a k ho => ⟨ho, ?_⟩)
      simp only [tw, outside_cons, outside_nil, and_true] at ho ⊢
      exact ho.1
    · rw [hrg]; simp only [Arm64.Memory.regions_writeLE]

end FvModexp.Amd64.W4Loop
