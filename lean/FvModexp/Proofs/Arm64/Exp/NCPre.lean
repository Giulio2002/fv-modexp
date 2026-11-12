import FvModexp.Proofs.Arm64.Exp.NPost
import FvModexp.Proofs.Common.StkFrame

/-!
# `nat.expNN` (arm64): a stack-taking callee's entry facts (`NHyp.CPre`) at its call

`cpre_at`: at a callee entry `S` (`SP' = sp + 1056`, window `[sp + 1056 - stk, sp + 1168)`, `stk ≤ K + 1056`) whose
memory is the entry memory changed only in the runtime ranges and expNN's window (`R.rt ++ wN`), live objects
untouched, live set `L1 ⊇ L`, from `NPre` at the entry: `NHyp.CPre` for the inputs among `x`, `y`, `m` and the `z`
argument `(zq, zcq)` (`ZQ`: empty, or apart from the window, the guard word, the stack and the operands).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

/-- the callee's `z` argument at the call (memory `M`, live set `L1`) -/
@[reducible] def ZQ (R : RtInv) (L1 : List (Nat × Nat)) (g sp K st xp xl yp yl mp n : Nat) (M : Memory)
    (zq zcq : Nat) : Prop :=
  zcq < 2 ^ 40 ∧ NatLive M R L1 zq zcq ∧
  (0 < zcq → Apart zq (8 * zcq) (sp - K) (K + 1432) ∧ Apart zq (8 * zcq) (g + 16) 8 ∧ Apart zq (8 * zcq) st 24 ∧
    Apart zq (8 * zcq) (NHyp.freeOf M st).1 (NHyp.freeOf M st).2 ∧ Apart zq (8 * zcq) RunIface.gA 32 ∧
    Apart zq (8 * zcq) xp (8 * xl) ∧ Apart zq (8 * zcq) yp (8 * yl) ∧ Apart zq (8 * zcq) mp (8 * n))

/-- a held range apart from the window keeps its bytes -/
theorem rd_held {R : RtInv} {L : List (Nat × Nat)} {sp K a k : Nat} {M m : Memory}
    (hH : InRanges a k L ∨ Outside a k R.rt) (hLF : LiveFrame M m L []) (hMF : MemFrame M m (R.rt ++ wN sp K))
    (hw : Apart a k (sp - K) (K + 1432)) : m.readLE a k = M.readLE a k :=
  rd_mk hH hLF hMF (by unfold Apart at hw; simp only [wN, outside_cons, outside_nil, and_true]; omega)

theorem held_sub {R : RtInv} {L : List (Nat × Nat)} {a k b n : Nat} (h : InRanges a k L ∨ Outside a k R.rt)
    (h1 : a ≤ b) (h2 : b + n ≤ a + k) : InRanges b n L ∨ Outside b n R.rt :=
  h.elim (fun h => Or.inl (h.sub h1 h2)) (fun h => Or.inr (h.of_sub h1 h2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- an operand's input facts at the callee entry -/
theorem opnd_at {R : RtInv} {L L1 : List (Nat × Nat)} {sp K st stk p k zq zcq : Nat} {s S : State}
    (hO : NE R L sp K st s.mem p (8 * k)) (hacc : s.mem.accessible p (8 * k) false = true) (h48 : p + 8 * k ≤ 2 ^ 48)
    (hN : NatNorm s.mem p k) (hk : k ≤ 2 ^ 9)
    (hF : MemFrame s.mem S.mem (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem S.mem L []) (hx : LiveExt R L L1)
    (hSsp : S.sp.toNat = sp + 1056) (hstk : stk ≤ K + 1056) (hK : K ≤ sp)
    (ew : stW S.mem st = stW s.mem st) (el : stLen S.mem st = stLen s.mem st) (ec : stCap S.mem st = stCap s.mem st)
    (hz : 0 < zcq → Apart zq (8 * zcq) p (8 * k)) :
    ExpHyp.RdIn R L1 S stk 112 p k ∧ k ≤ 2 ^ 9 ∧ NatNorm S.mem p k ∧ Apart p (8 * k) st 24 ∧
      Apart p (8 * k) (NHyp.freeOf S.mem st).1 (NHyp.freeOf S.mem st).2 ∧ (0 < zcq → Apart zq (8 * zcq) p (8 * k)) := by
  obtain ⟨hH, hw, hst, hfr⟩ := hO
  refine ⟨⟨by omega, by rw [hF.accessible]; exact hacc, h48, hx.held hH, ?_⟩, hk, ?_, hst, ?_, hz⟩
  · simp only [win, hSsp, outside_cons, outside_nil, and_true]; unfold Apart at hw; omega
  · rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact Or.inl hk0
    rcases hN with h0 | h1
    · exact Or.inl h0
    · right
      rw [rd_held (held_sub hH (by omega) (by omega)) hLF hF (by unfold Apart at hw ⊢; omega)]; exact h1
  · show Apart p (8 * k) (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact hfr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `NHyp.CPre` at a callee entry -/
theorem cpre_at {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat} {s S : State}
    (hP : NPre R b L K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (hF : MemFrame s.mem S.mem (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem S.mem L []) (hrg : S.mem.regions = s.mem.regions)
    {L1 : List (Nat × Nat)} {b1 : Nat} (hx : LiveExt R L L1) (hinv : R.inv b1 L1 g (view R.rt L1 S.mem))
    (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056)) (h28 : S.regs 28 = BitVec.ofNat 64 g) {stk : Nat}
    (hstk : stk ≤ K + 1056)
    {zq zl' zcq : Nat} (hzq : ZQ R L1 g sp K st xp xl yp yl mp n S.mem zq zcq) (hzl : zl' ≤ zcq)
    {ins : List (Nat × Nat)} (hins : ∀ p k, (p, k) ∈ ins → (p = xp ∧ k = xl) ∨ (p = yp ∧ k = yl) ∨ (p = mp ∧ k = n))
    {need cst : Nat} (hneed : stLen s.mem st + need ≤ 2 ^ 16) (hcst : cst ≤ b1) :
    NHyp.CPre R b1 L1 stk 112 zq zl' zcq st ins need cst S := by
  obtain ⟨⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK, hK', hsp2, hacc, hwrt, hLs, hd, hsv⟩, -, hgl, hro, hty, -,
    hn, hn128, -, -, hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, -, hxO, hxa, hx48, hxN, hxl, -, -, -, -, -, -,
    hgO, -, -, -, hsok, hstw, hstg, harr, hc0, hwbf, hwbA, hstf, hfg, -, -, -, -, -, -⟩ := hP
  have hSs : S.sp.toNat = sp + 1056 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  have hSg : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; omega
  have hout : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  simp only [outside_cons] at hgo
  have hgw : Outside (g + 16) 8 (wN sp K) := by
    simp only [wN, outside_cons, outside_nil, and_true]; omega
  have hgM : S.mem.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 :=
    hF.readLE _ _ (by rw [outside_append]; exact ⟨hgo.2, hgw⟩)
  -- the stack header
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF hF (by unfold Apart at hstw ⊢; omega)
  have ew : stW S.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S.mem st = stCap s.mem st := rdh 16 (by omega)
  obtain ⟨hzq40, hzqL, hzqA⟩ := hzq
  have hwin : ∀ {a k : Nat}, Apart a k (sp - K) (K + 1432) → Outside a k (win S stk 112) := fun h => by
    unfold Apart at h; simp only [win, hSs, outside_cons, outside_nil, and_true]; omega
  -- the globals
  have hgl' : RunIface.Globals R S.mem (win S stk 112) := by
    obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw', hwbacc, hwbrt, hwbw⟩ := hgl
    have hgA : Outside RunIface.gA 32 (R.rt ++ wN sp K) := by
      simp only [wN, outside_append, outside_cons, outside_nil, and_true] at hgw' ⊢
      exact ⟨hgrt, by omega, by omega⟩
    have hrd : ∀ k, k + 8 ≤ 32 → S.mem.readLE (RunIface.gA + k) 8 = s.mem.readLE (RunIface.gA + k) 8 := fun k hk =>
      hF.readLE _ _ (hgA.of_sub (by omega) (by omega))
    refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, (hF.accessible _ _ _).trans hgacc, hgrt, ?_,
      (hF.accessible _ _ _).trans hwbacc, hwbrt, ?_⟩
    · rw [e8, hrd 8 (by omega), ← e8]; exact h40
    · rw [e16, hrd 16 (by omega), ← e16]; exact h12
    · rw [e24, hrd 24 (by omega), ← e24]; exact h80
    · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
      show S.mem.readLE RunIface.gA 8 = 40; rw [this]; exact h40'
    · simp only [win, hSs, outside_cons, outside_nil, and_true] at hgw' ⊢; omega
    · simp only [win, hSs, outside_cons, outside_nil, and_true] at hwbw ⊢; omega
  have hgOa := hgO.2.2.1
  refine ⟨⟨⟨by rw [hSg]; exact hg1, by rw [hSg, hF.accessible]; exact hg2, by rw [hSg, hgM, hSs]; omega⟩,
      ⟨by rw [hSs]; omega, by rw [hSs]; omega, by rw [hSs]; omega, by
        rw [hSs, hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)⟩,
      dataLoaded_frame hd hrg hro hF (fun r hr _ => by
        simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hacc (by omega) (by omega)),
      by rw [hSs]; exact hout.of_sub (by omega) (by omega), by rw [hSg, hSs]; unfold Apart; omega,
      by rw [hSg]; exact hgo.2, ?_, hro⟩,
    hsv, hgl', hro, hty, hzl, ⟨hzq40, hzqL, fun hc => ?_⟩,
    fun p k hpk => ?_, stkOK_hdr hsok hF ew el ec hx, hwin hstw, by rw [hSg]; exact hstg, ?_, by rw [ec, ew]; exact hc0,
    by rw [el]; exact hneed, by rw [hF.accessible]; exact hwbf, hwbA, ?_, fun hc => ?_, by unfold Apart at hgOa ⊢; omega,
    ?_, hcst, by rw [hSg]; exact hinv⟩
  · refine hx.liveSep (LiveSep.sub_win hLs (by rw [hSs]; omega) (by rw [hSs]; omega)) fun r hr => ?_
    simp only [win, List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by rw [hSs]; omega) (by rw [hSs]; omega)
  · obtain ⟨a1, a2, -⟩ := hzqA hc
    exact ⟨hwin a1, by rw [hSg]; unfold Apart at a2 ⊢; omega⟩
  · rcases hins p k hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact opnd_at hxO hxa hx48 hxN (by omega) hF hLF hx hSs hstk hK' ew el ec fun hc => (hzqA hc).2.2.2.2.2.1
    · exact opnd_at hyO hya hy48 hyN hyl hF hLF hx hSs hstk hK' ew el ec fun hc => (hzqA hc).2.2.2.2.2.2.1
    · exact opnd_at hmO hma hm48 hmN (by omega) hF hLF hx hSs hstk hK' ew el ec fun hc => (hzqA hc).2.2.2.2.2.2.2
  · rw [ec, ew, hSg]; intro hc
    obtain ⟨a1, a2⟩ := harr hc
    exact ⟨hwin a1, a2⟩
  · show Apart st 24 (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact hstf
  · obtain ⟨-, -, a3, a4, a5, -⟩ := hzqA hc
    exact ⟨a3, a4, a5⟩
  · show Apart (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st)) RunIface.gA 32
    rw [ew, el, ec]; exact hfg

end FvModexp.Arm64.ExpN
