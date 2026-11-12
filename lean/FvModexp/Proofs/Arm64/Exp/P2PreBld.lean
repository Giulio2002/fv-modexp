import FvModexp.Proofs.Arm64.Exp.P2PreRS

/-!
# `buildPrecomputationWindowModPower2` (arm64): callee precondition pieces from `Pre` and `Ctx` (agent infra)

For a callee at `S'` (`SP' = SP - 208`, window `stk ≤ kc`, `above ≤ 88`): `pf_of` (the entry facts `PF`), `cenv_ctx`
(the callee environment), `globals_ctx`, `stkIn_ctx`, and `bufObj` (a range of `buf`: writable, held, outside the
callee window, apart from the guard word and from the stack's header / free part).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

section
variable {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

theorem pf_of (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 8 ≤ kc) : PF R kc L st pw pl s := by
  obtain ⟨⟨-, ⟨-, hb', ha, -⟩, -, hout, -, -, hLs, -⟩, -, -, hws, hpl, -, -, -, hpw48, -, hpwrt, hpww, -, hsa, -, -, -, -,
    -, ⟨-, hstw, -, hsta⟩, -⟩ := hpre
  have hpl0 : 0 < pl := by rcases hws with rfl | rfl <;> simp [hpl]
  exact ⟨⟨hout, hstw, fun h => (hsta h).1, hb', hkc⟩, hLs, hpwrt, hpww, (hsa (by omega)).1, ha, hpw48⟩

theorem pl_facts (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) : 4 ≤ pl ∧ pl ≤ 16 ∧ pl % 2 = 0 := by
  have hws := hpre.2.2.2.1
  have hpl := hpre.2.2.2.2.1
  rcases hws with rfl | rfl <;> subst hpl <;> decide

theorem w_facts (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) : 1 ≤ W lm ∧ W lm ≤ 128 := by
  have h1 := hpre.2.2.2.2.2.1
  have h2 := hpre.2.2.2.2.2.2.1
  simp only [W]; omega

/-- the guard word is outside everything the function writes -/
theorem guard_keep (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {M : Memory}
    (hF : MemFrame s.mem M (AW R kc s pw pl st)) :
    M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
  obtain ⟨⟨-, ⟨-, hb', -, -⟩, -, -, hga, hgrt, -, -⟩, -, -, -, -, -, -, -, -, -, -, -, hpg, -, -, -, -, -, -,
    ⟨⟨-, -, -, -, -, hlc, -⟩, -, hstg, hsta⟩, -⟩ := hpre
  simp only [K, A] at hga hb'
  unfold Apart at hga hpg hstg
  refine frame_read hF fun r hr hr' => ?_
  simp only [AW, LW, stWs, stkWs, winA, K, A, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (hr | rfl | rfl) | rfl | rfl | rfl
  · have := MemFrame.outside_mem hgrt hr; omega
  · simp only at hr' ⊢; omega
  · simp only at hr' ⊢; omega
  · simp only at hr' ⊢; omega
  · simp only at hr' ⊢; omega
  · simp only at hr' ⊢
    have := (hsta (by omega)).2; unfold Apart at this; omega

set_option maxRecDepth 20000 in
/-- the callee environment at `SP' = SP - 208` (window `kc` below, `88` above) -/
theorem cenv_ctx (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) :
    CallW.CEnv R L1 (s.regs 28).toNat (s.sp.toNat - 208) kc 88 M := by
  have hgk := guard_keep hpre hc.fr
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgrt, hLs, hro⟩, -, -, -, -, -, -, -, -, hacc, -, -, -,
    -, -, ⟨-, hxa, -, -, -⟩, -, -, -, ⟨⟨-, -, hsta, -, hstl, -, -⟩, -⟩, -⟩ := hpre
  simp only [K, A] at hb' ha hw hout hga hg3 hLs
  unfold Apart at hga
  refine ⟨by omega, by omega, by omega, ?_, hg1, by rw [hc.fr.accessible]; exact hg2, by rw [hgk]; omega,
    hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgrt, ?_, ?_, hro⟩
  · rw [hc.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · refine hc.le.liveSep (fun q hq => ?_) (fun r hr => ?_)
    · have := hLs q hq
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact hout.of_sub (by omega) (by omega)
  · refine dataLoaded_frame hd hc.rg hro (by simpa only [AW, List.append_assoc] using hc.fr) ?_
    intro r hr hlt
    simp only [winA, LW, stWs, stkWs, K, A, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl | rfl | rfl
    · dsimp only at hlt ⊢; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · dsimp only at hlt ⊢; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · dsimp only at hlt ⊢; rw [show pw + 24 * pl - pw = 24 * pl by omega]; exact hacc
    · dsimp only at hlt ⊢; rw [show st + 24 - st = 24 by omega]; exact hsta
    · dsimp only at hlt ⊢
      exact Memory.accessible_mono _ (hstl (by omega)).2.2.1 (by omega) (by omega)

theorem callEnv_ctx (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {S' : State}
    (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 208)) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) : CallEnv R L1 S' stk above :=
  CallW.callEnv_of (cenv_ctx hpre hc) hsp (by rw [h28, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hm hstk habove

set_option maxRecDepth 20000 in
theorem globals_ctx (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {S' : State}
    (hsp : S'.sp.toNat = s.sp.toNat - 208) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) :
    RunIface.Globals R M (win S' stk above) := by
  have hK : 208 + kc ≤ s.sp.toNat := by have := hpre.1.2.1.2.1; simp only [K] at this; omega
  obtain ⟨-, -, ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hgf⟩ := hpre
  have hrd : ∀ a n, Outside a n (AW R kc s pw pl st) → M.readLE a n = s.mem.readLE a n := fun a n h =>
    hc.fr.readLE a n h
  have hA : ∀ a n, RunIface.gA ≤ a → a + n ≤ RunIface.gA + 32 → Outside a n (AW R kc s pw pl st) := by
    intro a n h1 h2
    have o1 := g9.of_sub h1 h2
    have o2 := g10.of_sub h1 h2
    unfold Apart at hgf
    simp only [AW, LW, stWs, stkWs, winA, K, A, List.append_assoc, List.cons_append, List.nil_append, outside_append,
      outside_cons, outside_nil, and_true] at o2 ⊢
    exact ⟨o1, by omega⟩
  have hwin : ∀ a n, Outside a n (winA s (K kc) A ++ [(pw, pw + 24 * pl), (st, st + 24)]) →
      Outside a n (win S' stk above) := by
    intro a n h
    simp only [winA, win, K, A, List.cons_append, outside_cons, outside_append, outside_nil, and_true] at h ⊢
    rw [hsp]; omega
  refine ⟨?_, ?_, ?_, ?_, g5, g6, g7, by rw [hc.fr.accessible]; exact g8, g9, hwin _ _ g10,
    by rw [hc.fr.accessible]; exact g11, g12, hwin _ _ g13⟩
  · rw [g5, hrd _ _ (hA _ _ (by omega) (by omega)), ← g5]; exact g1
  · rw [g6, hrd _ _ (hA _ _ (by omega) (by omega)), ← g6]; exact g2
  · rw [g7, hrd _ _ (hA _ _ (by omega) (by omega)), ← g7]; exact g3
  · have e : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» =
        RunIface.gA := by decide
    rw [e, hrd _ _ (hA _ _ (by omega) (by omega)), ← e]; exact g4

set_option maxRecDepth 20000 in
/-- a range of `buf` -/
theorem bufObj (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {S' : State}
    (hf : PF R kc L st pw pl s) (hsp : S'.sp.toNat = s.sp.toNat - 208) {stk above : Nat} (hstk : stk ≤ kc)
    (habove : above ≤ 88) {a n : Nat} (h1 : bp ≤ a) (h2 : a + n ≤ bp + 8 * NB pl lm) (h0 : 0 < n) :
    a + n ≤ 2 ^ 48 ∧ M.accessible a n true = true ∧ Held R L1 a n ∧ Outside a n (win S' stk above) ∧
      Apart a n ((s.regs 28).toNat + 16) 8 ∧ StkApart M st a n := by
  obtain ⟨⟨-, -, -, -, -, hgrt, -, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨-, -, -, hsta⟩, -⟩ := hpre
  have hwok := wok_buf (zp := a) (zn := n) hc.scr h1 h2
  have hwin := wok_win hwok hf.w (by simp only; omega)
  have hK := hf.w.sp
  simp only [K, A] at hwin hK
  refine ⟨by have := hc.scr.b48; omega, Memory.accessible_mono _ hc.scr.acc h1 (by omega), hc.scr.held.sub h1 h2,
    ?_, ?_, ?_⟩
  · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  · rcases hc.scr.loc with ⟨hc0, l1, l2⟩ | ⟨hin, -⟩
    · have := (hsta hc0).2; unfold Apart at this ⊢; omega
    · have := (hin.sub (a := a) (n := n) h1 (by omega)).apart hgrt; unfold Apart at this ⊢; omega
  · intro hn
    have := hc.sap (by simp only [NB] at h2 ⊢; omega)
    obtain ⟨e1, e2⟩ := this
    exact ⟨by unfold Apart at e1 ⊢; omega, fun hlt => by have := e2 hlt; unfold Apart at this ⊢; omega⟩

set_option maxRecDepth 20000 in
theorem stkIn_ctx (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {S' : State}
    (hf : PF R kc L st pw pl s) (hsp : S'.sp.toNat = s.sp.toNat - 208) (h28 : S'.regs 28 = s.regs 28)
    (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) : StkIn R L1 S' stk above st := by
  obtain ⟨⟨-, -, -, -, -, hgrt, -, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨-, hstw, hstg, hsta⟩, -⟩ := hpre
  have hK := hf.w.sp
  have hrt := hf.w.rt
  simp only [K, A] at hK hrt hstw
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  obtain ⟨hok, hl, har⟩ := hc.sa
  subst hm
  refine ⟨hok, ?_, by rw [h28]; exact hstg, fun hc0 => ?_⟩
  · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  · rw [h28]
    rcases har with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e2] at hc0; rw [e1, e2]
      obtain ⟨o1, o2⟩ := hsta hc0
      refine ⟨?_, o2⟩
      simp only [win, K, A, outside_cons, outside_nil, and_true] at o1 ⊢
      rw [hsp]; omega
    · have hin' : InRanges (stW S'.mem st) (8 * stCap S'.mem st) R.rt := hin
      have hlt : stW S'.mem st < stW S'.mem st + 8 * stCap S'.mem st := Nat.lt_add_of_pos_right (Nat.mul_pos (by decide) hc0)
      have h1 := in_rt_sep (lo := stW S'.mem st) (hi := stW S'.mem st + 8 * stCap S'.mem st)
        (by simp only [Nat.add_sub_cancel_left]; exact hin') hrt hlt
      have hA : Apart (stW S'.mem st) (8 * stCap S'.mem st) ((s.regs 28).toNat + 16) 8 := by
        have := InRanges.apart hin' hgrt; unfold Apart at this ⊢; omega
      refine ⟨?_, hA⟩
      simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

end

end FvModexp.Arm64.P2Pre
