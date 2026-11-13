import FvModexp.Proofs.Arm64.Exp.P2PreCall

/-!
# `buildPrecomputationWindowModPower2` (arm64): divmc's extra `sqr` / `mul` facts (`StkX`, `OpX`) from `Pre`/`Ctx`
(agent infra)

`stkX_ctx`: the stack object facts `StkX` at a callee state `S'` (`SP' = SP - 208`); `bufOp`: a range of `buf` is apart
from the stack's free part and the threshold globals `gA` (`OpX`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

section
variable {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

/-- the free part at `M` is apart from what the entry free part and the runtime ranges are apart from (`h0`: the
range is held in `L`, or outside the runtime) -/
theorem free_ctx (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {a n : Nat}
    (h0 : InRanges a n L ∨ Outside a n R.rt)
    (h1 : Apart a n (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))) :
    Apart a n (frP M st) (frN M st) := by
  obtain ⟨⟨-, -, -, -, -, hlc, -⟩, hl, har⟩ := hc.sa
  have hlc0 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.1
  simp only [frP, frN, lvl1] at hl hlc ⊢
  rcases har with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · rw [e2] at hlc; rw [e1, e2, hl]; unfold Apart at h1 ⊢; omega
  · have : a + n ≤ stW M st ∨ stW M st + 8 * stCap M st ≤ a := by
      rcases h0 with hL | hO
      · have := hap.apart_of_inRanges hL; omega
      · have := hin.apart hO; unfold Apart at this; omega
    unfold Apart; omega

set_option maxRecDepth 20000 in
/-- divmc's `StkX` at a callee state `S'` (`SP' = SP - 208`) -/
theorem stkX_ctx (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {S' : State}
    (hf : PF R kc L st pw pl s) (hsp : S'.sp.toNat = s.sp.toNat - 208) (h28 : S'.regs 28 = s.regs 28)
    (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 88) : StkX R L1 S' stk above st := by
  have hsi := stkIn_ctx hpre hc hf hsp h28 hm hstk habove
  have hW := w_facts hpre
  obtain ⟨-, -, ⟨-, -, -, -, -, -, -, -, g9, -, -, -, g13⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨⟨-, hhd0, -⟩, -⟩, -, hstf, -, -, -, -, -, hgst, hgf, hst0⟩ := id hpre
  have ewb : StackNat.wbA = RunIface.wbA := by decide
  have hok := hc.sa.1
  have hl := hc.sa.2.1
  obtain ⟨-, hhd, -, -, hnl, hlc, -⟩ := hok
  subst hm
  have hcap : 0 < stCap S'.mem st := by
    simp only [lvl1, NB, StackNat.rnd] at hl
    have : 0 < (pl + 1) * W lm := Nat.mul_pos (by omega) (by omega)
    omega
  obtain ⟨-, hah, -, -⟩ := hnl hcap
  obtain ⟨o1, o2⟩ := hsi.2.2.2 hcap
  simp only [win, outside_cons, outside_nil, and_true] at o1
  simp only [winA, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at g13
  unfold Apart at o2
  refine ⟨hst0, by rw [ewb]; unfold Apart; omega, hah.sub (by simp only [frP]; omega) (by simp only [frP, frN]; omega),
    ?_, by simp only [frP, frN]; unfold Apart; omega, free_ctx hpre hc hhd0 hstf, hgst,
    (free_ctx hpre hc (Or.inr g9) hgf.symm).symm⟩
  simp only [win, frP, frN, outside_cons, outside_nil, and_true]; omega

/-- a range of `buf` is apart from the stack's free part and the threshold globals (`OpX`) -/
theorem bufOp (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {a n : Nat} (h1 : bp ≤ a)
    (h2 : a + n ≤ bp + 8 * NB pl lm) : OpX M st a n := by
  intro hn
  obtain ⟨-, -, ⟨-, -, -, -, -, -, -, -, g9, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgf, -⟩ := id hpre
  obtain ⟨⟨-, -, -, -, -, hlc, -⟩, -, -⟩ := hc.sa
  refine ⟨?_, ?_⟩
  · rcases hc.bu with ⟨c1, c2⟩ | hap
    · simp only [frP, frN]; unfold Apart; omega
    · simp only [frP, frN]; unfold Apart at hap ⊢; omega
  · rcases hc.scr.loc with ⟨-, l1, l2⟩ | ⟨hin, -⟩
    · unfold Apart at hgf ⊢; omega
    · have := (hin.sub (a := a) (n := n) h1 (by omega)).apart g9; unfold Apart at this ⊢; omega

end

end FvModexp.Arm64.P2Pre
