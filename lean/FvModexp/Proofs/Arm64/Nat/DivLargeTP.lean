import FvModexp.Proofs.Arm64.Nat.DivLargeTN
import FvModexp.Proofs.Arm64.Nat.DivLargeG

set_option autoImplicit false

/-!
# `divLarge` (arm64): the postcondition from the facts at the return (pure)

`M` = the memory at `rJoin` (`AtR`), `Mf` = the final memory: `M` with the result slots (`SP - 88 … SP - 64`), the defer
bit (`SP - 201`), the deferred closure's frame and the stack header's `len` (restored by `stk.restore`) written.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

namespace FvModexp.Arm64.DivLarge

/-- the function's return relation: callee-saved registers and `Post` -/
@[reducible] def RQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat)
    (s s' : State) : Prop :=
  (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
    PostG R b L c zp zc st up uc ip il vp vl s s'

/-- the final frame list -/
@[reducible] def finW (s : State) (st : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - 328, s.sp.toNat - 312), (s.sp.toNat - 201, s.sp.toNat - 200), (s.sp.toNat - 88, s.sp.toNat - 64),
    (st + 8, st + 16)]

theorem natNorm_frame' {m m' : Memory} {p n : Nat} (h : NatNorm m p n)
    (hr : m'.readLE (p + 8 * (n - 1)) 8 = m.readLE (p + 8 * (n - 1)) 8) : NatNorm m' p n :=
  h.imp id (fun h => by rw [hr]; exact h)

theorem natLive_acc' {m m' : Memory} {R : RtInv} {L : List (Nat × Nat)} {p c : Nat} (h : NatLive m R L p c)
    (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) : NatLive m' R L p c := fun h0 => by
  obtain ⟨a, b, d, e⟩ := h h0; exact ⟨a, b, by rw [hacc]; exact d, e⟩

theorem out3_parts' {a n p q p' q' : Nat} {w k : List (Nat × Nat)} (h : Outside a n (w ++ [(p, q), (p', q')] ++ k)) :
    Outside a n w ∧ (a + n ≤ p ∨ q ≤ a) ∧ (a + n ≤ p' ∨ q' ≤ a) ∧ Outside a n k := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at h; exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem lpost {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {P C sh qp qc : Nat}
    {L2 : List (Nat × Nat)} {b2 w2 c2 ql : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {T : State}
    (hT : AtR R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 Lq P C sh qp qc L2 b2 w2 c2 ql T)
    {rl : Nat} (hrl : rl ≤ il + 1) (hrv : natVal T.mem P rl = natVal s.mem ip il % natVal s.mem vp vl)
    (hrn : NatNorm T.mem P rl) {Mf : Memory} (hW : MemFrame T.mem Mf (finW s st))
    (hlen : Mf.readLE (st + 8) 8 = stLen s.mem st) (s' : State) (hm : s'.mem = Mf)
    (h0 : s'.regs 0 = BitVec.ofNat 64 qp) (h1 : s'.regs 1 = BitVec.ofNat 64 ql) (h2 : s'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : s'.regs 3 = BitVec.ofNat 64 P) (h4 : s'.regs 4 = BitVec.ofNat 64 rl) (h5 : s'.regs 5 = BitVec.ofNat 64 C) :
    PostG R b L c zp zc st up uc ip il vp vl s s' := by
  subst hm
  have hl := hE.lay
  have hpre := hE.pre
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hU := hT.ua; have hQ := hT.qa
  have hcap := hU.cap; have hqcap := hQ.cap; have hql := hT.qle
  have hM := hT.mem.mem
  have hacc : ∀ a n w, s'.mem.accessible a n w = T.mem.accessible a n w := fun a n w => hW.accessible a n w
  -- reads at `Mf` of ranges outside the window and apart from `st + 8 … st + 16`
  have rdf : ∀ a n, (a + n ≤ s.sp.toNat - 41264 ∨ s.sp.toNat + 112 ≤ a) → (a + n ≤ st + 8 ∨ st + 16 ≤ a) →
      s'.mem.readLE a n = T.mem.readLE a n := fun a n h1 h2 =>
    hW.readLE a n (by simp only [finW, outside_cons, outside_nil, and_true]; omega)
  have hsw := hl.sw
  have hW2 : stW s'.mem st = w2 := by simp only [stW]; rw [rdf _ _ (by omega) (by omega)]; exact hM.hw
  have hC2 : stCap s'.mem st = c2 := by simp only [stCap]; rw [rdf _ _ (by omega) (by omega)]; exact hM.hcap
  have hlc := hpre.sti.1.2.2.2.2.2.1
  have hc2 := hT.c2len
  have hext : LiveExt R L L2 := hE.ext.trans (hT.ext3.trans hT.ext4)
  have hsth := hpre.sti.1.2.1
  refine ⟨qp, ql, qc, P, rl, C, h0, h1, h2, h3, h4, h5, L2, b2, ⟨?qv, ?qn, by omega, hQ.c40, ?qlive, ?qror⟩,
    ⟨?rv, ?rn, by omega, hU.c40, ?rlive, ?rror⟩, ⟨hext, hT.bud, ?inv⟩, ⟨⟨?stok, hlen, ?arr⟩, ?arrL⟩, ?fresh, ?fr, ?lf,
    fun _ _ => hQ.pu, ?qfresh⟩
  case qv =>
    rw [← hT.qval]; unfold natVal
    exact rdf _ _ (by have := hQ.pw; omega) (by have := hQ.ps; unfold Apart at this; omega)
  case qn => exact natNorm_frame' hT.qnrm (rdf _ _ (by have := hQ.pw; omega) (by have := hQ.ps; unfold Apart at this; omega))
  case qlive => exact fun _ => ⟨hQ.p8, hQ.pheld, by rw [hacc]; exact hQ.pacc, hQ.p48⟩
  case qror =>
    rcases hQ.ror with h | ⟨-, hin, hap⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hin, fun r hr => hap r (hE.ext.mem_old hr)⟩
  case rv =>
    rw [← hrv]; unfold natVal
    exact rdf _ _ (by have := hU.pw; omega) (by have := hU.ps; unfold Apart at this; omega)
  case rn => exact natNorm_frame' hrn (rdf _ _ (by have := hU.pw; omega) (by have := hU.ps; unfold Apart at this; omega))
  case rlive => exact fun _ => ⟨hU.p8, hT.ext4.held hU.pheld, by rw [hacc]; exact hU.pacc, hU.p48⟩
  case rror =>
    rcases hU.ror with h | ⟨-, hin, hap⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hin, fun r hr => hap r (hE.ext.mem_old hr)⟩
  case inv =>
    refine RtInv.inv_frame' hW (fun r hr => ?_) hM.inv
    have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hpre.ce.2.2.2.1
    simp only [finW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · simp only [show st + 16 - (st + 8) = 8 by omega]
      rcases hsth.sub (a := st + 8) (n := 8) (by omega) (by omega) with h | h
      · right; exact hext.inRanges_old h
      · left; exact h
  case stok =>
    unfold StkOK
    rw [hW2, hC2]
    refine ⟨hpre.sti.1.1, hext.held hsth, by rw [hacc, hM.fr.accessible]; exact hpre.sti.1.2.2.1, hpre.sti.1.2.2.2.1,
      natLive_acc' hT.live2 hacc, ?_, hT.c2b⟩
    show s'.mem.readLE (st + 8) 8 ≤ c2
    rw [hlen]; omega
  case arr =>
    rw [hW2, hC2]
    rcases hT.arr2 with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
    · rcases hE.arr with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact Or.inr ⟨hin, fun r hr => hap r (hT.ext3.mem_old (hE.ext.mem_old hr))⟩
  case arrL =>
    show ¬(stW s'.mem st = stW s.mem st ∧ stCap s'.mem st = stCap s.mem st) →
      (stW s'.mem st, stW s'.mem st + 8 * stCap s'.mem st) ∈ L2 ∧ 0 < stCap s'.mem st
    rw [hW2, hC2]
    intro hn
    by_cases h21 : w2 = w1 ∧ c2 = c1
    · obtain ⟨e1, e2⟩ := h21
      subst e1 e2
      obtain ⟨hm, hc⟩ := hE.arrL hn
      exact ⟨(hT.ext3.trans hT.ext4).mem_old hm, hc⟩
    · exact hT.arrL2 h21
  case fresh =>
    intro hne hC0 hc0
    rw [hW2, hC2]
    rcases hU.ror with h | ⟨-, hinP, hapP⟩
    · exact absurd h hne
    · rcases hT.arr2 with ⟨hw21, hc21⟩ | ⟨hin, hap⟩
      · rw [hw21, hc21]
        have hc0' : 0 < c1 := by have := hE.c1len; have := hl.v2; simp only [StackNat.rnd] at *; omega
        rcases (hE.w1live hc0').2.1 with hi | ho
        · obtain ⟨r, hr, i1, i2⟩ := hi; have := hapP r hr; unfold Apart at this ⊢; omega
        · have := outside_of_inRanges ho hinP; unfold Apart; omega
      · rcases hU.pheld with hi | ho
        · obtain ⟨r, hr, i1, i2⟩ := hi; have := hap r hr; unfold Apart at this ⊢; omega
        · have := outside_of_inRanges ho hin; unfold Apart; omega
  case qfresh =>
    intro hne hqc hc0
    rw [hC2] at hc0
    rw [hW2, hC2]
    rcases hQ.ror with h | ⟨-, hinQ, hapQ⟩
    · exact absurd h hne
    · rcases hT.arr2 with ⟨hw21, hc21⟩ | ⟨hin, hap⟩
      · rw [hw21, hc21]
        have hc0' : 0 < c1 := by omega
        rcases (hE.w1live hc0').2.1 with hi | ho
        · obtain ⟨r, hr, i1, i2⟩ := hi; have := hapQ r hr; unfold Apart at this ⊢; omega
        · have := outside_of_inRanges ho hinQ; unfold Apart; omega
      · rcases hT.qL with hi | ho
        · obtain ⟨r, hr, i1, i2⟩ := hi; have := hap r hr; unfold Apart at this ⊢; omega
        · have := outside_of_inRanges ho hin; unfold Apart; omega
  case fr =>
    refine (mfTrans hM.fr hW).mono fun a n ho => ?_
    simp only [outside_append] at ho
    obtain ⟨⟨⟨hrt, hwa⟩, hz, hu⟩, hst⟩ := ho
    have hst' := hst
    simp only [stkWs, outside_cons, outside_nil, and_true] at hst'
    rw [outside_append]
    refine ⟨?_, ?_⟩
    · rw [outside_append, outside_append, outside_append]
      refine ⟨⟨⟨hrt, hwa⟩, outside_wsL ?_ (ar_out hz) (ar_out hu)⟩, hst⟩
      rcases hE.scr.loc with ⟨-, i1, i2⟩ | ⟨hin, -⟩
      · omega
      · exact outside_of_inRanges hrt hin
    · have hwa' := hwa
      simp only [winA, outside_cons, outside_nil, and_true] at hwa'
      simp only [finW, outside_cons, outside_nil, and_true]; omega
  case lf =>
    refine ⟨fun a n hin ho => ?_⟩
    rw [outside_append] at ho
    have hst' := ho.2
    simp only [stkWs, outside_cons, outside_nil, and_true] at hst'
    have hz := ho.1
    rw [outside_append] at hz
    have hLs := hl.lsep
    obtain ⟨r, hr, i1, i2⟩ := hin
    have hrr := hLs r (hE.ext.mem_old hr)
    rw [hW.readLE a n (by simp only [finW, outside_cons, outside_nil, and_true]; omega)]
    refine hM.lf.readLE a n ⟨r, hr, i1, i2⟩ ?_
    rw [outside_append]
    refine ⟨outside_wsL ?_ (ar_out hz.1) (ar_out hz.2), ho.2⟩
    rcases hE.scr.loc with ⟨-, j1, j2⟩ | ⟨-, hap⟩
    · omega
    · have := hap r hr; unfold Apart at this; omega

end FvModexp.Arm64.DivLarge
