import FvModexp.Proofs.Arm64.Exp.NNilD
import FvModexp.Proofs.Arm64.Exp.NPost

/-!
# `nat.expNN` (arm64), `stk == nil`: the posts of the paths without a callee (no stack is ever taken)

`postN_triv` / `postN_oneA` / `postN_oneB`: `NPost.post_triv` / `post_oneA` / `post_oneB` stated with `PostNil` (no
stack facts; the budget bound of `PostNil` is weaker). `frame_postN`: `frame_post` without the stack's ranges.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

theorem frame_postN {R : RtInv} {K sp zp zc : Nat} {s : State} {m : Memory} (hs : s.sp.toNat = sp + 1312)
    {ws : List (Nat × Nat)} (hF : MemFrame s.mem m (ws ++ wN sp K))
    (hws : ∀ a k, Outside a k (R.rt ++ [(zp, zp + 8 * zc)]) → Outside a k ws) :
    MemFrame s.mem m (R.rt ++ winA s (K + 1312) 120 ++ [(zp, zp + 8 * zc)]) :=
  hF.mono fun a k ho => by
    simp only [winA, hs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    refine ⟨hws a k (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho.1.1, ho.2⟩),
      by omega, by omega⟩

set_option maxRecDepth 20000 in
theorem postN_triv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc xp xl yp yl mp n zp' zc' : Nat} {s s' : State}
    (hs : s.sp.toNat = sp + 1312) (hLs : LiveSep L [(sp - K, sp + 1432)]) (hrw : LiveSep [(sp - K, sp + 1432)] R.rt)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem))
    (hz : (zp' = zp ∧ zc' = zc ∧ NatLive s.mem R L zp zc) ∨ (zp' = 0 ∧ zc' = 0)) (hzc : zc < 2 ^ 40)
    (hv : natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n = 0)
    (hF : MemFrame s.mem s'.mem (wN sp K))
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp') (h1 : s'.regs 1 = 0#64) (h2 : s'.regs 2 = BitVec.ofNat 64 zc') :
    PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s' := by
  have hx := LiveExt.refl R L
  refine ⟨zp', 0, zc', h0, h1, h2, by rw [hv]; rfl, Or.inl rfl, Nat.zero_le _, ?_, L, b, hx, Nat.sub_le _ _,
    Expmc.inv_frame hF (fun r hr => Or.inr (out_rt_wN hrw r hr)) hinv, ?_, ?_,
    frame_postN (ws := []) hs hF (fun _ _ _ => trivial), LiveFrame.of_win hF (liveSep_wN hLs)⟩
  · rcases hz with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> omega
  · rcases hz with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl⟩
    · exact natLive_frame h hx hF
    · simp
  · rcases hz with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩

set_option maxRecDepth 20000 in
theorem postN_oneA {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc xp xl yp yl mp n : Nat} {s s' : State}
    (hs : s.sp.toNat = sp + 1312) (hLs : LiveSep L [(sp - K, sp + 1432)]) (hrw : LiveSep [(sp - K, sp + 1432)] R.rt)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem))
    (hzc0 : 0 < zc) (hzc : zc < 2 ^ 40) (hzH : InRanges zp (8 * zc) L ∨ Outside zp (8 * zc) R.rt)
    (hzL : NatLive s.mem R L zp zc)
    (hv : natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n = 1)
    (hF : MemFrame s.mem s'.mem ([(zp, zp + 8)] ++ wN sp K)) (hv1 : s'.mem.readLE zp 8 = 1)
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 1 = 1#64) (h2 : s'.regs 2 = BitVec.ofNat 64 zc) :
    PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s' := by
  have hx := LiveExt.refl R L
  have hz8 : InRanges zp 8 L ∨ Outside zp 8 R.rt :=
    hzH.elim (fun h => Or.inl (h.sub (Nat.le_refl _) (by omega))) (fun h => Or.inr (h.of_sub (Nat.le_refl _) (by omega)))
  refine ⟨zp, 1, zc, h0, h1, h2, by rw [hv]; exact hv1,
    Or.inr (by simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; rw [hv1]; decide),
    hzc0, by omega, L, b, hx, Nat.sub_le _ _, Expmc.inv_frame hF ?_ hinv, natLive_frame hzL hx hF,
    Or.inr (Or.inl ⟨rfl, rfl⟩), frame_postN hs hF ?_, ⟨fun a k hin hout => hF.readLE a k ?_⟩⟩
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [Nat.add_sub_cancel_left]; exact hz8
    · exact Or.inr (out_rt_wN hrw r hr)
  · intro a k ho
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  · have hw : Outside a k (wN sp K) := by
      obtain ⟨r, hr, e1, e2⟩ := hin
      exact Outside.of_sub (liveSep_wN hLs r hr) e1 (by omega)
    rw [outside_append]
    refine ⟨?_, hw⟩
    simp only [outside_cons, outside_nil, and_true] at hout ⊢
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem postN_oneB {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc xp xl yp yl mp n p r : Nat} {s s' : State} {M m : Memory}
    (hs : s.sp.toNat = sp + 1312) (hK : 4304 ≤ K) (hLs : LiveSep L [(sp - K, sp + 1432)])
    (hrw : LiveSep [(sp - K, sp + 1432)] R.rt)
    (hv : natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n = 1)
    (hF0 : MemFrame s.mem M (wN sp K))
    (hLF : LiveFrame M m L []) (hMF : MemFrame M m (R.rt ++ [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1088)]))
    (hAp : ApartAll p r L) (hIn : InRanges p r R.rt) (hp48 : p + r ≤ 2 ^ 48) (hacc : M.accessible p r true = true)
    (h8 : p % 8 = 0) (hr8 : 8 ≤ r) (hr : r = blockSize 8 true)
    (hinv : R.inv (b - r) (L ++ [(p, p + r)]) (s.regs 28).toNat (view R.rt (L ++ [(p, p + r)]) m))
    (hF2 : MemFrame m s'.mem [(p, p + 8), (sp + 1232, sp + 1256)]) (hv1 : s'.mem.readLE p 8 = 1)
    (h0 : s'.regs 0 = BitVec.ofNat 64 p) (h1 : s'.regs 1 = 1#64) (h2 : s'.regs 2 = 1#64) :
    PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s' := by
  have hw := out_rt_wN hrw
  have hwr : ∀ a k, Outside a k R.rt → a + k ≤ p ∨ p + 8 ≤ a := fun a k h => by
    have := out_inR2 h hIn; omega
  have hM2 : MemFrame M s'.mem (R.rt ++ wN sp K) := hMF.trans hF2 fun a k ho => by
    have h1 := hwr a k (by rw [outside_append] at ho; exact ho.1)
    simp only [wN, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨⟨ho.1, by omega, by omega⟩, by omega, by omega⟩
  have hS : MemFrame s.mem s'.mem (R.rt ++ wN sp K) := hF0.trans hM2 fun a k ho => by
    rw [outside_append] at ho; exact ⟨ho.2, by rw [outside_append]; exact ho⟩
  have hx : LiveExt R L (L ++ [(p, p + r)]) := ⟨[(p, p + r)], rfl, fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; simp only [Nat.add_sub_cancel_left]; exact ⟨hIn, hAp⟩,
    List.pairwise_singleton _ _⟩
  have hin8 : InRanges p 8 (L ++ [(p, p + r)]) := ⟨(p, p + r), by simp, by simp only; omega, by simp only; omega⟩
  have hbl := blockSize_le_allocCost 8 true
  have e1 : makeCost 1 = allocCost 8 := rfl
  refine ⟨p, 1, 1, h0, h1, h2, by rw [hv]; exact hv1,
    Or.inr (by simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; rw [hv1]; decide), Nat.le_refl _, by decide,
    L ++ [(p, p + r)], b - r, hx, by unfold NCost; omega, Expmc.inv_frame hF2 ?_ hinv, ?_, ?_,
    frame_postN (ws := R.rt) hs hS (fun a k ho => by rw [outside_append] at ho; exact ho.1), ?_⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · left; simpa using hin8
    · right
      have := hw (sp - K, sp + 1304) (List.mem_cons_self ..)
      simp only [List.mem_singleton] at hq; subst hq
      exact Outside.of_sub this (by simp only; omega) (by simp only; omega)
  · intro _
    refine ⟨h8, Or.inl (by simpa using hin8), ?_, by omega⟩
    rw [hF2.accessible, hMF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)
  · exact Or.inr (Or.inr ⟨by simpa using hIn.sub (Nat.le_refl _) (by omega),
      by simpa using ApartAll.sub' hAp (Nat.le_refl _) (by omega)⟩)
  · refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨q, hq, e1, e2⟩ := hin
    have hq1 := liveSep_wN hLs q hq
    have hq2 := hAp q hq
    unfold Apart at hq2
    rw [hF2.readLE _ _ ?_, hLF.readLE a k ⟨q, hq, e1, e2⟩ trivial, hF0.readLE _ _ (Outside.of_sub hq1 e1 (by omega))]
    simp only [wN, outside_cons, outside_nil, and_true] at hq1 ⊢
    omega

end FvModexp.Arm64.ExpN
