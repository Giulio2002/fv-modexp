import FvModexp.Proofs.Amd64.Exp.NRemP
import FvModexp.Proofs.Common.SubMod2NMath

/-!
# `nat.expNN` (amd64): the result of `z = z.make(len m)` (nat.go:694) as a callee-entry context `ZM` (agent expmc s71;
twin of `Arm64.ExpN.ZM` / `zm_keep` / `zm_fresh` in Arm64/Exp/NMkP)

`ZM … s0 M L1 b1 zq zcq mk`: the memory `M` at a dispatch point is framed from the entry memory `s0` over
`R.rt ++ wN`, the live set is `L1 ⊇ L`, the budget `b1 ≥ b - mk` with `mk ≤ makeCost n`, and `z'' = (zq, zcq)`
(`n ≤ zcq`) satisfies the callee `z` facts `ZQ` (at `M`, `L1`) and `ZArg` (old `z` or a fresh block).
`zm_keep`: `n ≤ cap z'` (reuse; `z'` = the entry `z` kept by the alias test); `zm_fresh`: a `makeslice` block (the
call's frame `R.rt ++ ws` with `ws` inside `wN`). Value lemmas `val_mod2`, `val_pos`, `val_two`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Amd64.ExpN

/-- the callee-entry context after the make -/
@[reducible] def ZM (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g fs sp K zp zc st xp xl yp yl mp n : Nat)
    (s0 M : Memory) (L1 : List (Nat × Nat)) (b1 zq zcq mk : Nat) : Prop :=
  MemFrame s0 M (R.rt ++ wN sp K) ∧ LiveFrame s0 M L [] ∧ M.regions = s0.regions ∧
  LiveExt R L L1 ∧ b - mk ≤ b1 ∧ mk ≤ makeCost n ∧ R.inv b1 L1 g (view R.rt L1 M) ∧
  ZQ R L1 g fs sp K st xp xl yp yl mp n M zq zcq ∧ ZArg R L sp K zp zc zq zcq ∧ n ≤ zcq ∧ zq < 2 ^ 64

theorem val_mod2 {M : Memory} {mp n : Nat} (hn : 0 < n) : natVal M mp n % 2 = M.readLE mp 8 % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1 + k := ⟨n - 1, by omega⟩
  rw [FvModexp.natVal_add]
  have e : natVal M mp 1 = M.readLE mp 8 := rfl
  rw [e, show 2 ^ (64 * 1) = 2 * 2 ^ 63 by decide, Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem val_pos {M : Memory} {p l : Nat} (hN : NatNorm M p l) (hl : l ≠ 0) : 0 < natVal M p l :=
  Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (FvModexp.SubMod2N.natVal_lower M p l hN (by omega))

theorem val_two {M : Memory} {p l : Nat} (hN : NatNorm M p l) (hl : l ≠ 0) (h1 : ¬(l = 1 ∧ M.readLE p 8 = 1)) :
    2 ≤ natVal M p l := by
  by_cases e1 : l = 1
  · subst e1
    have e : natVal M p 1 = M.readLE p 8 := rfl
    rcases hN with h | h
    · omega
    · simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at h
      rw [e]
      rcases Nat.lt_or_ge (M.readLE p 8) 2 with hc | hc
      · exact absurd ⟨rfl, by omega⟩ h1
      · exact hc
  · have := FvModexp.SubMod2N.natVal_lower M p l hN (by omega)
    have h2 : 2 ^ 1 ≤ 2 ^ (64 * (l - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem apart_fresh {R : RtInv} {L : List (Nat × Nat)} {a n p r : Nat} (hH : InRanges a n L ∨ Outside a n R.rt)
    (hAp : ApartAll p r L) (hIn : InRanges p r R.rt) : a + n ≤ p ∨ p + r ≤ a := by
  rcases hH with ⟨q, hq, h1, h2⟩ | ho
  · have := hAp q hq; unfold Apart at this; omega
  · exact out_inR2 ho hIn

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- reuse: `z'` (the entry `z` kept by the alias test) has `n ≤ cap` -/
theorem zm_keep {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow zp' zc' : Nat} {s : State} {M : Memory}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hF1 : MemFrame s.mem M (wN sp K)) (hLF : LiveFrame s.mem M L []) (hrg : M.regions = s.mem.regions)
    (hz : (zp' = zp ∧ zc' = zc ∧ (0 < zc → ZOK R L g fs sp K st zp zc xp xc yp yl mp n s.mem)) ∨ (zp' = 0 ∧ zc' = 0))
    (hn : n ≤ zc') :
    ZM R b L g fs sp K zp zc st xp xl yp yl mp n s.mem M L b zp' zc' 0 := by
  obtain ⟨⟨-, -, -, -, -, -, -, hce, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hxlc, -, hzp, -, hzc, -, -, -, -, -, hsok, hstw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinv, -⟩ := hP
  obtain ⟨-, hK0, -, -, -, -, -, hwrt, -⟩ := hce
  have hF : MemFrame s.mem M (R.rt ++ wN sp K) := hF1.mono fun a k ho => by rw [outside_append] at ho; exact ho.2
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → M.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF hF (by unfold Apart at hstw ⊢; omega)
  have ew : stW M st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen M st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap M st = stCap s.mem st := rdh 16 (by omega)
  obtain ⟨hZQ, hZA⟩ := zq_keep (L1 := L) (xl := xl) hzc (LiveExt.refl R L) hxlc hF.accessible ew el ec hz
  refine ⟨hF, hLF, hrg, LiveExt.refl R L, by omega, by omega,
    Expmc.inv_frame hF1 (fun r hr => Or.inr (wN_rt (rw_of hK0 hwrt) r hr)) hinv, hZQ, hZA, hn, ?_⟩
  rcases hz with ⟨rfl, -, -⟩ | ⟨rfl, -⟩ <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- a fresh `makeslice(Word, n, makeCap n)` block `[p, p + r)` (memory `M` before the call, `m` after; the call's
frame `R.rt ++ ws`, `ws` inside `wN sp K`) -/
theorem zm_fresh {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow p r : Nat} {s : State} {M m : Memory}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hF : MemFrame s.mem M (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M L []) (hrg : M.regions = s.mem.regions)
    (hLF' : LiveFrame M m L []) {ws : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ ws))
    (hws : ∀ a k, Outside a k (wN sp K) → Outside a k ws)
    (hrg' : m.regions = M.regions) (hAp : ApartAll p r L) (hIn : InRanges p r R.rt) (hp48 : p + r ≤ 2 ^ 48)
    (hacc : M.accessible p r true = true) (h8 : p % 8 = 0) (hr8 : 8 * makeCap n ≤ r)
    (hr : r = blockSize (8 * makeCap n) true)
    (hinv : R.inv (b - r) (L ++ [(p, p + r)]) g (view R.rt (L ++ [(p, p + r)]) m)) :
    ZM R b L g fs sp K zp zc st xp xl yp yl mp n s.mem m (L ++ [(p, p + r)]) (b - r) p (makeCap n) r := by
  obtain ⟨⟨-, -, -, -, -, -, -, hce, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, hn128, -, -, hmO, -, -, -,
    hyO, -, -, -, -, -, hxO, -, -, -, -, hxlc, -, -, -, -, -, hgO, -, -, -, hsok, hstw, -, -, -, hc0, -⟩ := hP
  obtain ⟨-, hK0, -, -, -, -, -, hwrt, -, hgrt, -, -, -, -, -, -, -, f5, -⟩ := hce
  have hmc : n ≤ makeCap n ∧ makeCap n ≤ n + 4 := by unfold makeCap; split <;> omega
  have hx : LiveExt R L (L ++ [(p, p + r)]) := ⟨[(p, p + r)], rfl, fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; simp only [Nat.add_sub_cancel_left]; exact ⟨hIn, hAp⟩,
    List.pairwise_singleton _ _⟩
  have hIn' : InRanges p (8 * makeCap n) R.rt := hIn.sub (Nat.le_refl _) (by omega)
  have hAp' : ApartAll p (8 * makeCap n) L := ApartAll.sub' hAp (Nat.le_refl _) (by omega)
  have hF2 : MemFrame s.mem m (R.rt ++ wN sp K) := hF.trans hMF fun a k ho => ⟨ho, by
    rw [outside_append] at ho ⊢; exact ⟨ho.1, hws a k ho.2⟩⟩
  have hLF2 : LiveFrame s.mem m L [] := hLF.trans hLF' fun _ _ h => h
  -- the stack header at `m`
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → m.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF2 hF2 (by unfold Apart at hstw ⊢; omega)
  have ew : stW m st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen m st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap m st = stCap s.mem st := rdh 16 (by omega)
  have af : ∀ {a k : Nat}, (InRanges a k L ∨ Outside a k R.rt) → Apart p (8 * makeCap n) a k := fun h => by
    have := apart_fresh h hAp' hIn'; unfold Apart; omega
  have hacc' : m.accessible p (8 * makeCap n) true = true := by
    rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have hin1 : InRanges p (8 * makeCap n) (L ++ [(p, p + r)]) := ⟨(p, p + r), by simp, by simp only; omega,
    by simp only; omega⟩
  refine ⟨hF2, hLF2, hrg'.trans hrg, hx, by omega, ?_, hinv, ⟨by omega, fun _ => ⟨h8, Or.inl hin1, hacc', by omega⟩,
    fun _ => ⟨?_, ?_, ?_, af hH, ?_, af hgO.1, ?_, af hyO.1, af hmO.1⟩⟩,
    Or.inr (Or.inr ⟨hIn', hAp'⟩), hmc.1, by omega⟩
  · rw [hr]; exact blockSize_le_allocCost _ _
  · have := out_inR2 hwrt hIn'; unfold Apart; omega
  · have := out_inR2 hgrt hIn'; unfold Apart; omega
  · have := out_inR2 f5 hIn'; unfold Apart; omega
  · show Apart p (8 * makeCap n) (stW m st + 8 * stLen m st) (8 * (stCap m st - stLen m st))
    rw [ew, el, ec]
    rcases Nat.eq_zero_or_pos (stCap s.mem st) with h0 | h0
    · rw [hc0 h0, h0]; unfold Apart; omega
    · obtain ⟨-, hA, -, -⟩ := hsok.2.2.2.2.1 h0
      have := af hA; have := hsok.2.2.2.2.2.1; unfold Apart at *; omega
  · have := af hxO.1; unfold Apart at this ⊢; omega

end FvModexp.Amd64.ExpN
