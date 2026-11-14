import FvModexp.Proofs.Amd64.Exp.NZM

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): pure post lemmas of the paths without a callee (agent expmc s72; twin of `Arm64.ExpN` NPost)

* `post_triv`: `z[:0]` returns (`m == 1`, or `x == 0` with `y ≠ 0`): value `0`;
* `post_oneA` / `post_oneB`: `z.setWord(1)` (`y == 0` or `x == 1`, `M > 1`): reuse / fresh `makeslice(1, 1)`.
Common helpers: `frame_post` (a frame inside the window → the `Post` frame), `stackBack_keep`, `resSep_keep`,
`val_triv`, `val_one`. Here `t = sp + 0x498` is the entry `RSP`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

theorem frame_post {R : RtInv} {K sp zp zc st : Nat} {s : State} {m : Memory} (hs : (s.regs 4).toNat = sp + 0x498)
    {ws : List (Nat × Nat)} (hF : MemFrame s.mem m (ws ++ wN sp K))
    (hws : ∀ a k, Outside a k (R.rt ++ [(zp, zp + 8 * zc)]) → Outside a k ws) :
    MemFrame s.mem m (R.rt ++ win s (K + 0x498) 0x78 ++ [(zp, zp + 8 * zc)] ++ ExpHyp.stWs s.mem st) :=
  hF.mono fun a k ho => by
    simp only [win, hs, outside_append, outside_cons, outside_nil, and_true] at ho
    rw [outside_append]
    refine ⟨hws a k (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho.1.1.1, ho.1.2⟩), ?_⟩
    have := ho.1.1.2
    simp only [wN, outside_cons, outside_nil, and_true]; omega

theorem stackBack_keep {R : RtInv} {L L' ws : List (Nat × Nat)} {st : Nat} {m m' : Memory}
    (hok : StkOK m R L st) (hx : LiveExt R L L') (hF : MemFrame m m' ws) (ho : Outside st 24 ws) :
    StackBackL R L L' st m m' := by
  obtain ⟨h1, ew, el, ec⟩ := FvModexp.stkOK_frame hok hF ho hx
  exact ⟨⟨h1, el, Or.inl ⟨ew, ec⟩⟩, fun hn => absurd ⟨ew, ec⟩ hn⟩

/-- a header-preserving frame keeps `ResSep` (the array is the entry one) -/
theorem resSep_keep {ws : List (Nat × Nat)} {st p c : Nat} {m m' : Memory} (hF : MemFrame m m' ws)
    (ho : Outside st 24 ws) : ResSep m m' st p c := by
  intro _ hn
  exact absurd ⟨hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega)), hF.readLE _ _ (ho.of_sub (by omega) (by omega))⟩ hn

/-- the `z[:0]` returns: value `0` (`M = 1`, or `X = 0 < Y`) -/
theorem val_triv {M : Memory} {xp xl yp yl mp n : Nat} (hyN : NatNorm M yp yl)
    (h : (n = 1 ∧ M.readLE mp 8 = 1) ∨ (yl ≠ 0 ∧ xl = 0)) :
    natVal M xp xl ^ natVal M yp yl % natVal M mp n = 0 := by
  rcases h with ⟨rfl, h⟩ | ⟨hy, rfl⟩
  · have e : natVal M mp 1 = 1 := h
    rw [e, Nat.mod_one]
  · have h1 := FvModexp.SubMod2N.natVal_lower M yp yl hyN (by omega)
    have hp : 0 < natVal M yp yl := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) h1
    have e0 : natVal M xp 0 = 0 := rfl
    rw [e0, Nat.zero_pow hp, Nat.zero_mod]

/-- the `z.setWord(1)` value: `X ^ Y % M = 1` when `Y = 0` or `X = 1` (and `M > 1`) -/
theorem val_one {M : Memory} {xp xl yp yl mp n : Nat} (hM : 1 < natVal M mp n)
    (h : yl = 0 ∨ (xl = 1 ∧ M.readLE xp 8 = 1)) :
    natVal M xp xl ^ natVal M yp yl % natVal M mp n = 1 := by
  rcases h with rfl | ⟨rfl, h⟩
  · have e0 : natVal M yp 0 = 0 := rfl
    rw [e0, Nat.pow_zero, Nat.mod_eq_of_lt hM]
  · have e : natVal M xp 1 = 1 := h
    rw [e, Nat.one_pow, Nat.mod_eq_of_lt hM]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the post of the `z[:0]` returns (`z` kept or nil'd by the alias test; only the window changed) -/
theorem post_triv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K costD : Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc st xp xl yp yl mp n zp' zc' : Nat} {s s' : State}
    (hs : (s.regs 4).toNat = sp + 0x498) (hK : K ≤ sp) (hLs : LiveSep L [(sp - K, sp + 0x510)])
    (hrw : Outside (sp - K) (K + 0x510) R.rt)
    (hsok : StkOK s.mem R L st) (hstw : Apart st 24 (sp - K) (K + 0x510))
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem))
    (hz : (zp' = zp ∧ zc' = zc ∧ NatLive s.mem R L zp zc) ∨ (zp' = 0 ∧ zc' = 0)) (hzc : zc < 2 ^ 40)
    (hzp : zp < 2 ^ 64)
    (hv : natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n = 0)
    (hF : MemFrame s.mem s'.mem (wN sp K))
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp') (h3 : s'.regs 3 = 0#64) (h1 : s'.regs 1 = BitVec.ofNat 64 zc')
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) :
    Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s s' := by
  have hx := LiveExt.refl R L
  have hso : Outside st 24 (wN sp K) := by
    simp only [wN, outside_cons, outside_nil, and_true]; unfold Apart at hstw; omega
  refine ⟨hfs, hdf, zp', 0, zc', h0, h3, h1, by rw [hv]; rfl, Or.inl rfl, Nat.zero_le _, ?_, L, b, hx, Nat.sub_le _ _,
    Expmc.inv_frame hF (fun r hr => Or.inr (wN_rt (rw_of hK hrw) r hr)) hinv, ?_, ?_, stackBack_keep hsok hx hF hso,
    frame_post (ws := []) hs hF (fun _ _ _ => trivial), LiveFrame.of_win hF (liveSep_wN hLs), resSep_keep hF hso⟩
  · rcases hz with ⟨e, rfl, -⟩ | ⟨e, rfl⟩ <;> exact ⟨by omega, by omega⟩
  · rcases hz with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl⟩
    · exact natLive_frame h hx hF
    · simp
  · rcases hz with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the post of `z.setWord(1)` reusing `z` (`0 < zc`, `z` kept by the alias test) -/
theorem post_oneA {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K costD : Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc st xp xl yp yl mp n : Nat} {s s' : State}
    (hs : (s.regs 4).toNat = sp + 0x498) (hK : K ≤ sp) (hLs : LiveSep L [(sp - K, sp + 0x510)])
    (hrw : Outside (sp - K) (K + 0x510) R.rt)
    (hsok : StkOK s.mem R L st) (hstw : Apart st 24 (sp - K) (K + 0x510))
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem))
    (hzc0 : 0 < zc) (hzc : zc < 2 ^ 40) (hzH : InRanges zp (8 * zc) L ∨ Outside zp (8 * zc) R.rt)
    (hzst : Apart zp (8 * zc) st 24) (hzL : NatLive s.mem R L zp zc)
    (hv : natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n = 1)
    (hF : MemFrame s.mem s'.mem ([(zp, zp + 8)] ++ wN sp K)) (hv1 : s'.mem.readLE zp 8 = 1)
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h3 : s'.regs 3 = 1#64) (h1 : s'.regs 1 = BitVec.ofNat 64 zc)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) :
    Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s s' := by
  have hx := LiveExt.refl R L
  have hso : Outside st 24 ([(zp, zp + 8)] ++ wN sp K) := by
    simp only [wN, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
    unfold Apart at hstw hzst; omega
  have hz8 : InRanges zp 8 L ∨ Outside zp 8 R.rt :=
    hzH.elim (fun h => Or.inl (h.sub (Nat.le_refl _) (by omega))) (fun h => Or.inr (h.of_sub (Nat.le_refl _) (by omega)))
  refine ⟨hfs, hdf, zp, 1, zc, h0, h3, h1, by rw [hv]; exact hv1,
    Or.inr (by simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; rw [hv1]; decide),
    hzc0, ⟨by omega, by have := (hzL hzc0).2.2.2; omega⟩, L, b, hx, Nat.sub_le _ _, Expmc.inv_frame hF ?_ hinv,
    natLive_frame hzL hx hF, Or.inr (Or.inl ⟨rfl, rfl⟩), stackBack_keep hsok hx hF hso, frame_post hs hF ?_,
    ⟨fun a k hin hout => hF.readLE a k ?_⟩, resSep_keep hF hso⟩
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [Nat.add_sub_cancel_left]; exact hz8
    · exact Or.inr (wN_rt (rw_of hK hrw) r hr)
  · intro a k ho
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  · have hw : Outside a k (wN sp K) := by
      obtain ⟨r, hr, e1, e2⟩ := hin
      exact Outside.of_sub (liveSep_wN hLs r hr) e1 (by omega)
    rw [outside_append] at hout ⊢
    refine ⟨?_, hw⟩
    have := hout.1
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the post of `z.setWord(1)` with a fresh `makeslice(Word, 1, 1)` block `[p, p + r)` (`z` empty) -/
theorem post_oneB {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K costD : Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc st xp xl yp yl mp n p r : Nat} {s s' : State} {M m : Memory}
    (hs : (s.regs 4).toNat = sp + 0x498) (hK : 41640 ≤ K) (hKs : K ≤ sp) (hLs : LiveSep L [(sp - K, sp + 0x510)])
    (hrw : Outside (sp - K) (K + 0x510) R.rt)
    (hsok : StkOK s.mem R L st) (hstw : Apart st 24 (sp - K) (K + 0x510))
    (hv : natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n = 1)
    (hF0 : MemFrame s.mem M (wN sp K))
    (hLF : LiveFrame M m L [])
    (hMF : MemFrame M m (R.rt ++ [(sp + 0x498 - 0x110 - 4096, sp + 0x498 - 0x110),
      (sp + 0x498 - 0x108, sp + 0x498 - 0x108 + 24), (sp + 0x498 - 0x110, sp + 0x498 - 0x108)]))
    (hAp : ApartAll p r L) (hIn : InRanges p r R.rt) (hp48 : p + r ≤ 2 ^ 48) (hacc : M.accessible p r true = true)
    (h8 : p % 8 = 0) (hr8 : 8 ≤ r) (hr : r = blockSize 8 true)
    (hinv : R.inv (b - r) (L ++ [(p, p + r)]) (s.regs 14).toNat (view R.rt (L ++ [(p, p + r)]) m))
    (hF2 : MemFrame m s'.mem [(p, p + 8), (sp + 0x498 - 0x58, sp + 0x498 - 0x40)]) (hv1 : s'.mem.readLE p 8 = 1)
    (h0 : s'.regs 0 = BitVec.ofNat 64 p) (h3 : s'.regs 3 = 1#64) (h1 : s'.regs 1 = 1#64)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) :
    Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s s' := by
  have hw := wN_rt (rw_of hKs hrw)
  have hwr : ∀ a k, Outside a k R.rt → a + k ≤ p ∨ p + 8 ≤ a := fun a k h => by
    have := out_inR2 h hIn; omega
  -- M → s'.mem over `R.rt ++ wN`
  have hM2 : MemFrame M s'.mem (R.rt ++ wN sp K) := hMF.trans hF2 fun a k ho => by
    have h1 := hwr a k (by rw [outside_append] at ho; exact ho.1)
    simp only [wN, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨⟨ho.1, by omega, by omega, by omega⟩, by omega, by omega⟩
  have hS : MemFrame s.mem s'.mem (R.rt ++ wN sp K) := hF0.trans hM2 fun a k ho => by
    rw [outside_append] at ho; exact ⟨ho.2, by rw [outside_append]; exact ho⟩
  have hx : LiveExt R L (L ++ [(p, p + r)]) := ⟨[(p, p + r)], rfl, fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; simp only [Nat.add_sub_cancel_left]; exact ⟨hIn, hAp⟩,
    List.pairwise_singleton _ _⟩
  have hin8 : InRanges p 8 (L ++ [(p, p + r)]) := ⟨(p, p + r), by simp, by simp only; omega, by simp only; omega⟩
  have hbl := blockSize_le_allocCost 8 true
  have e1 : makeCost 1 = allocCost 8 := rfl
  -- the stack header through the three steps
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hsok
  have hstO : Outside st 24 (wN sp K) := by
    simp only [wN, outside_cons, outside_nil, and_true]; unfold Apart at hstw; omega
  have rdst : ∀ o, o + 8 ≤ 24 → s'.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho => by
    rw [hF2.readLE _ _ (by
        have := apart_fresh k2 hAp hIn
        simp only [outside_cons, outside_nil, and_true]; unfold Apart at hstw; omega),
      rd_mk (k2.elim (fun h => Or.inl (h.sub (by omega) (by omega))) (fun h => Or.inr (h.of_sub (by omega) (by omega))))
        hLF hMF (by simp only [outside_cons, outside_nil, and_true]; unfold Apart at hstw; omega),
      hF0.readLE _ _ (hstO.of_sub (by omega) (by omega))]
  have ew : stW s'.mem st = stW s.mem st := by have := rdst 0 (by omega); simpa using this
  have el : stLen s'.mem st = stLen s.mem st := rdst 8 (by omega)
  have ec : stCap s'.mem st = stCap s.mem st := rdst 16 (by omega)
  have hacS : ∀ a k w, s'.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hF2.accessible, hMF.accessible, hF0.accessible]
  refine ⟨hfs, hdf, p, 1, 1, h0, h3, h1, by rw [hv]; exact hv1,
    Or.inr (by simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; rw [hv1]; decide), Nat.le_refl _,
    ⟨by decide, by omega⟩, L ++ [(p, p + r)], b - r, hx, by unfold NCost; omega, Expmc.inv_frame hF2 ?_ hinv, ?_, ?_,
    ?_, frame_post (ws := R.rt) hs hS (fun a k ho => by rw [outside_append] at ho; exact ho.1), ?_,
    fun _ hn => absurd ⟨ew, ec⟩ hn⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · left; simpa using hin8
    · right
      have := hw (sp - K, sp + 0x490) (List.mem_cons_self ..)
      simp only [List.mem_singleton] at hq; subst hq
      exact Outside.of_sub this (by simp only; omega) (by simp only; omega)
  · intro _
    refine ⟨h8, Or.inl (by simpa using hin8), ?_, by omega⟩
    rw [hF2.accessible, hMF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  · exact Or.inr (Or.inr ⟨by simpa using hIn.sub (Nat.le_refl _) (by omega),
      by simpa using ApartAll.sub' hAp (Nat.le_refl _) (by omega)⟩)
  · refine ⟨⟨⟨k1, k2.elim (fun h => Or.inl (hx.inRanges_old h)) Or.inr, by rw [hacS]; exact k3, k4, ?_,
      by rw [el, ec]; exact k6, by rw [ec]; exact k7⟩, el, Or.inl ⟨ew, ec⟩⟩, fun hn => absurd ⟨ew, ec⟩ hn⟩
    rw [ew, ec]; intro hc
    obtain ⟨a1, a2, a3, a4⟩ := k5 hc
    exact ⟨a1, a2.elim (fun h => Or.inl (hx.inRanges_old h)) Or.inr, by rw [hacS]; exact a3, a4⟩
  · refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨q, hq, e1, e2⟩ := hin
    have hq1 := liveSep_wN hLs q hq
    have hq2 := hAp q hq
    unfold Apart at hq2
    rw [hF2.readLE _ _ ?_, hLF.readLE a k ⟨q, hq, e1, e2⟩ trivial, hF0.readLE _ _ (Outside.of_sub hq1 e1 (by omega))]
    simp only [wN, outside_cons, outside_nil, and_true] at hq1 ⊢
    omega

end FvModexp.Amd64.ExpN
