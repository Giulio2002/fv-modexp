import FvModexp.Proofs.Arm64.Exp.NDefs
import FvModexp.Proofs.Common.ExpmcFrame
import FvModexp.Proofs.Common.SubMod2NMath

/-!
# `nat.expNN` (arm64): pure post lemmas of the paths without a callee

* `post_triv`: `z[:0]` returns (`m == 1`, or `x == 0` with `y ≠ 0`): value `0`;
* `post_oneA` / `post_oneB`: `z.setWord(1)` (`y == 0` or `x == 1`, `M > 1`): reuse / fresh `makeslice(1, 1)`.
Common helpers: `frame_post` (window frame → the `Post` frame), `liveSep_post`, `stackBack_keep`, `natLive_frame`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

/-- the window `[sp - K, sp + 1432)` without the caller's saved FP/LR words `[sp + 1304, sp + 1320)` -/
@[reducible] def wN (sp K : Nat) : List (Nat × Nat) := [(sp - K, sp + 1304), (sp + 1320, sp + 1432)]

theorem frame_post {R : RtInv} {K sp zp zc st : Nat} {s : State} {m : Memory} (hs : s.sp.toNat = sp + 1312)
    {ws : List (Nat × Nat)} (hF : MemFrame s.mem m (ws ++ wN sp K))
    (hws : ∀ a k, Outside a k (R.rt ++ [(zp, zp + 8 * zc)]) → Outside a k ws) :
    MemFrame s.mem m (R.rt ++ winA s (K + 1312) 120 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) :=
  hF.mono fun a k ho => by
    simp only [winA, hs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    refine ⟨hws a k (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho.1.1.1, ho.1.2⟩),
      by omega, by omega⟩

theorem liveSep_wN {L : List (Nat × Nat)} {sp K : Nat} (h : LiveSep L [(sp - K, sp + 1432)]) : LiveSep L (wN sp K) :=
  fun r hr => by
    have := h r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega

theorem out_rt_wN {R : RtInv} {sp K : Nat} (h : LiveSep [(sp - K, sp + 1432)] R.rt) :
    ∀ r ∈ wN sp K, Outside r.1 (r.2 - r.1) R.rt := by
  have h0 := h _ (List.mem_singleton_self _)
  intro r hr
  simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Outside.of_sub h0 (by simp only; omega) (by simp only; omega)
  · exact Outside.of_sub h0 (by simp only; omega) (by simp only; omega)

theorem stackBack_keep {R : RtInv} {L L' ws : List (Nat × Nat)} {st : Nat} {m m' : Memory}
    (hok : StkOK m R L st) (hx : LiveExt R L L') (hF : MemFrame m m' ws) (ho : Outside st 24 ws) :
    StackBack R L L' st m m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hok
  have ew : stW m' st = stW m st := hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega))
  have el : stLen m' st = stLen m st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have ec : stCap m' st = stCap m st := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  refine ⟨⟨h1, h2.elim (fun h => Or.inl (hx.inRanges_old h)) Or.inr, by rw [hF.accessible]; exact h3, h4, ?_,
    by rw [el, ec]; exact h6, by rw [ec]; exact h7⟩, el, Or.inl ⟨ew, ec⟩⟩
  rw [ew, ec]; intro hc
  obtain ⟨a1, a2, a3, a4⟩ := h5 hc
  exact ⟨a1, a2.elim (fun h => Or.inl (hx.inRanges_old h)) Or.inr, by rw [hF.accessible]; exact a3, a4⟩

theorem natLive_frame {R : RtInv} {L L' ws : List (Nat × Nat)} {p c : Nat} {m m' : Memory}
    (h : NatLive m R L p c) (hx : LiveExt R L L') (hF : MemFrame m m' ws) : NatLive m' R L' p c := by
  intro hc
  obtain ⟨a1, a2, a3, a4⟩ := h hc
  exact ⟨a1, a2.elim (fun h => Or.inl (hx.inRanges_old h)) Or.inr, by rw [hF.accessible]; exact a3, a4⟩

/-- `M > 1` from `¬(len m = 1 ∧ m[0] = 1)`, `m` normalised and nonempty -/
theorem m_gt1 {M : Memory} {mp n : Nat} (hn : 0 < n) (hN : NatNorm M mp n) (h1 : ¬(n = 1 ∧ M.readLE mp 8 = 1)) :
    1 < natVal M mp n := by
  by_cases hn1 : n = 1
  · subst hn1
    rcases hN with h | h
    · omega
    · simp only [natVal, Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h ⊢
      have : M.readLE mp 8 ≠ 1 := fun e => h1 ⟨rfl, e⟩
      omega
  · have := FvModexp.SubMod2N.natVal_lower M mp n hN hn
    have h2 : 2 ^ 64 ≤ 2 ^ (64 * (n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

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

/-- the post of the `z[:0]` returns (`z` kept or nil'd by the alias test; only the window changed) -/
theorem post_triv {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc st xp xl yp yl mp n zp' zc' : Nat} {s s' : State}
    (hs : s.sp.toNat = sp + 1312) (hLs : LiveSep L [(sp - K, sp + 1432)]) (hrw : LiveSep [(sp - K, sp + 1432)] R.rt)
    (hsok : StkOK s.mem R L st) (hstw : Apart st 24 (sp - K) (K + 1432))
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem))
    (hz : (zp' = zp ∧ zc' = zc ∧ NatLive s.mem R L zp zc) ∨ (zp' = 0 ∧ zc' = 0)) (hzc : zc < 2 ^ 40)
    (hv : natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n = 0)
    (hF : MemFrame s.mem s'.mem (wN sp K))
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp') (h1 : s'.regs 1 = 0#64) (h2 : s'.regs 2 = BitVec.ofNat 64 zc') :
    Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s' := by
  have hx := LiveExt.refl R L
  have hso : Outside st 24 (wN sp K) := by
    simp only [wN, outside_cons, outside_nil, and_true]; unfold Apart at hstw; omega
  refine ⟨zp', 0, zc', h0, h1, h2, by rw [hv]; rfl, Or.inl rfl, Nat.zero_le _, ?_, L, b, hx, Nat.sub_le _ _,
    Expmc.inv_frame hF (fun r hr => Or.inr (out_rt_wN hrw r hr)) hinv, ?_, ?_, stackBack_keep hsok hx hF hso,
    frame_post (ws := []) hs hF (fun _ _ _ => trivial), LiveFrame.of_win hF (liveSep_wN hLs)⟩
  · rcases hz with ⟨-, rfl, -⟩ | ⟨-, rfl⟩ <;> omega
  · rcases hz with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl⟩
    · exact natLive_frame h hx hF
    · simp
  · rcases hz with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl rfl

/-- the `z.setWord(1)` value: `X ^ Y % M = 1` when `Y = 0` or `X = 1` (and `M > 1`) -/
theorem val_one {M : Memory} {xp xl yp yl mp n : Nat} (hM : 1 < natVal M mp n)
    (h : yl = 0 ∨ (xl = 1 ∧ M.readLE xp 8 = 1)) :
    natVal M xp xl ^ natVal M yp yl % natVal M mp n = 1 := by
  rcases h with rfl | ⟨rfl, h⟩
  · have e0 : natVal M yp 0 = 0 := rfl
    rw [e0, Nat.pow_zero, Nat.mod_eq_of_lt hM]
  · have e : natVal M xp 1 = 1 := h
    rw [e, Nat.one_pow, Nat.mod_eq_of_lt hM]

/-- the post of `z.setWord(1)` reusing `z` (`0 < zc`, `z` kept by the alias test) -/
theorem post_oneA {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc st xp xl yp yl mp n : Nat} {s s' : State}
    (hs : s.sp.toNat = sp + 1312) (hLs : LiveSep L [(sp - K, sp + 1432)]) (hrw : LiveSep [(sp - K, sp + 1432)] R.rt)
    (hsok : StkOK s.mem R L st) (hstw : Apart st 24 (sp - K) (K + 1432))
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem))
    (hzc0 : 0 < zc) (hzc : zc < 2 ^ 40) (hzH : InRanges zp (8 * zc) L ∨ Outside zp (8 * zc) R.rt)
    (hzst : Apart zp (8 * zc) st 24) (hzL : NatLive s.mem R L zp zc)
    (hv : natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n = 1)
    (hF : MemFrame s.mem s'.mem ([(zp, zp + 8)] ++ wN sp K)) (hv1 : s'.mem.readLE zp 8 = 1)
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 1 = 1#64) (h2 : s'.regs 2 = BitVec.ofNat 64 zc) :
    Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s' := by
  have hx := LiveExt.refl R L
  have hso : Outside st 24 ([(zp, zp + 8)] ++ wN sp K) := by
    simp only [wN, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
    unfold Apart at hstw hzst; omega
  have hz8 : InRanges zp 8 L ∨ Outside zp 8 R.rt :=
    hzH.elim (fun h => Or.inl (h.sub (Nat.le_refl _) (by omega))) (fun h => Or.inr (h.of_sub (Nat.le_refl _) (by omega)))
  refine ⟨zp, 1, zc, h0, h1, h2, by rw [hv]; exact hv1, Or.inr (by simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; rw [hv1]; decide),
    hzc0, by omega, L, b, hx, Nat.sub_le _ _, Expmc.inv_frame hF ?_ hinv, natLive_frame hzL hx hF,
    Or.inr (Or.inl ⟨rfl, rfl⟩), stackBack_keep hsok hx hF hso, frame_post hs hF ?_, ⟨fun a k hin hout => hF.readLE a k ?_⟩⟩
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
    rw [outside_append] at hout ⊢
    refine ⟨?_, hw⟩
    have := hout.1
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega

end FvModexp.Arm64.ExpN
