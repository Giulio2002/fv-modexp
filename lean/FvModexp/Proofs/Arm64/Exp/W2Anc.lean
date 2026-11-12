import FvModexp.Proofs.Arm64.Exp.W2Ctx

/-!
# window-2 (arm64): the anchor relation of the prologue (`Anc`)

`Anc R L0 sp K st M0 L M`: what changed between the anchor memory `M0` (live set `L0`; the memory after the inline
`stk.reserve`) and a later memory `M` of the window-2 prologue (live set `L`): the live set only grew, memory changed
only in the runtime's ranges, the frame window (except the caller's saved FP/LR at `[sp + 632, sp + 648)`), the stack
header and the stack's free part at `M0`; the stack only grew, and its array is the anchor's or a fresh one.
`Anc.step` moves it through any step whose `Keeps`/`KeepsB` facts are known (the function-level frame of window-2
is composed from it and the explicit frames of the posts after `divRet`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

/-- the free part of the stack's array at `M0` -/
@[reducible] def frA (st : Nat) (M0 : Memory) : Nat × Nat :=
  (stW M0 st + 8 * stLen M0 st, stW M0 st + 8 * stLen M0 st + 8 * (stCap M0 st - stLen M0 st))

/-- the ranges window-2's prologue may write (besides `R.rt`) -/
@[reducible] def aw (sp K st : Nat) (M0 : Memory) : List (Nat × Nat) :=
  [(sp - K, sp + 632), (sp + 648, sp + 752), (st, st + 24), frA st M0]

/-- the allocation cost of the prologue from `xJ` (stack level `l`) to `divRet` -/
abbrev xjBudA (n costD l : Nat) : Nat :=
  stackNatCost l (2 * n) + (makeCost (1 + 128 * n / 64 + 1) + (stackNatCost (l + StackNat.rnd (2 * n)) (2 * n) + costD))

/-- the allocation cost of path A of the `x` normalisation (then path B of the join) up to `divRet` -/
abbrev xnBudAB (n costD l k : Nat) : Nat :=
  stackNatCost l k + (stackNatCost (l + StackNat.rnd k) n + (costD +
    (stackNatCost (l + StackNat.rnd k + StackNat.rnd n) n +
      xjBudA n costD (l + StackNat.rnd k + StackNat.rnd n + StackNat.rnd n))))

/-- the allocation cost of path A of the `x` normalisation (then path C of the join) up to `divRet` -/
abbrev xnBudAA (n costD l k : Nat) : Nat :=
  stackNatCost l k + (stackNatCost (l + StackNat.rnd k) n + (costD + xjBudA n costD (l + StackNat.rnd k + StackNat.rnd n)))

/-- a bound of the allocation cost of every path of the prologue from `xnE` (stack level `l`, `k = len x - n + 1`)
up to `divRet` -/
abbrev xnPre (n costD l k : Nat) : Nat :=
  xjBudA n costD l + (stackNatCost l n + xjBudA n costD (l + StackNat.rnd n)) + xnBudAB n costD l k +
    xnBudAA n costD l k

theorem xnPre_ge1 (n costD l k : Nat) : xjBudA n costD l ≤ xnPre n costD l k := by unfold xnPre; omega
theorem xnPre_ge2 (n costD l k : Nat) :
    stackNatCost l n + xjBudA n costD (l + StackNat.rnd n) ≤ xnPre n costD l k := by unfold xnPre; omega
theorem xnPre_ge3 (n costD l k : Nat) : xnBudAB n costD l k ≤ xnPre n costD l k := by unfold xnPre; omega
theorem xnPre_ge4 (n costD l k : Nat) : xnBudAA n costD l k ≤ xnPre n costD l k := by unfold xnPre; omega

/-- the anchor relation (see the module doc) -/
@[reducible] def Anc (R : RtInv) (L0 : List (Nat × Nat)) (sp K st : Nat) (M0 : Memory) (L : List (Nat × Nat))
    (M : Memory) : Prop :=
  LiveExt R L0 L ∧ MemFrame M0 M (R.rt ++ aw sp K st M0) ∧ LiveFrame M0 M L0 [(st, st + 24), frA st M0] ∧
  stLen M0 st ≤ stLen M st ∧
  ((stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L0))

/-- a range the anchor relation allows a step to use as scratch (`ex` of `Obj`) -/
@[reducible] def ALoc (R : RtInv) (L0 : List (Nat × Nat)) (st : Nat) (M0 : Memory) (e : Nat × Nat) : Prop :=
  (stW M0 st + 8 * stLen M0 st ≤ e.1 ∧ e.1 + e.2 ≤ stW M0 st + 8 * stCap M0 st) ∨
    (InRanges e.1 e.2 R.rt ∧ ApartAll e.1 e.2 L0)

/-! small arithmetic steps (stated separately: `omega` in the steps' large contexts is very slow) -/
theorem ble1 {bA c b b' : Nat} (h1 : bA + c ≤ b) (h2 : b - c ≤ b') : bA ≤ b' := by omega
theorem ble2 {bA x y b b' : Nat} (h1 : bA + (x + y) ≤ b) (h2 : b - x ≤ b') : bA + y ≤ b' := by omega
theorem ble3 {bA x y z b b2 b4 : Nat} (h : bA + (x + (y + z)) ≤ b) (h2 : b - x ≤ b2) (h4 : b2 - y ≤ b4) :
    bA + z ≤ b4 := by omega
theorem le_cap_of {l r len cap : Nat} (h1 : len = l + r) (h2 : len ≤ cap) : l ≤ cap := by omega
theorem cap8 {l k r len cap : Nat} (h1 : len = l + r) (h2 : k ≤ r) (h3 : len ≤ cap) : 8 * l + 8 * k ≤ 8 * cap := by
  omega
theorem cap_of_in {W a b c : Nat} (h : W + a + b ≤ W + c) : a + b ≤ c := by omega
theorem le_drop {a r x y z c : Nat} (h : a + r + x + y + z ≤ c) : a + x + y + z ≤ c := by omega
theorem bP {s P Q b b1 : Nat} (hQ : Q ≤ P) (hbP : s + P ≤ b) (hb1 : b - s ≤ b1) : b1 - P + Q ≤ b1 := by omega

theorem Anc.refl (R : RtInv) (L0 : List (Nat × Nat)) (sp K st : Nat) (M0 : Memory) : Anc R L0 sp K st M0 L0 M0 :=
  ⟨LiveExt.refl R L0, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, LiveFrame.refl _ _ _, Nat.le_refl _,
    Or.inl ⟨rfl, rfl⟩⟩

theorem bytes_of_readLE {m m' : Memory} : ∀ {b k : Nat}, m'.readLE b k = m.readLE b k →
    ∀ i, i < k → m'.bytes (b + i) = m.bytes (b + i)
  | _, 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | b, k + 1, h, i, hi => by
    rw [Memory.readLE_succ, Memory.readLE_succ] at h
    have h1 := (m'.bytes b).isLt
    have h2 := (m.bytes b).isLt
    have hb : (m'.bytes b).toNat = (m.bytes b).toNat := by omega
    rcases i with _ | i
    · exact BitVec.eq_of_toNat_eq hb
    · have := bytes_of_readLE (m := m) (m' := m') (b := b + 1) (k := k) (by omega) i (by omega)
      rwa [show b + 1 + i = b + (i + 1) by omega] at this

/-- a read inside `[b, b + k)` is unchanged if the read of `[b, b + k)` is -/
theorem readLE_sub_eq {m m' : Memory} {a n b k : Nat} (h : m'.readLE b k = m.readLE b k) (h1 : b ≤ a)
    (h2 : a + n ≤ b + k) : m'.readLE a n = m.readLE a n :=
  Memory.readLE_congr fun i hi => by
    have := bytes_of_readLE h (a - b + i) (by omega)
    rwa [show b + (a - b + i) = a + i by omega] at this

theorem apart_of_inRanges_sep {L : List (Nat × Nat)} {lo hi a n : Nat} (hLs : LiveSep L [(lo, hi)])
    (h : InRanges a n L) (hlh : lo ≤ hi) : Apart a n lo (hi - lo) := by
  obtain ⟨r, hr, h1, h2⟩ := h
  have := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at this
  unfold Apart; omega

theorem apartAll_ext {R : RtInv} {L0 L : List (Nat × Nat)} {p k : Nat} (hx : LiveExt R L0 L) (h : ApartAll p k L) :
    ApartAll p k L0 := fun r hr => h r (hx.mem_old hr)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the anchor relation through one step** `M → M'` (live set `L → L'`), from the raw facts every `Keeps`/`KeepsB`
provides -/
theorem Anc.step {R : RtInv} {L0 L L' : List (Nat × Nat)} {sp K st l0 : Nat} {ex : List (Nat × Nat)}
    {M0 M M' : Memory} (hA : Anc R L0 sp K st M0 L M) (hx : LiveExt R L L')
    (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w)
    (hob : ∀ a k, Obj R L sp K st l0 ex M a k → M'.readLE a k = M.readLE a k)
    (h632 : M'.readLE (sp + 632) 8 = M.readLE (sp + 632) 8) (h640 : M'.readLE (sp + 640) 8 = M.readLE (sp + 640) 8)
    (hlen : stLen M st ≤ stLen M' st)
    (hst : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L))
    (hl0 : stLen M0 st ≤ l0) (hl0' : l0 ≤ stCap M st) (hex : ∀ e ∈ ex, ALoc R L0 st M0 e)
    (hLs : LiveSep L [(sp - K, sp + 752)]) (hK : K ≤ sp) :
    Anc R L0 sp K st M0 L' M' := by
  obtain ⟨hx0, hF, hLF, hl, hkf⟩ := hA
  -- `stUp M st l0` is inside the anchor's free part or a fresh array
  have hup : ∀ a k, (Outside a k R.rt ∨ InRanges a k L0) → Apart a k (stFree M0 st).1 (stFree M0 st).2 →
      Apart a k (stUp M st l0).1 (stUp M st l0).2 := by
    intro a k hh ha
    rcases hkf with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · simp only [stUp, stFree, stLen, stW, stCap] at e1 e2 hl0 hl0' ha ⊢; unfold Apart at ha ⊢
      rw [e1, e2]; omega
    · have := apart_held' hin hap hh.symm
      simp only [stUp, stCap, stW] at this hl0' ⊢; unfold Apart at this ⊢; omega
  have hexA : ∀ a k, (Outside a k R.rt ∨ InRanges a k L0) → Apart a k (stFree M0 st).1 (stFree M0 st).2 →
      ∀ e ∈ ex, Apart a k e.1 e.2 := by
    intro a k hh ha e he
    rcases hex e he with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · simp only [stFree] at ha; unfold Apart at ha ⊢; omega
    · exact apart_held' hin hap hh.symm
  refine ⟨hx0.trans hx, ?_, ?_, Nat.le_trans hl hlen, ?_⟩
  · refine MemFrame.trans hF ⟨fun a k ho => ?_, hacc⟩ fun _ _ h => ⟨h, h⟩
    simp only [aw, frA, outside_append, outside_cons, outside_nil, and_true] at ho
    obtain ⟨hrt, w1, w2, w3, w4⟩ := ho
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    by_cases hw : a + k ≤ sp - K ∨ sp + 752 ≤ a
    · refine hob a k ⟨Or.inr hrt, by unfold AW Apart; omega, by unfold Apart; omega,
        hup a k (Or.inl hrt) (by simp only [stFree] at w4 ⊢; unfold Apart; omega),
        hexA a k (Or.inl hrt) (by simp only [stFree] at w4 ⊢; unfold Apart; omega)⟩
    · have h16 : M'.readLE (sp + 632) 16 = M.readLE (sp + 632) 16 := by
        rw [Memory.readLE_sixteen, Memory.readLE_sixteen, h632, show sp + 632 + 8 = sp + 640 by omega, h640]
      exact readLE_sub_eq h16 (by omega) (by omega)
  · refine LiveFrame.trans hLF ⟨fun a k hin ho => ?_⟩ fun _ _ h => h
    simp only [frA, outside_cons, outside_nil, and_true] at ho
    obtain ⟨w3, w4⟩ := ho
    have hinL := hx0.inRanges_old hin
    have hw := apart_of_inRanges_sep hLs hinL (by omega)
    rw [show sp + 752 - (sp - K) = K + 752 by omega] at hw
    exact hob a k ⟨Or.inl hinL, hw, by unfold Apart; omega,
      hup a k (Or.inr hin) (by simp only [stFree] at w4 ⊢; unfold Apart; omega),
      hexA a k (Or.inr hin) (by simp only [stFree] at w4 ⊢; unfold Apart; omega)⟩
  · rcases hst with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · rw [e1, e2]; exact hkf
    · exact Or.inr ⟨hin, apartAll_ext hx0 hap⟩

/-- a stack nat above the anchor's length (in the anchor's array or in a fresh one) is an allowed scratch range -/
theorem aloc_of_anc {R : RtInv} {L0 L : List (Nat × Nat)} {sp K st l k : Nat} {M0 M : Memory}
    (hA : Anc R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l) (hk : 8 * l + k ≤ 8 * stCap M st) :
    ALoc R L0 st M0 (stW M st + 8 * l, k) := by
  rcases hA.2.2.2.2 with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · left; simp only [stW, stCap, stLen] at e1 e2 hl hk ⊢; rw [e1] at ⊢; rw [e2] at hk; omega
  · right
    refine ⟨hin.sub (by omega) (by omega), fun r hr => ?_⟩
    have := hap r hr; unfold Apart at this ⊢; omega

/-- `Anc` through a `Keeps` step -/
theorem Anc.keep {R : RtInv} {L0 L L' : List (Nat × Nat)} {g sp K st l0 : Nat} {ex : List (Nat × Nat)}
    {M0 M M' : Memory} (hA : Anc R L0 sp K st M0 L M) (hk : Keeps R L L' g sp K st l0 ex M M')
    (hl0 : stLen M0 st ≤ l0) (hl0' : l0 ≤ stCap M st) (hex : ∀ e ∈ ex, ALoc R L0 st M0 e)
    (hLs : LiveSep L [(sp - K, sp + 752)]) (hK : K ≤ sp) : Anc R L0 sp K st M0 L' M' :=
  Anc.step hA hk.1 hk.2.1 hk.2.2.2.1 (hk.2.2.2.2.1 632 (by omega)) (hk.2.2.2.2.1 640 (by omega))
    hk.2.2.2.2.2.2.2.2.2.1 hk.2.2.2.2.2.2.2.2.2.2.1 hl0 hl0' hex hLs hK

end FvModexp.Arm64.W2Pro
