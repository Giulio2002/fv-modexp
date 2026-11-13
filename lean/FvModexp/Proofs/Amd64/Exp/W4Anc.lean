import FvModexp.Proofs.Amd64.Exp.W4XnK
import FvModexp.Proofs.Amd64.Exp.W4ORDefs

set_option autoImplicit false

/-!
# window-4 (amd64): the anchor relation of the prologue (`Anc`) (agent expmc s56; twin of `Arm64.W4Anc`)

`Anc R L0 sp K st M0 L M`: what changed between the anchor memory `M0` (live set `L0`; the memory at the start of
the `Keeps`/`KeepsX` chain, after the inline `stk.reserve` and the entry spills) and a later memory `M` (live set `L`):
the live set only grew, memory changed only in the runtime's ranges, the frame window `[sp - 8 - K, sp + 0x3b0)`
(NOT the saved `BP`/return address `[sp + 0x3b0, sp + 0x3c0)`), the stack header and the stack's free part at `M0`;
the stack only grew, and its array is the anchor's or a fresh one.

This is the BRIDGE from the amd64 chain posts (which carry `Keeps`/`KeepsX` facts, no `Anc`) to the function-level
frame of window-4 (`MemFrame` over `R.rt ++ window ++ [z] ++ stkWs M0` and `LiveFrame` over `L0`): `Anc.keep` /
`Anc.keepX` move it through every `Keeps`/`KeepsX` step of a post, given that the step's level is at least the
anchor's stack length and its scratch ranges `ex` are stack nats above it or fresh (`ALoc`, `aloc_of_anc`).
The chain posts are NOT changed: `W4Fun` unfolds them layer by layer and applies `Anc.keep*` at each `Keeps`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

/-- the free part of the stack's array at `M0` -/
@[reducible] def frA (st : Nat) (M0 : Memory) : Nat × Nat :=
  (stW M0 st + 8 * stLen M0 st, stW M0 st + 8 * stLen M0 st + 8 * (stCap M0 st - stLen M0 st))

/-- the ranges window-4's prologue may write (besides `R.rt`) -/
@[reducible] def aw (sp K st : Nat) (M0 : Memory) : List (Nat × Nat) :=
  [(sp - 8 - K, sp + 0x3b0), (st, st + 24), frA st M0]

/-- the anchor relation (see the module doc) -/
@[reducible] def Anc (R : RtInv) (L0 : List (Nat × Nat)) (sp K st : Nat) (M0 : Memory) (L : List (Nat × Nat))
    (M : Memory) : Prop :=
  LiveExt R L0 L ∧ MemFrame M0 M (R.rt ++ aw sp K st M0) ∧ LiveFrame M0 M L0 [(st, st + 24), frA st M0] ∧
  stLen M0 st ≤ stLen M st ∧
  ((stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L0)) ∧
  ArrIn L st M0 M

/-- a range the anchor relation allows a step to use as scratch (`ex` of `Obj`) -/
@[reducible] def ALoc (R : RtInv) (L0 : List (Nat × Nat)) (st : Nat) (M0 : Memory) (e : Nat × Nat) : Prop :=
  (stW M0 st + 8 * stLen M0 st ≤ e.1 ∧ e.1 + e.2 ≤ stW M0 st + 8 * stCap M0 st) ∨
    (InRanges e.1 e.2 R.rt ∧ ApartAll e.1 e.2 L0)

theorem Anc.refl (R : RtInv) (L0 : List (Nat × Nat)) (sp K st : Nat) (M0 : Memory) : Anc R L0 sp K st M0 L0 M0 :=
  ⟨LiveExt.refl R L0, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, LiveFrame.refl _ _ _, Nat.le_refl _,
    Or.inl ⟨rfl, rfl⟩, fun h => absurd ⟨rfl, rfl⟩ h⟩

theorem bytes_of_readLE {m m' : Memory} : ∀ {b k : Nat}, m'.readLE b k = m.readLE b k →
    ∀ i, i < k → m'.bytes (b + i) = m.bytes (b + i)
  | _, 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | b, k + 1, h, i, hi => by
    rw [Arm64.Memory.readLE_succ, Arm64.Memory.readLE_succ] at h
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
  Arm64.Memory.readLE_congr fun i hi => by
    have := bytes_of_readLE h (a - b + i) (by omega)
    rwa [show b + (a - b + i) = a + i by omega] at this

theorem apart_of_inRanges_sep {L : List (Nat × Nat)} {lo hi a n : Nat} (hLs : LiveSep L [(lo, hi)])
    (h : InRanges a n L) (hlh : lo ≤ hi) : Apart a n lo (hi - lo) := by
  obtain ⟨r, hr, h1, h2⟩ := h
  have := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at this
  unfold Apart; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the anchor relation through one step** `M → M'` (live set `L → L'`), from the raw facts every `Keeps`/`KeepsX`
provides (`h3b0`/`h3b8`: the saved `BP` and the return address) -/
theorem Anc.step {R : RtInv} {L0 L L' : List (Nat × Nat)} {sp K st l0 : Nat} {ex : List (Nat × Nat)}
    {M0 M M' : Memory} (hA : Anc R L0 sp K st M0 L M) (hx : LiveExt R L L')
    (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w)
    (hob : ∀ a k, Obj R L sp K st l0 ex M a k → M'.readLE a k = M.readLE a k)
    (h3b0 : M'.readLE (sp + 0x3b0) 8 = M.readLE (sp + 0x3b0) 8)
    (h3b8 : M'.readLE (sp + 0x3b8) 8 = M.readLE (sp + 0x3b8) 8)
    (hlen : stLen M st ≤ stLen M' st)
    (hst : (stW M' st = stW M st ∧ stCap M' st = stCap M st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L))
    (hai : ArrIn L' st M M') (hl0 : stLen M0 st ≤ l0) (hl0' : l0 ≤ stCap M st) (hex : ∀ e ∈ ex, ALoc R L0 st M0 e)
    (hLs : LiveSep L [(sp - 8 - K, sp + 0x3c0)]) (hK : K + 8 ≤ sp) :
    Anc R L0 sp K st M0 L' M' := by
  obtain ⟨hx0, hF, hLF, hl, hkf, hai0⟩ := hA
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
  refine ⟨hx0.trans hx, ?_, ?_, Nat.le_trans hl hlen, ?_, ArrIn.trans hai0 hai hx⟩
  · refine MemFrame.trans hF ⟨fun a k ho => ?_, hacc⟩ fun _ _ h => ⟨h, h⟩
    simp only [aw, frA, outside_append, outside_cons, outside_nil, and_true] at ho
    obtain ⟨hrt, w1, w2, w4⟩ := ho
    have h16 : M'.readLE (sp + 0x3b0) 16 = M.readLE (sp + 0x3b0) 16 := by
      rw [Arm64.Memory.readLE_sixteen, Arm64.Memory.readLE_sixteen, h3b0, show sp + 0x3b0 + 8 = sp + 0x3b8 by omega,
        h3b8]
    refine Arm64.Memory.readLE_congr fun i hi => ?_
    by_cases hw : sp + 0x3b0 ≤ a + i ∧ a + i < sp + 0x3c0
    · have := bytes_of_readLE h16 (a + i - (sp + 0x3b0)) (by omega)
      rwa [show sp + 0x3b0 + (a + i - (sp + 0x3b0)) = a + i by omega] at this
    · have hrt1 : Outside (a + i) 1 R.rt := hrt.of_sub (by omega) (by omega)
      have := bytes_of_readLE (hob (a + i) 1 ⟨Or.inr hrt1, by unfold AW Apart; omega, by unfold Apart; omega,
        hup (a + i) 1 (Or.inl hrt1) (by simp only [stFree] at w4 ⊢; unfold Apart; omega),
        hexA (a + i) 1 (Or.inl hrt1) (by simp only [stFree] at w4 ⊢; unfold Apart; omega)⟩) 0 (by omega)
      rwa [Nat.add_zero] at this
  · refine LiveFrame.trans hLF ⟨fun a k hin ho => ?_⟩ fun _ _ h => h
    simp only [frA, outside_cons, outside_nil, and_true] at ho
    obtain ⟨w3, w4⟩ := ho
    have hinL := hx0.inRanges_old hin
    have hw := apart_of_inRanges_sep hLs hinL (by omega)
    rw [show sp + 0x3c0 - (sp - 8 - K) = K + 968 by omega] at hw
    exact hob a k ⟨Or.inl hinL, hw, by unfold Apart; omega,
      hup a k (Or.inr hin) (by simp only [stFree] at w4 ⊢; unfold Apart; omega),
      hexA a k (Or.inr hin) (by simp only [stFree] at w4 ⊢; unfold Apart; omega)⟩
  · rcases hst with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · rw [e1, e2]; exact hkf
    · exact Or.inr ⟨hin, apartAll_of_ext hx0 hap⟩

/-- a stack nat above the anchor's length (in the anchor's array or in a fresh one) is an allowed scratch range -/
theorem aloc_of_anc {R : RtInv} {L0 L : List (Nat × Nat)} {sp K st l k : Nat} {M0 M : Memory}
    (hA : Anc R L0 sp K st M0 L M) (hl : stLen M0 st ≤ l) (hk : 8 * l + k ≤ 8 * stCap M st) :
    ALoc R L0 st M0 (stW M st + 8 * l, k) := by
  rcases hA.2.2.2.2.1 with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · left; simp only [stW, stCap, stLen] at e1 e2 hl hk ⊢; rw [e1] at ⊢; rw [e2] at hk; omega
  · right
    refine ⟨hin.sub (by omega) (by omega), fun r hr => ?_⟩
    have := hap r hr; unfold Apart at this ⊢; omega

/-- `Anc` through a `Keeps` step -/
theorem Anc.keep {R : RtInv} {L0 L L' : List (Nat × Nat)} {g fs sp K st l0 : Nat} {ex : List (Nat × Nat)}
    {M0 M M' : Memory} (hA : Anc R L0 sp K st M0 L M) (hk : Keeps R L L' g fs sp K st l0 ex M M')
    (hl0 : stLen M0 st ≤ l0) (hl0' : l0 ≤ stCap M st) (hex : ∀ e ∈ ex, ALoc R L0 st M0 e)
    (hLs : LiveSep L [(sp - 8 - K, sp + 0x3c0)]) (hK : K + 8 ≤ sp) : Anc R L0 sp K st M0 L' M' := by
  obtain ⟨k1, k2, -, k4, k5, -, -, -, k9, k10, -, k12⟩ := hk
  exact Anc.step hA k1 k2 k4 (k5 0x3b0 (by simp only [KeptJ]; omega)) (k5 0x3b8 (by simp only [KeptJ]; omega))
    k9 k10 k12 hl0 hl0' hex hLs hK

/-- `Anc` through a `KeepsX` step -/
theorem Anc.keepX {R : RtInv} {L0 L L' : List (Nat × Nat)} {g fs sp K st l0 : Nat} {ex : List (Nat × Nat)}
    {M0 M M' : Memory} (hA : Anc R L0 sp K st M0 L M) (hk : KeepsX R L L' g fs sp K st l0 ex M M')
    (hl0 : stLen M0 st ≤ l0) (hl0' : l0 ≤ stCap M st) (hex : ∀ e ∈ ex, ALoc R L0 st M0 e)
    (hLs : LiveSep L [(sp - 8 - K, sp + 0x3c0)]) (hK : K + 8 ≤ sp) : Anc R L0 sp K st M0 L' M' := by
  obtain ⟨k1, k2, -, k4, k5, -, -, -, k9, k10, -, k12⟩ := hk
  exact Anc.step hA k1 k2 k4 (k5 0x3b0 (by simp only [KeptJX]; omega)) (k5 0x3b8 (by simp only [KeptJX]; omega))
    k9 k10 k12 hl0 hl0' hex hLs hK

/-- **the bridge at the function level**: the anchor relation gives the frame of window-4 over the anchor's ranges
(`R.rt`, the frame window incl. the saved `BP`/return address, the stack header and free part at `M0`) -/
theorem Anc.frame {R : RtInv} {L0 L : List (Nat × Nat)} {sp K st : Nat} {M0 M : Memory}
    (hA : Anc R L0 sp K st M0 L M) (hK : K + 8 ≤ sp) (hlc : stLen M0 st ≤ stCap M0 st) :
    MemFrame M0 M (R.rt ++ [(sp - 8 - K, sp + 0x3c0)] ++ stkWs M0 st) ∧
      LiveFrame M0 M L0 (stkWs M0 st) := by
  obtain ⟨-, hF, hLF, -, -, -⟩ := hA
  refine ⟨⟨fun a k ho => hF.readLE a k ?_, hF.accessible⟩, ⟨fun a k hin ho => hLF.readLE a k hin ?_⟩⟩
  · simp only [aw, frA, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := ho
    refine ⟨h1, by omega, h3, by omega⟩
  · simp only [frA, stkWs, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨ho.1, by omega⟩

end FvModexp.Amd64.W4Pro
