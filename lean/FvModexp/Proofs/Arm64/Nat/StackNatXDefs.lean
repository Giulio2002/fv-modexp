import FvModexp.Proofs.Arm64.Nat.StackNatDefs
import FvModexp.Proofs.Common.StackPot

set_option autoImplicit false

/-!
# `(*stack).nat(n)` (go-bigmodexpfix nat.go:319-329), arm64 — EXACT-budget and Q-form statements (divmc, TIGHT COSTS)

`StackNatDefs`' `Pre`/`PostL` charge every call the worst case `stackNatCost len n`. The exact forms:
* `PreX`: only a growth (`cap < len + nr`) needs budget, exactly `growslice`'s block `8 · growCap8 (len + nr) cap`;
* `PostXL`: no growth → `b ≤ b'`; growth → the new capacity is `growCap8 (len + nr) cap` and `b - 8 · cap' ≤ b'`.
The Q-form (Common/StackPot, NOTES-conventions "[divmc s34] TIGHT COSTS step 2") follows: `PreQ` (level bound
`len + n + 3 ≤ H`, budget `stkR H s.mem st ≤ b`), `PostQ` (`b - stkR H s.mem st + stkR H s'.mem st ≤ b'`), `HypQ`.
Both `Pre → PreX` and `PostXL → PostL` hold (`pre_of_pre`, `PostXL.toPostL`): the old statements are corollaries.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.StackNatX

open FvModexp.Arm64.StackNat (fn names wbA rnd Pre Post PostL)
open FvModexp.Arm64.RunIface (Serves)

/-- a growth's budget need -/
@[reducible] def GrowNeed (b len n c : Nat) : Prop := c < len + rnd n → 8 * growCap8 (len + rnd n) c ≤ b

/-- the exact budget step (`c, c'` the capacities before / after) -/
@[reducible] def BudX (b b' len n c c' : Nat) : Prop :=
  (len + rnd n ≤ c → b ≤ b') ∧ (c < len + rnd n → c' = growCap8 (len + rnd n) c ∧ b - 8 * c' ≤ b')

@[reducible] def PreX (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above st n : Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ StkOK s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8) ∧
    n ≤ 2 ^ 16 ∧ stLen s.mem st + n + 3 ≤ 2 ^ 16 ∧ GrowNeed b (stLen s.mem st) n (stCap s.mem st) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ s.mem.accessible wbA 4 false = true ∧ Apart st 24 wbA 4 ∧
    Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))

@[reducible] def PostXL (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above st n : Nat) (s s' : State) : Prop :=
  (0 < n → s'.regs 0 = BitVec.ofNat 64 (stW s'.mem st + 8 * stLen s.mem st)) ∧ s'.regs 1 = BitVec.ofNat 64 n ∧
    s'.regs 2 = BitVec.ofNat 64 n ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), (LiveExt R L L' ∧
      BudX b b' (stLen s.mem st) n (stCap s.mem st) (stCap s'.mem st) ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem)) ∧
      StkOK s'.mem R L' st ∧ stLen s'.mem st = stLen s.mem st + rnd n ∧
      (stLen s.mem st + rnd n ≤ stCap s.mem st → stW s'.mem st = stW s.mem st ∧ stCap s'.mem st = stCap s.mem st) ∧
      (stCap s.mem st < stLen s.mem st + rnd n → InRanges (stW s'.mem st) (8 * stCap s'.mem st) R.rt ∧
        ApartAll (stW s'.mem st) (8 * stCap s'.mem st) L) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ stkWs s.mem st) ∧ LiveFrame s.mem s'.mem L (stkWs s.mem st) ∧
      (stCap s.mem st < stLen s.mem st + rnd n → (stW s'.mem st, stW s'.mem st + 8 * stCap s'.mem st) ∈ L')

/-- **Q-form pre** (`H` bounds the level after the call; the reserve not held in the capacity is in the budget) -/
@[reducible] def PreQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H stk above st n : Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ StkOK s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8) ∧
    n ≤ 2 ^ 16 ∧ stLen s.mem st + n + 3 ≤ 2 ^ 16 ∧ (stLen s.mem st + n + 3 ≤ H ∧ stkR H s.mem st ≤ b) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ s.mem.accessible wbA 4 false = true ∧ Apart st 24 wbA 4 ∧
    Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))

/-- **Q-form post** (L form: a grown array is an element of the final live set) -/
@[reducible] def PostQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (H stk above st n : Nat) (s s' : State) : Prop :=
  (0 < n → s'.regs 0 = BitVec.ofNat 64 (stW s'.mem st + 8 * stLen s.mem st)) ∧ s'.regs 1 = BitVec.ofNat 64 n ∧
    s'.regs 2 = BitVec.ofNat 64 n ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), (LiveExt R L L' ∧ b - stkR H s.mem st + stkR H s'.mem st ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem)) ∧
      StkOK s'.mem R L' st ∧ stLen s'.mem st = stLen s.mem st + rnd n ∧
      (stLen s.mem st + rnd n ≤ stCap s.mem st → stW s'.mem st = stW s.mem st ∧ stCap s'.mem st = stCap s.mem st) ∧
      (stCap s.mem st < stLen s.mem st + rnd n → InRanges (stW s'.mem st) (8 * stCap s'.mem st) R.rt ∧
        ApartAll (stW s'.mem st) (8 * stCap s'.mem st) L) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ stkWs s.mem st) ∧ LiveFrame s.mem s'.mem L (stkWs s.mem st) ∧
      (stCap s.mem st < stLen s.mem st + rnd n → (stW s'.mem st, stW s'.mem st + 8 * stCap s'.mem st) ∈ L')

/-- the Q-form premise (callers take it; `ensQ` proves it) -/
def HypQ (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn) [st, n]
      (fun s => PreQ R b L H stk above st.toNat n.toNat s)
      (fun s s' => PostQ R b L H stk above st.toNat n.toNat s s')

/-! ## Bridges -/

theorem growNeed_of_cost {b len n c : Nat} (h : stackNatCost len n ≤ b) : GrowNeed b len n c := fun hc =>
  Nat.le_trans (growRound_le_cost len n c hc) h

theorem growNeed_of_q {b len n c H : Nat} (hH : len + n + 3 ≤ H) (h : stkRes H - potK * c ≤ b) :
    GrowNeed b len n c := fun hc => (grow_bud len n c H b hc hH h).1

theorem preX_of_pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above st n : Nat} {s : State}
    (h : Pre R b L stk above st n s) : PreX R b L stk above st n s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, growNeed_of_cost a8, a9, a10, a11, a12⟩

theorem preX_of_preQ {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H stk above st n : Nat} {s : State}
    (h : PreQ R b L H stk above st n s) : PreX R b L stk above st n s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, ⟨a8, a8'⟩, a9, a10, a11, a12⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, growNeed_of_q a8 (by unfold stkR at a8'; exact a8'), a9, a10, a11, a12⟩

theorem budX_cost {b b' len n c c' : Nat} (h : BudX b b' len n c c') : b - stackNatCost len n ≤ b' := by
  by_cases hk : len + rnd n ≤ c
  · have := h.1 hk; omega
  · obtain ⟨e, h2⟩ := h.2 (by omega)
    have := growRound_le_cost len n c (by simp only [rnd] at hk ⊢; omega)
    rw [e] at h2; simp only [rnd] at h2 this; omega

theorem budX_q {b b' len n c c' H : Nat} {m m' : Memory} {st : Nat} (hc : stCap m st = c) (hc' : stCap m' st = c')
    (hkeep : len + rnd n ≤ c → c' = c) (hH : len + n + 3 ≤ H) (hb : stkR H m st ≤ b) (h : BudX b b' len n c c') :
    b - stkR H m st + stkR H m' st ≤ b' := by
  rw [stkR_of_cap hc, stkR_of_cap hc'] at *
  by_cases hk : len + rnd n ≤ c
  · have := h.1 hk; rw [hkeep hk]; omega
  · obtain ⟨e, h2⟩ := h.2 (by omega)
    have := (grow_bud len n c H b (by simp only [rnd] at hk ⊢; omega) hH hb).2
    subst e; simp only [rnd] at h2 this ⊢; omega

theorem PostXL.toPostL {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk above st n : Nat} {s s' : State}
    (h : PostXL R b L stk above st n s s') : PostL R b L stk above st n s s' := by
  obtain ⟨h1, h2, h3, L', b', ⟨h4, h5, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, L', b', ⟨h4, budX_cost h5, h6⟩, h7⟩

theorem PostXL.toPostQ {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {H stk above st n : Nat} {s s' : State}
    (hH : stLen s.mem st + n + 3 ≤ H) (hb : stkR H s.mem st ≤ b)
    (h : PostXL R b L stk above st n s s') : PostQ R b L H stk above st n s s' := by
  obtain ⟨h1, h2, h3, L', b', ⟨h4, h5, h6⟩, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, L', b', ⟨h4, budX_q rfl rfl (fun hk => (h9 hk).2) hH hb h5, h6⟩, h7, h8, h9, h10⟩

end FvModexp.Arm64.StackNatX
