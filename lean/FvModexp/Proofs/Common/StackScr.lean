import FvModexp.Proofs.Common.Conv

/-!
# Scratch nats from `(*stack).nat` (ISA independent)

The `*stack` object: a header `(w, len, cap)` at `st` (`stW`, `stLen`, `stCap`; definitionally the same reads as agent
expmc's `ExpHyp.stW/stLen/stCap`). `StkOK` = expmc's `StackOK'` (top's `stackOK`).

`Scr R L L1 m0 m st t k`: after `t = stk.nat(k)` (entry memory `m0`, live set `L` at the call, `L1` after it, memory `m`),
the `k` words at `t` are an aligned, writable, held object of `L1`, and they are either inside the free part of the
stack array of `m0` or a fresh runtime block apart from everything in `L`. Consequence `Scr.apart`: they are apart from
every object held in `L` that is apart from the old free part.

`StackBack R L L1 st m0 m`: the stack after a function that used it as scratch and restored it: `StkOK`, same `len`, and
the array is the old one or a fresh block apart from `L` (so the caller's next `stk.nat` result is apart from the
caller's objects). NOTE: no claim on the VALUE of the used part `[w, w + 8 len)`: a callee whose output nat lives in that
part (karatsubaSqr's `z1 = stk.nat(…)` passed to `sqr`) writes it through its own pointer, and if `stk.nat` grew the
array in between, the stack's copy of that part is stale. Callers read their nats through their own pointers.
-/

namespace FvModexp

open Janus Janus.Arm64 Janus.Contracts

@[reducible] def stW (m : Memory) (st : Nat) : Nat := m.readLE st 8
@[reducible] def stLen (m : Memory) (st : Nat) : Nat := m.readLE (st + 8) 8
@[reducible] def stCap (m : Memory) (st : Nat) : Nat := m.readLE (st + 16) 8

/-- = agent expmc's `ExpHyp.StackOK'` -/
@[reducible] def StkOK (m : Memory) (R : RtInv) (L : List (Nat × Nat)) (st : Nat) : Prop :=
  st % 8 = 0 ∧ Held R L st 24 ∧ m.accessible st 24 true = true ∧ st + 24 ≤ 2 ^ 48 ∧
    NatLive m R L (stW m st) (stCap m st) ∧ stLen m st ≤ stCap m st ∧ stCap m st < 2 ^ 40

/-- the ranges a stack user may write: the header and the free part of the array (= expmc's `stWs`) -/
@[reducible] def stkWs (m : Memory) (st : Nat) : List (Nat × Nat) :=
  [(st, st + 24), (stW m st + 8 * stLen m st, stW m st + 8 * stCap m st)]

/-- the stack after a scratch user (see the module doc) -/
@[reducible] def StackBack (R : RtInv) (L L1 : List (Nat × Nat)) (st : Nat) (m0 m : Memory) : Prop :=
  StkOK m R L1 st ∧ stLen m st = stLen m0 st ∧
    ((stW m st = stW m0 st ∧ stCap m st = stCap m0 st) ∨
      (InRanges (stW m st) (8 * stCap m st) R.rt ∧ ApartAll (stW m st) (8 * stCap m st) L))

/-- the stack's array of `m` is that of `m0`, or (fresh) an exact element of `L1` with a POSITIVE capacity
(`StackBackL`'s second half). The `0 < cap` half (coordinator decision on "[expmc s25] PROPOSAL"): a grown array is
never empty, so the pool shape's `cap = 0 → ptr = 0` (`StkSh`) is re-established at the `sync.(*Pool).Put`. -/
@[reducible] def ArrIn (L1 : List (Nat × Nat)) (st : Nat) (m0 m : Memory) : Prop :=
  ¬(stW m st = stW m0 st ∧ stCap m st = stCap m0 st) →
    (stW m st, stW m st + 8 * stCap m st) ∈ L1 ∧ 0 < stCap m st

/-- `StackBack` plus (coordinator's STACK-IN-LIVE-SET DECISION): when the stack's array is not the entry one, its range
is an exact element of the final live set (needed by `sync.(*Pool).Put` of the `stk == nil` path) and not empty -/
@[reducible] def StackBackL (R : RtInv) (L L1 : List (Nat × Nat)) (st : Nat) (m0 m : Memory) : Prop :=
  StackBack R L L1 st m0 m ∧ ArrIn L1 st m0 m

theorem StackBackL.toStackBack {R : RtInv} {L L1 : List (Nat × Nat)} {st : Nat} {m0 m : Memory}
    (h : StackBackL R L L1 st m0 m) : StackBack R L L1 st m0 m := h.1

/-- the s15 second half of `StackBackL` (membership only) -/
theorem ArrIn.mem {L1 : List (Nat × Nat)} {st : Nat} {m0 m : Memory} (h : ArrIn L1 st m0 m)
    (hn : ¬(stW m st = stW m0 st ∧ stCap m st = stCap m0 st)) : (stW m st, stW m st + 8 * stCap m st) ∈ L1 :=
  (h hn).1

theorem ArrIn.cap {L1 : List (Nat × Nat)} {st : Nat} {m0 m : Memory} (h : ArrIn L1 st m0 m)
    (hn : ¬(stW m st = stW m0 st ∧ stCap m st = stCap m0 st)) : 0 < stCap m st :=
  (h hn).2

/-- the pool-shape fact `cap = 0 → ptr = 0` survives a stack user (`ArrIn`) -/
theorem ArrIn.cap0 {L1 : List (Nat × Nat)} {st : Nat} {m0 m : Memory} (h : ArrIn L1 st m0 m)
    (h0 : stCap m0 st = 0 → stW m0 st = 0) : stCap m st = 0 → stW m st = 0 := by
  intro hc
  by_cases hs : stW m st = stW m0 st ∧ stCap m st = stCap m0 st
  · rw [hs.1]; exact h0 (by rw [← hs.2]; exact hc)
  · have := h.cap hs; omega

/-- `ArrIn` after `(*stack).nat` (the `PostL` shape: same array when it fits, else a member of `L1`): a grown array
has `cap ≥ len = len0 + r > cap0 ≥ 0` -/
theorem ArrIn.of_nat {L1 : List (Nat × Nat)} {st len0 r : Nat} {m0 m : Memory}
    (hlc : stLen m st ≤ stCap m st) (hlen : stLen m st = len0 + r)
    (hsame : len0 + r ≤ stCap m0 st → stW m st = stW m0 st ∧ stCap m st = stCap m0 st)
    (hmem : stCap m0 st < len0 + r → (stW m st, stW m st + 8 * stCap m st) ∈ L1) :
    ArrIn L1 st m0 m := by
  intro hn
  by_cases hc : len0 + r ≤ stCap m0 st
  · exact absurd (hsame hc) hn
  · exact ⟨hmem (by omega), by omega⟩

/-- `StackBack` with the array kept is `StackBackL` -/
theorem StackBack.toL {R : RtInv} {L L1 : List (Nat × Nat)} {st : Nat} {m0 m : Memory}
    (h : StackBack R L L1 st m0 m) (hs : stW m st = stW m0 st ∧ stCap m st = stCap m0 st) :
    StackBackL R L L1 st m0 m := ⟨h, fun hn => absurd hs hn⟩

/-- `ArrIn` composes along a callee that brought the stack back in the L form -/
theorem ArrIn.trans {R : RtInv} {L L' : List (Nat × Nat)} {st : Nat} {m0 m m' : Memory}
    (h : ArrIn L st m0 m) (hb : ArrIn L' st m m') (he : LiveExt R L L') : ArrIn L' st m0 m' := by
  intro hn
  by_cases hs : stW m' st = stW m st ∧ stCap m' st = stCap m st
  · rw [hs.1, hs.2] at hn ⊢; exact ⟨he.mem_old (h hn).1, (h hn).2⟩
  · exact hb hs

/-- `ArrIn` survives frames that keep the header -/
theorem ArrIn.congr {L L' : List (Nat × Nat)} {st : Nat} {m0 m m' : Memory}
    (h : ArrIn L st m0 m) (hw : stW m' st = stW m st) (hc : stCap m' st = stCap m st) (hL : ∀ r ∈ L, r ∈ L') :
    ArrIn L' st m0 m' := by
  intro hn; rw [hw, hc] at hn ⊢; exact ⟨hL _ (h hn).1, (h hn).2⟩

/-- a scratch nat of `k > 0` words at `t` (see the module doc) -/
structure Scr (R : RtInv) (L L1 : List (Nat × Nat)) (m0 m : Memory) (st t k : Nat) : Prop where
  b48 : t + 8 * k ≤ 2 ^ 48
  acc : m.accessible t (8 * k) true = true
  al : t % 8 = 0
  held : Held R L1 t (8 * k)
  loc : (0 < stCap m0 st ∧ stW m0 st + 8 * stLen m0 st ≤ t ∧ t + 8 * k ≤ stW m0 st + 8 * stCap m0 st) ∨
    (InRanges t (8 * k) R.rt ∧ ApartAll t (8 * k) L)

theorem ApartAll.sub' {a n b k : Nat} {L : List (Nat × Nat)} (h : ApartAll b k L) (h1 : b ≤ a) (h2 : a + n ≤ b + k) :
    ApartAll a n L := fun r hr => by have := h r hr; unfold Apart at *; omega

/-- A scratch nat is apart from every object held in `L` and apart from the old free part. -/
theorem Scr.apart {R : RtInv} {L L1 : List (Nat × Nat)} {m0 m : Memory} {st t k p n : Nat}
    (h : Scr R L L1 m0 m st t k) (hp : Held R L p n)
    (hf : 0 < stCap m0 st → Apart p n (stW m0 st + 8 * stLen m0 st) (8 * (stCap m0 st - stLen m0 st))) :
    Apart t (8 * k) p n := by
  rcases h.loc with ⟨h0, h1, h2⟩ | ⟨hin, hap⟩
  · have hf := hf h0; unfold Apart at hf ⊢; omega
  · rcases hp with hpL | hpO
    · exact hap.apart_of_inRanges hpL
    · exact (hin.apart hpO).symm

/-- A scratch nat is outside every range list that is outside `R.rt` and outside the old free part. -/
theorem Scr.outside {R : RtInv} {L L1 : List (Nat × Nat)} {m0 m : Memory} {st t k : Nat} {rs : List (Nat × Nat)}
    (h : Scr R L L1 m0 m st t k) (hrt : ∀ r ∈ rs, Outside r.1 (r.2 - r.1) R.rt)
    (hf : ∀ r ∈ rs, 0 < stCap m0 st → Apart r.1 (r.2 - r.1) (stW m0 st + 8 * stLen m0 st) (8 * (stCap m0 st - stLen m0 st))) :
    Outside t (8 * k) rs := by
  induction rs with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨lo, hi⟩ := r
    simp only [outside_cons]
    refine ⟨?_, ih (fun r hr => hrt r (List.mem_cons_of_mem _ hr)) (fun r hr => hf r (List.mem_cons_of_mem _ hr))⟩
    have e := h.apart (p := lo) (n := hi - lo) (Or.inr (hrt (lo, hi) List.mem_cons_self))
      (hf (lo, hi) List.mem_cons_self)
    unfold Apart at e; omega

/-- `Scr` from `(*stack).nat`'s postcondition (expmc's `StackNatPost` shape). -/
theorem Scr.of_post {R : RtInv} {L L1 : List (Nat × Nat)} {m0 m : Memory} {st len0 k : Nat}
    (hok : StkOK m R L1 st) (hlen : stLen m st = len0 + (k + 3) / 4 * 4) (hk : 0 < k)
    (hsame : len0 + (k + 3) / 4 * 4 ≤ stCap m0 st → stW m st = stW m0 st ∧ stCap m st = stCap m0 st)
    (hgrow : stCap m0 st < len0 + (k + 3) / 4 * 4 → InRanges (stW m st) (8 * stCap m st) R.rt ∧
      ApartAll (stW m st) (8 * stCap m st) L)
    (hl0 : len0 = stLen m0 st) :
    Scr R L L1 m0 m st (stW m st + 8 * len0) k := by
  obtain ⟨-, -, -, -, hnl, hlc, -⟩ := hok
  have hcap : len0 + k ≤ stCap m st := by omega
  obtain ⟨hal, hh, hacc, h48⟩ := hnl (by omega)
  refine ⟨by omega, Memory.accessible_mono _ hacc (by omega) (by omega), by omega, hh.sub (by omega) (by omega), ?_⟩
  by_cases hc : len0 + (k + 3) / 4 * 4 ≤ stCap m0 st
  · obtain ⟨e1, e2⟩ := hsame hc
    left; subst hl0; refine ⟨by omega, by omega, by omega⟩
  · obtain ⟨hin, hap⟩ := hgrow (by omega)
    right; exact ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩

end FvModexp
