import FvModexp.Proofs.Arm64.Exp.NDefs

set_option autoImplicit false

/-!
# `nat.expNNEven`'s premise on the two recursive `nat.expNN` calls (arm64; agent infra)

`ExpNNHypNE` is EXACTLY the conclusion of expmc's `ExpN.ens_noEven` (NFun.lean), the parameters universally quantified
except the fixed callee-shape ones: `nat.expNN` with a given stack, `slow = false`, `m` odd or a power of two, as an
`Ensures` on `nat.expNN`'s program `LibN` (= `ExpN.names`; it contains neither `nat.expNNEven` nor `(*Int).exp`, so a
return address inside `nat.expNNEven` is outside it). The caller (expmc's full `nat.expNN`) discharges it with
`fun b L … => ExpN.ens_noEven impl hap R H hRem hnsR hn11R hKR b L …`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.EvenHyp

def ExpNNHypNE (impl : List Segment) (R : RtInv) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat),
    Ensures ((Extracted.program.onlySegments ExpN.names).link impl) (segAddr Extracted.program ExpN.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc, BitVec.ofNat 64 slow]
      (ExpN.Pre R b L K costF needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow)
      (ExpN.Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n)

/-- `ExpNNHypNE` with the fact `ExpN.Post` does not state (true of the code, nat.go:639-722): the result capacity is
below `2^40` (a fresh result comes from `nat.make`). An EMPTY result may be `nil` (`p = 0`) even for a located `z`
(`expNNSlow`: the remainder `nil.setWord(0)`; NOTES-conventions "[infra s30] FINDING"), so nothing is claimed about it.
LOCAL WRAPPER (infra s29/s30) until expmc exports the lemma (coordinator RESOLUTION). -/
def ExpNNHypNE0 (impl : List Segment) (R : RtInv) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat),
    Ensures ((Extracted.program.onlySegments ExpN.names).link impl) (segAddr Extracted.program ExpN.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc, BitVec.ofNat 64 slow]
      (ExpN.Pre R b L K costF needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow)
      (fun s s' => ExpN.Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s' ∧
        (s'.regs 2).toNat < 2 ^ 40)

/-- `ExpNNHypNE0` + the LOCATION of an empty result (as a register value): `0`, or a runtime pointer apart from the
call's live set. `ExpN.Post`'s disjunct `(c = 0 ∧ p = 0) ∨ (p = zp ∧ c = zc) ∨ (fresh)` gives it for `p` once `ExpN.Post`
bounds `p < 2^64` (always true of the code: `p` is `X0`); REQUEST to expmc "[infra s33]". LOCAL WRAPPER until then. -/
def ExpNNHypNE1 (impl : List Segment) (R : RtInv) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat),
    Ensures ((Extracted.program.onlySegments ExpN.names).link impl) (segAddr Extracted.program ExpN.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc, BitVec.ofNat 64 slow]
      (ExpN.Pre R b L K costF needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow)
      (fun s s' => ExpN.Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s' ∧
        (s'.regs 2).toNat < 2 ^ 40 ∧
        ((s'.regs 2).toNat = 0 → 0 < zc → (s'.regs 0).toNat = 0 ∨
          (InRanges (s'.regs 0).toNat 0 R.rt ∧ ApartAll (s'.regs 0).toNat 0 L)))

/-- the empty-result location from `ExpN.Post` when its pointer is a register value (`p < 2^64`) -/
theorem ExpNNHypNE1.loc_of {R : RtInv} {L : List (Nat × Nat)} {zp zc p c : Nat} {s' : State}
    (h0 : s'.regs 0 = BitVec.ofNat 64 p) (h2 : s'.regs 2 = BitVec.ofNat 64 c) (hp : p < 2 ^ 64) (hc : c < 2 ^ 40)
    (hres : (c = 0 ∧ p = 0) ∨ (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) :
    (s'.regs 2).toNat = 0 → 0 < zc → (s'.regs 0).toNat = 0 ∨
      (InRanges (s'.regs 0).toNat 0 R.rt ∧ ApartAll (s'.regs 0).toNat 0 L) := by
  intro e2 hz
  rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at e2
  subst e2
  rw [h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  rcases hres with ⟨-, e⟩ | ⟨-, e⟩ | h
  · exact Or.inl e
  · omega
  · exact Or.inr h

end FvModexp.Arm64.EvenHyp
