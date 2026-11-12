import FvModexp.Proofs.Arm64.Exp.NDefs

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

end FvModexp.Arm64.EvenHyp
