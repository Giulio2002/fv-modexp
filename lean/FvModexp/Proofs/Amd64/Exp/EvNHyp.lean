import FvModexp.Proofs.Amd64.Exp.NDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the premise for its two `expNN` calls (asm s56; twin of infra's arm64 `EvenNHyp.ExpNNHypNE1`)

`z1.expNN(stk, x, y, m1, false)` (`m1 = 2^n`) and `z2.expNN(stk, x, y, m2, false)` (`m2` odd) run the odd / power-of-two
branches of `nat.expNN` only, so the callee is expmc's amd64 `ExpN` summary (statement `ExpN.Pre`/`ExpN.Post`, NDefs) on
the program `ExpN.names` (= `LibN`, which leaves out `nat.expNNEven`: NESTED-PROGRAM RULE, no recursion in the proof).
Arguments: registers `[z, zl, zc, st, x, xl, xc, slow]` (RAX RBX RCX RDI RSI R8 R9 R10), `y`/`m` as stack words read by
`ExpN.NPre`. Unlike arm64 no extra result conjuncts are needed: amd64 `ExpN.PostG` already states `c < 2^40`,
`p < 2^64` and the result location.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.EvenHyp

/-- the `expNN` premise of `nat.expNNEven`'s two calls (expmc's amd64 `ExpN` export shape) -/
def ExpNNHypNE1 (impl : List Amd64.Segment) (R : RtInv) (K : Nat) (costF : Nat → Nat → Nat → Nat) (costD : Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat),
    Ensures ((Extracted.program.onlySegments ExpN.names).link impl) (segAddr Extracted.program ExpN.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 slow]
      (ExpN.Pre R b L K costF costD needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow)
      (ExpN.Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n)

end FvModexp.Amd64.EvenHyp
