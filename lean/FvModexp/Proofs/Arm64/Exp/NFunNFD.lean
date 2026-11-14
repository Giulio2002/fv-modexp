import FvModexp.Proofs.Arm64.Exp.NNilD

/-! `ExpN.PreNF` (split out of `NFunNE.lean`, top s47): `(*Int).exp`'s pure call-site lemma `IExp.preNF_of` needs only
this definition, so `IExpP` imports this module instead of `NFunNE` and compiles in parallel with the `nat.expNN` chain. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- the precondition, `stk == nil`, every modulus (arguments `[z, zl, zc, st, x, xl, xc, y, yl, yc, m, n, mc, slow]`) -/
def PreNF (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat)
    (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  PreNil R b L K costF needR costR needS needP costS costP (s.regs 28).toNat (s.sp.toNat - 1312) zp zl zc st xp xl xc
    yp yl yc mp n mc slow s ∧ NHyp.XFacts R L xp xl xc

end FvModexp.Arm64.ExpN
