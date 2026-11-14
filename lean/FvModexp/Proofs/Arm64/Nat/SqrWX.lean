import FvModexp.Proofs.Arm64.Nat.SqrDefs
import FvModexp.Proofs.Arm64.Nat.NatAddDefs

/-!
# `nat.sqr` (arm64): the exported window `sqrWX` and `wordT_rt` (agent infra s54, moved out of `Nat/SqrHypX`)

A light module (no `nat.sqr` SCC proof in its closure): `NatQ/SqrHypQ` and the exp layer import it instead of
`Nat/SqrHypX`, so rows on the Q-form `nat.sqr` do not compile the retired old SCC (row-time fix, rel44).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- the window every exported `nat.sqr` call gets -/
abbrev sqrWX : Nat := sqrW 4096

set_option maxRecDepth 20000 in
theorem wordT_rt {R : RtInv} (hro : RoOut R) : Outside NatAdd.wordT 16 R.rt :=
  RoOut.out' hro 1 (by decide) (by decide)

end FvModexp.Arm64.NatSqr
