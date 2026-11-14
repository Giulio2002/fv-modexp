import FvModexp.Proofs.Arm64.Exp.NDefs
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Arm64.Nat.Free

/-! Definitions and helper lemmas of `NStkNil.lean` (split out, top s47: the module and its LibNE twin import this instead of each other / the original, so they compile in parallel). `sync.(*Pool).Get`'s address. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- `sync.(*Pool).Get` -/
abbrev getA : Nat := Extracted.program.contractAddr "sync.(*Pool).Get"

end FvModexp.Arm64.ExpN
