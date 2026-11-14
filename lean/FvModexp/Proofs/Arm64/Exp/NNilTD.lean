import FvModexp.Proofs.Arm64.Exp.NGetD

/-! Definitions and helper lemmas of `NNilT.lean` (split out, top s47: the module and its LibNE twin import this instead of each other / the original, so they compile in parallel). `nat.expNN.deferwrap1`'s entry. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- `nat.expNN.deferwrap1`'s entry (the closure's code word, `SP' + 216`) -/
abbrev dwA : Nat := 1788272

end FvModexp.Arm64.ExpN
