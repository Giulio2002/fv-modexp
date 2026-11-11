import FvModexp.Proofs.Amd64.Top.RunLaDefs

/-! # `Run` (amd64): the operand-phase boundary `C0` -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace FvModexp.Amd64.Run

/-- The operand phase (`getData` of base/exp/mod) starts here. -/
abbrev pcC0 : Nat := segAddr Extracted.program fn + 0x5c7

end FvModexp.Amd64.Run
