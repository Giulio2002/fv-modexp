import FvModexp.Proofs.Amd64.Top.RunRel
import FvModexp.Proofs.Amd64.Top.RunLMath

/-! # `Run` (amd64): the length-check boundary `P1` (after the three `BitLen`/`Uint64`) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace FvModexp.Amd64.Run

abbrev pcP1 : Nat := segAddr Extracted.program fn + 0x4e2

end FvModexp.Amd64.Run
