import Janus
import Extracted
import FvModexp.Spec.Pool

set_option autoImplicit false

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1b): amd64 definitions the row-1 statements of
`(*bigModExp).Run` use for the Janus `sync.(*Pool)` contracts: the pooled element type `stkT` (byte-identical copy of
the proof-side `FvModexp.Amd64.Free.stkT`, Proofs/Amd64/Nat/Free.lean; shown equal by `rfl`). The witness call-site
premises (amd64 twins of `Spec.WitSitesArm64`) are added here with the amd64 success witness. -/

namespace FvModexp.Spec.WitSitesAmd64

/-- the `*big.stack` type descriptor (read-only data of the extraction): the `Pool.Put` element type -/
abbrev stkT : Nat := Extracted.dataAddr.«type:*big.stack#6bae7c96»

end FvModexp.Spec.WitSitesAmd64
