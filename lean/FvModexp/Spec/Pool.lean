import Janus

set_option autoImplicit false

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1b): the pooled `*big.stack` object shape the row
statements of `(*bigModExp).Run` fix for the `sync.(*Pool).Get` / `Put` runtime contracts (Janus's `PoolShape` row
binder, pinned by the precondition `S = StkShape`). Byte-identical copy of the proof-side `FvModexp.StkSh`
(Proofs/Common/StkPool.lean; the proofs show them equal by `rfl`):
* `SliceObj (2^40 - 1)` (Janus: a 24-byte header `{ptr, len, cap}` and, when `cap > 0`, its array, disjoint),
* `len = 0` (`stk.free()` stores it before the `Put`),
* `cap = 0 → ptr = 0`. -/

namespace FvModexp.Spec

open Janus Janus.Arm64 Janus.Spec Janus.Contracts Janus.Contracts.Pool

/-- the pooled `*big.stack` shape (copy of `FvModexp.StkSh`) -/
@[reducible] def StkShape : PoolShape := fun m d rs =>
  SliceObj (2 ^ 40 - 1) m d rs ∧ m.readLE (d + 8) 8 = 0 ∧ (m.readLE (d + 16) 8 = 0 → m.readLE d 8 = 0)

end FvModexp.Spec
