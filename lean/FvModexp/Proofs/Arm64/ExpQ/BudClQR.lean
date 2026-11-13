import FvModexp.Proofs.Arm64.ExpQ.BudClQ
import FvModexp.Proofs.Arm64.NatQ.BudRem

set_option autoImplicit false

/-!
# TIGHT COSTS: `IExp.BudClQ` with the `rem` field discharged (agent expmc s45)

divmc's `Q.BudT.rem` (Arm64/NatQ/BudRem.lean) is exactly the `hrem` premise of `IExp.budClQ_of` at the bridged
`nat.rem` cost `clRQ 0`. `budClQ_of_ep` leaves only infra's `even` / `p2` fields open.
-/

namespace FvModexp.Arm64.IExp

/-- **`BudClQ` from infra's `even` / `p2` targets** (rem: divmc's `Q.BudT.rem`; slow/obud/ocost: expmc) -/
theorem budClQ_of_ep
    (heven : ∀ xl yl n, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 →
      clEQ 0 xl yl n ≤ 72 * BudQ.opC (max xl n) + yl * (320 * BudQ.opC (max xl n)))
    (hp2 : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      clP 0 xl yl lm ≤ 6 * BudQ.opC (max xl n) + yl * (64 * BudQ.opC (max xl n))) : BudClQ :=
  budClQ_of (fun xl n hx hn0 hn => Q.BudT.rem xl n hx hn0 hn) heven hp2

end FvModexp.Arm64.IExp
