import FvModexp.Proofs.Arm64.Nat.KSqrB

/-!
# `karatsubaSqr` (arm64): `z0.abs = z0.abs.sqr(stk, x0.abs)` (natmul.go:300), `0x1bc4ac` → `0x1bc4d0`

From the boundary after `clear(z)` (`z[0:2n] = 0`): the call (`ks_sqcall`; `z0 = z[0:2·n2]` reused, exactly
`z[0:2·len x0]` written, holding `x0²`), then the stores of the result into `z0`'s header.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

end FvModexp.Arm64.NatSqr
