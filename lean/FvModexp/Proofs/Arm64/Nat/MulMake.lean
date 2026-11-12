import FvModexp.Proofs.Arm64.Nat.MulMakeR
import FvModexp.Proofs.Arm64.Nat.MulMakeA

/-!
# `nat.mul` (arm64): `z = z.make(m + n)` (natmul.go:31-35) — re-export of `make_reuse` (MulMakeR) and
`make_alloc` (MulMakeA), split so the two compile in parallel.
-/
