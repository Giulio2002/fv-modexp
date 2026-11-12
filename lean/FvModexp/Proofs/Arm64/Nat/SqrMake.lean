import FvModexp.Proofs.Arm64.Nat.SqrMakeR
import FvModexp.Proofs.Arm64.Nat.SqrMakeA

/-!
# `nat.sqr` (arm64): `z = z.make(2n)` (natmul.go:85-88) — re-export of `make_reuse` (SqrMakeR) and `make_alloc`
(SqrMakeA), split so the pieces compile in parallel (as MulMake).
-/
