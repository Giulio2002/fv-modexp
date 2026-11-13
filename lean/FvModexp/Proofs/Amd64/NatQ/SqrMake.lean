import FvModexp.Proofs.Amd64.NatQ.SqrMakeR
import FvModexp.Proofs.Amd64.NatQ.SqrMakeA

/-!
# [TIGHT COSTS, divmc s38] `nat.sqr` (amd64): `z = z.make(2n)` (natmul.go:85-88) — re-export of `make_reuse` (SqrMakeR)
and `make_alloc` (SqrMakeA), split so the pieces compile in parallel (twin of Arm64/NatQ/SqrMake).
-/
