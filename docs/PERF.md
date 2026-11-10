# Performance log

## Nat-level exponentiation layer (agent mathexp), 2026-11-10
`LEAN_NUM_THREADS=4 memcap -m 16G lake env lean <file>` (dependencies prebuilt), wall / max RSS:

| module | wall | max RSS |
|---|---|---|
| Proofs/Common/ExpBase   | 0.5 s | 0.51 GB |
| Proofs/Common/ExpWindow | 0.9 s | 0.55 GB |
| Proofs/Common/ExpMont   | 2.0 s | 0.60 GB |
| Proofs/Common/ExpOdd    | 1.1 s | 0.57 GB |
| Proofs/Common/ExpPow2   | 1.5 s | 0.59 GB |
| Proofs/Common/ExpSlow   | 1.4 s | 0.54 GB |
| Proofs/Common/ExpEven   | 1.7 s | 0.58 GB |
| Proofs/Common/ExpNN     | 1.0 s | 0.54 GB |
| tests/ExpDiff (508 #guard, not in lib) | 3.0 s | — |

All far below the 5 min / 8 GB module budget; no profiling needed.
