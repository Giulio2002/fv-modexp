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

## Nat-level multiplication / division layer (agent mathdiv), 2026-11-10
`LEAN_NUM_THREADS=4 lake env lean <file>` (dependencies prebuilt), wall / max RSS. Full `lake build` of the package
(all mathdiv + mathexp modules from scratch for the changed ones): well under 5 min. No module needed any profiling fix;
no heartbeat/timeout options are used anywhere.

| module | wall | max RSS | | module | wall | max RSS |
|---|---|---|---|---|---|---|
| BitsNat | 0.6 s | 0.53 GB | | DivRecMid | 2.0 s | 0.58 GB |
| BytesNat | 1.3 s | 0.58 GB | | DivRecStep | 3.0 s | 0.62 GB |
| Div64Math | 1.3 s | 0.55 GB | | DivW | 0.7 s | 0.53 GB |
| DivBasic | 1.3 s | 0.59 GB | | DivWW | 13.9 s | 1.12 GB |
| DivBasicEst | 2.1 s | 0.58 GB | | IntDiv | 0.6 s | 0.55 GB |
| DivBasicEstWin | 0.9 s | 0.56 GB | | IntOps | 1.1 s | 0.54 GB |
| DivBasicLemmas | 0.7 s | 0.53 GB | | Karatsuba | 3.9 s | 0.62 GB |
| DivBasicMath | 2.8 s | 0.58 GB | | KaratsubaSqr | 2.8 s | 0.60 GB |
| DivBasicStep | 1.9 s | 0.61 GB | | Limbs | 0.7 s | 0.54 GB |
| DivClosed | 0.3 s | 0.54 GB | | MulClosed | 2.2 s | 0.62 GB |
| DivContract | 0.3 s | 0.50 GB | | MulSqr | 2.7 s | 0.59 GB |
| DivLarge | 0.9 s | 0.57 GB | | NatBasic | 2.9 s | 0.67 GB |
| DivRec | 1.3 s | 0.60 GB | | NatDiv | 0.7 s | 0.55 GB |
| DivRecAux | 1.0 s | 0.56 GB | | NatMul1 | 2.4 s | 0.60 GB |
| DivRecCore | 1.1 s | 0.56 GB | | Slices | 0.6 s | 0.51 GB |
| DivRecFin | 1.0 s | 0.55 GB | | VecOps | 2.2 s | 0.60 GB |
| DivRecLoop | 8.4 s | 0.92 GB | | WordFacts | 0.4 s | 0.51 GB |
| DivRecMath | 0.8 s | 0.53 GB | | Words | 2.5 s | 0.57 GB |

Sum of all 36 mathdiv modules: 74 s; slowest DivWW 13.9 s / 1.1 GB, DivRecLoop 8.5 s / 0.92 GB.

## Leaf routines / assembly kernels (agent asm), 2026-11-11

Module elaboration: `scripts/asm-perf.sh` (each module from scratch with `scripts/dev-lean.sh`, `LEAN_NUM_THREADS=4`,
under `memcap`), wall / max RSS of the `lean` process (≈1.9 GB of it is the Janus framework import). All far below the
5 min / 8 GB module budget; no heartbeat/timeout option is raised anywhere.

| module | wall | max RSS | | module | wall | max RSS |
|---|---|---|---|---|---|---|
| Arm64/AddVVSum | 9.7 s | 2.22 GB | | Amd64/AddVVSum | 7.1 s | 2.19 GB |
| Arm64/SubVVSum | 7.6 s | 2.21 GB | | Amd64/SubVVSum | 7.4 s | 2.18 GB |
| Arm64/MulAddVWWSum | 8.5 s | 2.22 GB | | Amd64/MulAddVWWSum | 6.6 s | 2.17 GB |
| Arm64/AddMulVVWWSum | 13.9 s | 2.30 GB | | Amd64/AddMulVVWWSum (both paths) | 46.4 s | 2.92 GB |
| Arm64/CmpSum | 5.8 s | 2.18 GB | | Amd64/CmpSum | 5.2 s | 2.15 GB |
| Arm64/Div64Sum | 16.2 s | 2.59 GB | | Common/AsmMul, AsmAddMul | 2.8 s, 3.2 s | 2.06 GB |
| Arm64/DivWWSum | 4.1 s | 2.17 GB | | Common/AsmLimbs, AsmTac, AsmCmp, AsmModel, AsmDiv* | ≤ 2.3 s each | ≤ 2.05 GB |
| Lib/* (library programs) | ≤ 1.2 s each | ≤ 2.0 GB | | Arm64/Amd64 AsmModels | 0.9 s | 2.0 GB |

Before/after (amd64 `addMulVVWW`, the only module that needed work): one `janus64_run` over the whole 4x `MULQ` block
exceeded the 200000-heartbeat default budget (the carry terms nest four deep and are re-simplified at every step), and
the block-arithmetic `omega` calls ran > 5 min (they saw every `%`-hypothesis of the context; and `(by omega)` with
metavariable arguments). Fix: per-limb segment lemmas (`segM0..3`, ADX `segA0..3`, `ablock`) so each run is 8–14
instructions on a generic state, value lemmas (`am1`, `adx1`, `tele4`, `blkval4`, `ablkval`) proved on small contexts
(`modre`), aliasing given as the exact pairwise disjointness facts (`dpair`) instead of a context disjunction. After:
46 s / 2.9 GB for the whole module (both code paths).

Rows (`scripts/asm-row.sh`, `janus verify` of the single-function extraction, memcap 16G / timeout 900; warm replay cache
of the Janus framework — the first row of a fresh cache spends ~6.5 min replaying the 329 Janus modules once):

| row | arm64 | amd64 |
|---|---|---|
| AddVV | PASS 404 s (cold cache) | PASS 26 s |
| SubVV | PASS 28 s | PASS 38 s |
| MulAddVWW | PASS 27 s | PASS 27 s |
| AddMulVVWW | PASS 47 s | PASS 14 s (4 theorems: both paths) |
| Cmp (`nat.cmp`) | PASS 22 s | PASS 22 s |
| Div64 (`math/bits.Div64`) | PASS 42 s | n/a (intrinsic) |
| DivWW | PASS 16 s | todo |

Row peak memory: the sandboxed `leanchecker` runs inside the memcap scope; the scope's `memory.peak` was ~0.83–0.89 GB
where it was captured (`build/asm-rows.tsv`; some entries show the `janus` driver only, the measurement hook is fixed
in `scripts/asm-row.sh`).
