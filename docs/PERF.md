# Performance record (proof elaboration and `janus verify` rows)

Project sanity goal: every `janus verify` row <= 15 min wall and <= 16 GB (hard, `scripts/verify-all.sh` has no override); every proof module's
`lake build` / elaboration <= 5 min and <= 8 GB (target; anything above is profiled and fixed, never given more heartbeats/timeouts/memory);
median row <= 3 min; full run (both ISAs, 6 rows in parallel) <= 2 h.

Procedure for a slow module: `set_option trace.profiler true`, `janus.omega.log` (Janus PROOFS.md section Performance), then split segments,
use summaries, normalise to `Nat`, keep `omega` contexts small, use reducible closers. Record BEFORE and AFTER here.

| date | module / row | before (s, GB) | change | after (s, GB) |
|---|---|---|---|---|

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

## Function proofs, agent top (2026-11-10/11)
Dev compile, one module at a time (`build/dbuild.sh <isa> …`, `LEAN_NUM_THREADS=4`, under `memcap -m 16G`), wall / max RSS.
Lesson (before → after): the first setBytes exploration with `janus_data hd [hw]` did not finish 30 instructions in
> 5 min (49 rodata disjunctions in every `omega`); with `janus_data hd` + one `apart_of_data` fact: 24 s for the whole prefix.

| module | arm64 | amd64 |
|---|---|---|
| Nat/SetBytesDefs | 2.6 s, 2.2 GB | 1.6 s, 2.1 GB |
| Nat/SetBytesNorm (nat.norm loop + return) | 5.7 s, 2.2 GB | 7.9 s, 2.2 GB |
| Nat/SetBytesByte (byte loop) | 18.2 s, 2.2 GB | 33.1 s, 2.3 GB |
| Nat/SetBytesWord (word loop) | 7.3 s, 2.2 GB | 11.7 s, 2.2 GB |
| Nat/SetBytesMid | 2.8 s, 2.1 GB | 2.2 s, 2.1 GB |
| Nat/SetBytes (`ens`, 4 paths, makeslice) | 41.3 s, 2.4 GB | 42.0 s, 2.5 GB |
| Nat/SetBytesStd* (std copy) | same ±10 % (40.3 s max) | same (44.6 s max) |
(The ~2 GB floor is loading the Run `Extracted` olean.)
# Performance record (proof elaboration and `janus verify` rows)

Project sanity goal: every `janus verify` row <= 15 min wall and <= 16 GB (hard, `scripts/verify-all.sh` has no override); every proof module's
`lake build` / elaboration <= 5 min and <= 8 GB (target; anything above is profiled and fixed, never given more heartbeats/timeouts/memory);
median row <= 3 min; full run (both ISAs, 6 rows in parallel) <= 2 h.

Procedure for a slow module: `set_option trace.profiler true`, `janus.omega.log` (Janus PROOFS.md section Performance), then split segments,
use summaries, normalise to `Nat`, keep `omega` contexts small, use reducible closers. Record BEFORE and AFTER here.

| date | module / row | before (s, GB) | change | after (s, GB) |
|---|---|---|---|---|

## Mul/div machine summaries (agent divmc), 2026-11-11
Dev compile `scripts/dev-lean-divmc.sh -x <isa> FILE` (Lean 4.34.1, Janus v0.2.0 oleans, `LEAN_NUM_THREADS=4`, `memcap 8G`),
against the pinned Run extraction; every summary is proved on a restricted-program constant (`Lib*`, as expmc), never on
`Extracted.program.onlySegments`. Wall / max RSS of the whole module (no profiling fix needed so far, no heartbeat options
beyond `maxHeartbeats 0` on the executor theorems):

| module | arm64 | amd64 |
|---|---|---|
| Nat/LibAddTo, Nat/LibBasicMul (restricted programs + `eq_only`) | 6–9 s / 2.7 GB | 6–7 s / 2.7 GB |
| Nat/Callees (premise shapes, `Summary0.live`, `toSummaryRegs7`) | 1.2 s / 2.0 GB | 1.3 s / 2.0 GB |
| Nat/AddTo (`addTo`, 5 paths, addVV.abi0 + addVW calls) | 89 s / 4.4 GB | 125 s / 5.4 GB |
| Nat/BasicMul (`basicMul`: memclr + loop with addMulVVWW.abi0; loop lemma + pure step lemmas) | 74 s / 4.7 GB | 143 s / 5.5 GB |
| Common/DivmcNat, DivmcBits, DivmcMem | ≤ 1 s | — |

Cost drivers: each `by_cases` branch re-executes the prologue (AddTo: 3 runs); amd64 steps ~1.5× arm64. Next optimisation if
a module approaches the cap: one `janus_run` with conditional rewrite rules instead of `by_cases` before the run.
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
