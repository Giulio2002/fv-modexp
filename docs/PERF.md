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
