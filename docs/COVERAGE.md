# Coverage

What is verified: the machine code of geth v1.17.10's Osaka MODEXP precompile (`core/vm`,
`PrecompiledContractsOsaka[0x05] = &bigModExp{eip2565: true, eip7823: true, eip7883: true}`) on linux/arm64 and linux/amd64,
against the EthLib MODEXP specification (`EthLib.Execution.Evm.Precompiles.Modexp`, pinned package `ethlibspec`), for every
fork `.fusaka ≤ fork`. The statements are explained in [`HUMAN-REVIEW.md`](HUMAN-REVIEW.md) §2; the times are in
[`PERF.md`](PERF.md).

<!-- RELEASE-RUN: update the status cells below when a new release run lands. -->
Status on Janus v0.4.0: release run **rel51 PENDING** (TBD: arm64 —/43, amd64 —/37).
Previous release run **rel50** (Janus v0.3.3, fresh cache, 2026-11-15, before the v0.4.0 migration): every row verified on both
ISAs, arm64 43/43 and amd64 37/37, every main theorem with its kernel-checked non-vacuity witness. Times in the table are rel50's.
<!-- /RELEASE-RUN -->

## The claim

`scripts/verify-all.sh` reads this table. The Symbol cell is the exact symbol passed to `janus extract`; a per-ISA status
starting with `verified` (or `partial`) is verified, `todo` / `in progress` fails the run as MISSING, anything else is skipped.
The proof module is the claim module `lean/FvModexp/<Arm64|Amd64>/<module>.lean` (`module:` in the Notes cell, else the
last symbol component); a summary row's module is `lean/FvModexp/Proofs/<Arm64|Amd64>/<module>.lean`. Rows also listed in `scripts/release-rows.txt` run at their place in that list.

| Symbol | Claim | arm64 | amd64 | Notes |
|---|---|---|---|---|
| `github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run` | row 1, every input | verified (rel50: 79 s; rel51: TBD) | verified (rel50: 83 s; rel51: TBD) | `Run.correctness_total`: lengths pass → `(compute data (parseLengths data), nil)`; lengths fail → `(nil, err)`, `err ≠ nil`; module: `RunTotal` |
| `github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run` | row 1, lengths pass | verified (rel50: 476 s; rel51: TBD) | verified (rel50: 521 s; rel51: TBD) | `RunSucc.correctness`, witness `3^5 mod 7` → `[5]`; module: `RunSucc` |
| `github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run` | row 1, lengths fail | verified (rel50: 243 s; rel51: TBD) | verified (rel50: 379 s; rel51: TBD) | `Run.correctness`, witness: base-length header 1025; module: `RunErr` |
| `github.com/ethereum/go-ethereum/core/vm.(*bigModExp).RequiredGas` | row 2 | verified (rel50: 224 s; rel51: TBD) | verified (rel50: 269 s; rel51: TBD) | lengths pass → `requiredGas fork data (parseLengths data)` for every `.fusaka ≤ fork`; no panic or fault for any input; no runtime contract |

Row 3 has no machine code: `FvModexp.Proofs.Compose.composition` (`lean/FvModexp/Proofs/Common/Compose.lean`, checked by
`make build`) proves that geth's `RunPrecompiledContract` logic (gas check, optional result cache, then `Run`) agrees with
EthLib's `modexp fork data gas` for any precompile meeting rows 1 and 2 (stated as the hypothesis `RowsHold`).

## Release rows

The row-1 theorems compose machine-code summaries of every function `Run` reaches. Each summary below is also a release row of
its own, verified on the same `Run` extraction, with a `correctness` theorem and a kernel-checked `Witness.nonvacuous`. They run
before the row-1 rows, in the dependency order of `scripts/release-rows.txt`, so that each row compiles mostly its own modules
(see [`PERF.md`](PERF.md)). A function without its own row (for example arm64 `nat.expNNSlow`, the `deferwrap` closures,
`nat.setBytes`) is verified inside the rows that call it.

"(Q)": the tight-cost form of the summary (per-call allocation bound small enough that `Run`'s total budget stays below `2^35`
bytes); the arm64 rows without Q verify the earlier cost form of the same function, which some proofs still import.
All functions are from `github.com/ethereum/go-bigmodexpfix` (`src/math/big`, f9e208c548ab), the patched `math/big` that geth
uses for MODEXP.

| Row module | Go function | arm64 | amd64 |
|---|---|---|---|
| Nat/StackNatRow | `(*stack).nat` | ✓ | ✓ |
| Nat/MulAddWWRow | `nat.mulAddWW` | ✓ | ✓ |
| Nat/AddVWRow | `addVW` | ✓ | ✓ |
| Nat/SubVWRow | `subVW` | ✓ | ✓ |
| Nat/BasicMulRow | `basicMul` | ✓ | — |
| Nat/BasicSqrRow | `basicSqr` | ✓ | ✓ |
| Nat/TruncRow | `nat.trunc` | ✓ | ✓ |
| Nat/RshRow | `nat.rsh` | ✓ | ✓ |
| Nat/LshRow | `nat.lsh` | ✓ | ✓ |
| Int/IntASRow | `(*Int).Add`, `(*Int).Sub` (reached from `karatsuba`, `karatsubaSqr`) | ✓ | ✓ |
| Int/IntSubRow | `(*Int).Sub` alone | ✓ | — |
| NatQ/BasicSqrRowQ | `basicSqr` (Q) | ✓ | ✓ |
| NatQ/SqrRowQ | `nat.sqr`, incl. `karatsubaSqr` (Q) | ✓ | ✓ |
| NatQ/MulRowQ | `nat.mul`, incl. `karatsuba`, `(*Int).mul` (Q) | ✓ | ✓ |
| Exp/MontRow | `nat.montgomery` | ✓ | ✓ |
| Exp/SubMod2NRow | `nat.subMod2N` | ✓ | ✓ |
| Exp/ModInvRow | `nat.modularInverseModPowerOfTwo` | ✓ | ✓ |
| Nat/DivWRow | `nat.divW` | ✓ | ✓ |
| Nat/DivWVWRow | `divWVW` | ✓ | ✓ |
| Nat/DivBasicRow | `nat.divBasic` | ✓ | ✓ |
| Nat/MulRow | `nat.mul` | ✓ | — |
| Nat/DrsRow | `nat.divRecursiveStep` | ✓ | — |
| Nat/DivRow | `nat.div` | ✓ | — |
| Nat/DivMRow | `nat.div` as called by `(*Int).Mod` | ✓ | — |
| Nat/RemRow | `nat.rem` | ✓ | — |
| NatQ/DivBasicRowQ | `nat.divBasic` (Q) | ✓ | ✓ |
| NatQ/DrsRowQ | `nat.divRecursiveStep` (Q) | ✓ | ✓ |
| NatQ/DivRowQ | `nat.div` (Q) | ✓ | ✓ |
| NatQ/DivMRowQ | `nat.div` as called by `(*Int).Mod` (Q) | ✓ | — |
| NatQ/RemRowQ | `nat.rem` (Q) | ✓ | ✓ |
| Int/ModRow | `(*Int).Mod` | ✓ | ✓ |
| Exp/W2Row | `nat.expNNOddMontgomeryWindowSize2` | ✓ | ✓ |
| Exp/W4Row | `nat.expNNOddMontgomeryWindowSize4` | ✓ | ✓ |
| Exp/P2PreRow | `buildPrecomputationWindowModPower2` | — | ✓ |
| Exp/P2W2Row | `nat.expNNPowerOfTwoWindowSize2` | ✓ | ✓ |
| Exp/P2W4Row | `nat.expNNPowerOfTwoWindowSize4` | ✓ | ✓ |
| Exp/P2DRow | `nat.expNNPowerOfTwo` | ✓ | ✓ |
| Exp/SlowRow | `nat.expNNSlow` | — | ✓ |
| Exp/NRow | `nat.expNN` | ✓ | ✓ |
| Exp/EvenRow | `nat.expNNEven` | ✓ | ✓ |
| ExpQ/IExpRow (arm64), Exp/IExpRow (amd64) | `(*Int).exp` | ✓ | ✓ |
| RequiredGas, RunErr, RunSucc, RunTotal | the claim rows above (modules in `lean/FvModexp/<Isa>/`) | ✓ | ✓ |

Per ISA: 43 rows on arm64, 37 on amd64.

## Assembly leaf routines

The vector kernels and word routines are verified inside the release rows through their library summaries
`Proofs/<Isa>/<Fn>Sum.lean` ([`MODELS.md`](MODELS.md#assembly-leaf-routines)). Rows that reach each one:

| Function (library summary) | arm64 Run-extraction rows | amd64 Run-extraction rows |
|---|---|---|
| `addVV.abi0` (`AddVVSum.addVV_summary`) | DivRow (via nat.mul / divBasic), BasicMulRow, IntASRow, … | IntASRow (nat.add), BasicSqrRow |
| `subVV.abi0` (`SubVVSum.subVV_summary`) | DivRow (divBasic), IntASRow, … | IntASRow (nat.sub) |
| `addMulVVWW.abi0` (`AddMulVVWWSum.addMulVVWW_summary`) | DivRow (drs → nat.mul → basicMul), BasicMulRow | BasicSqrRow (basicSqr + basicMul) |
| `mulAddVWW.abi0` (`MulAddVWWSum.mulAddVWW_summary`) | DivRow (divBasic / drs), MulAddWWRow | MulAddWWRow |
| `lshVU.abi0` (`LshVUSum.lshVU_summary`) | DivRow (divLarge shift), LshRow | LshRow, BasicSqrRow |
| `rshVU.abi0` (`RshVUSum.rshVU_summary`) | DivRow (divLarge unshift), RshRow | RshRow |
| `nat.cmp` (`CmpSum.cmp_summary`) | DivRow (div `u.cmp(v)`), IntASRow | IntASRow (`(*Int).Add/Sub` sign case) |
| `divWW` (`DivWWSum.divWW_summary`) | DivRow, DivWRow, DivWVWRow | DivWRow, DivWVWRow |
| `bits.Div64` (`Div64Sum.div64_summary`, arm64 only) | DivRow, DivWRow, DivWVWRow | — (inlined `DIVQ` in divWW) |
| `reciprocalWord` (`RecipWordSum.recip_summary`, arm64 only) | DivRow, DivWRow, DivWVWRow | — (inlined) |

Their first proofs, on single-function extractions, are kept in `lean/FvModexp/Legacy/` (not part of the release run;
[`DEVELOPMENT.md`](DEVELOPMENT.md#leanfvmodexplegacy)).

## Scope limits of the claim

* **Stack growth / preemption not modelled.** `runtime.morestack` is never executed: every row's precondition makes each stack-check
  prologue fall through. Covered calls: arm64 row 1 success `SP − g.stackguard0 > 73 568` B (`GuardOK s W`, `W ≥ 624 + 72944`),
  arm64 row 1 error `> 4 800` B, amd64 row 1 error `> 4 800` B (`StackGuardOK s 4800`), amd64 row 1 success
  `> 44 352` B (`W ≥ 616 + 43736`: Run's frame + the closed amd64 `(*Int).exp` window), row 2 arm64 `> 464` B;
  and `stackguard0 ≠ stackPreempt` (no pending preemption). Calls with less free stack, or a pending preemption, are not covered.
* **Precompile result cache** (on by default in geth v1.17.10): not part of the row-3 model (`cache = nil`); its soundness for MODEXP
  is the pure-Lean `FvModexp.CacheKey.cacheKey_eq` (`Proofs/Common/CacheKey.lean`).

See [`HUMAN-REVIEW.md`](HUMAN-REVIEW.md) §3 for every assumption.
