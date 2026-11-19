# Performance

Proof checking must stay fast and bounded. This page gives the rules, how rows are measured, the times of the final release
run, and the techniques that brought every row under the limits. The full development record (every before/after
measurement, by module) is [`history/PERF-log.md`](history/PERF-log.md).

## Rules

* **Hard caps per `janus verify` row: 900 s wall and 16 GB** (`timeout 900`, `memcap 16G`). They are constants of
  `scripts/verify-all.sh`; no variable, flag or file changes them. A row over a cap fails.
* **Release margin: every row at most 600 s** in the release run (fresh cache, rows one at a time).
* Every proof module should elaborate in at most 5 minutes and 8 GB. A slower module is profiled and fixed (smaller
  `omega` contexts, segment splits, summaries, `Nat` normalisation). The fix is never more heartbeats, a longer timeout or
  more memory.
* The release run uses a fresh, empty `JANUS_CACHE_DIR`, so every row pays for compiling and kernel-replaying the proof
  modules it is the first to need.

## How a row is measured

`scripts/verify-all.sh` runs the rows of `scripts/release-rows.txt` in that order (dependency order: a row comes after
every row whose proof modules it imports), then any other row of `docs/COVERAGE.md`. Before the first row it warms the
cache with the Janus framework and the shared dependency closure (Janus, EthLib), outside the row caps.
For each row it records wall time, peak memory of the whole row (the `memcap` cgroup and the per-job peaks Janus reports,
whichever is larger), and the host load average at start, end and maximum, in `build/rows.tsv`. With `JANUS_TIMINGS=1`
the row log splits the time into compile, statement audit and kernel replay.

Because the cache is shared between rows, a row's time is mostly its *own* modules: the proof modules that no earlier
row compiled. A row that is the first to import a large shared layer pays for it. This is why the release order matters
and why the per-row numbers below are not a measure of each function's difficulty in isolation.

## Release run

<!-- RELEASE-RUN: update this block when a new release run lands (Janus tag, run id, per-row table). -->
**rel51**, Janus v0.4.0 (`b5db64328e92cf4a5d5b87c32a9c66844b0d892b`, binary sha256 `b92df613…`), snapshot of main `bef180a8`, fresh cache per ISA, one row at a time (`ROWS=1`), witnesses on, `JANUS_TIMINGS=1`, 2026-11-19:

| ISA | rows | result | wall (rows + warm-up) | sum of row times | slowest row | largest peak memory |
|---|---|---|---|---|---|---|
| arm64 | 43 | **43/43 PASS** | 20 354 s + 989 s | 14 089 s | `Exp/W4Row` 838 s | 5.2 GB (`RunSucc`) |
| amd64 | 37 | **37/37 PASS** (36 in the run + 1 single-row rerun) | 16 826 s + 1 473 s | 15 344 s | `NatQ/DivRowQ` 864 s | 6.3 GB (`Nat/BasicSqrRow`) |

The host was heavily loaded during this run (another project's gate and kernel checkers shared the machine): verify-all starts a row only at a 1-minute load below 80, but load rose while rows ran. Maximum load per row: median 93.5 (arm64) and 92.5 (amd64), peak 217.9 and 195.8 (rel50: median 14.2 / 16.6). Rows over 600 s, with load at start / end / max, cache-lock wait (LOCK) and own time (OWN = janus total minus LOCK), split into own-module compile, kernel replay and audit:

* arm64 NatQ_DivRowQ           PASS      665s  2678MB  LOAD 79.91/172.56/215.29 | LOCK 0s | OWN 663s | compile 67 mods 450s ok=true | replay 168s | audit 40s | janus 664s
* arm64 Exp_W2Row              PASS      752s  2988MB  LOAD 78.94/114.31/138.54 | LOCK 0s | OWN 751s | compile 90 mods 415s ok=true | replay 284s | audit 47s | janus 751s
* arm64 Exp_W4Row              PASS      838s  3149MB  LOAD 79.94/58.45/217.89 | LOCK 0s | OWN 836s | compile 85 mods 535s ok=true | replay 247s | audit 49s | janus 836s
* arm64 RunSucc                PASS      757s  5176MB  LOAD 62.96/48.34/101.56 | LOCK 0s | OWN 755s | compile 68 mods 480s ok=true | replay 189s | audit 83s | janus 755s
* amd64 Nat_BasicSqrRow        PASS      642s  6330MB  LOAD 66.42/51.36/120.19 | LOCK 0s | OWN 641s | compile 28 mods 512s ok=true | replay 117s | audit 9s | janus 641s
* amd64 NatQ_SqrRowQ           PASS      642s  4330MB  LOAD 77.70/126.58/131.43 | LOCK 0s | OWN 639s | compile 48 mods 379s ok=true | replay 239s | audit 17s | janus 639s
* amd64 NatQ_MulRowQ           PASS      699s  2346MB  LOAD 77.74/32.89/135.91 | LOCK 0s | OWN 698s | compile 78 mods 471s ok=true | replay 204s | audit 18s | janus 698s
* amd64 Exp_SubMod2NRow        PASS      776s  5155MB  LOAD 61.34/39.89/195.85 | LOCK 0s | OWN 774s | compile 40 mods 524s ok=true | replay 234s | audit 12s | janus 774s
* amd64 NatQ_DrsRowQ           FAIL      901s  2723MB  LOAD 78.68/121.62/134.41 | LOCK 0s | compile 140 mods 518s ok=true | audit 35s | last timing: theorem audit 34.949s
* amd64 NatQ_DivRowQ           PASS      864s  5252MB  LOAD 78.76/51.73/78.76 | LOCK 1s | OWN 861s | compile 82 mods 522s ok=true | replay 250s | audit 28s | janus 862s
* amd64 Exp_W4Row              PASS      683s  3304MB  LOAD 43.15/14.95/139.66 | LOCK 0s | OWN 681s | compile 118 mods 365s ok=true | replay 273s | audit 40s | janus 681s

amd64 `NatQ/DrsRowQ` hit the 900 s timeout in the run (FAIL, load 79 / 122 / 134, LOCK 0; it had compiled its 140 own modules in 518 s and passed the statement audit, and was stopped in kernel replay; rel50: 532 s). It was re-run alone, same snapshot and same cache, admitted at load below 40 (load 34 / 46 / 45): **PASS in 33 s** (1.8 GB). This rerun is NOT a fresh-cache time: all 465 modules came from the store (compiled by the failed attempt and the later rows) and the kernel replay found its closure already checked; it shows the row verifies (statement audit, kernel replay of the theorem and its witness), not how long it takes from scratch.

The rows over 600 s that passed were not re-run at normal load (user decision: rel51 is the final run). The same snapshot passed `RELEASE=1 scripts/no-sorry.sh` (release lint, Lean-level IO lint, spec closure: 8 of 8 final rows). The return-address audit (`check-ra-pin`) is retired: since v0.4.0 the precondition is evaluated before the return address is installed and Janus pins it.

Per row (seconds / peak MB / maximum load during the row):

| row | arm64 | amd64 |
|---|---|---|
| `Nat/StackNatRow` | 141 / 2466 / 122 | 268 / 1011 / 111 |
| `Nat/MulAddWWRow` | 180 / 948 / 79 | 388 / 1215 / 80 |
| `Nat/AddVWRow` | 81 / 963 / 86 | 98 / 1169 / 51 |
| `Nat/SubVWRow` | 60 / 953 / 79 | 121 / 1131 / 70 |
| `Nat/BasicMulRow` | 127 / 3304 / 84 | — |
| `Nat/BasicSqrRow` | 426 / 3221 / 123 | 642 / 6330 / 120 |
| `Nat/TruncRow` | 132 / 857 / 80 | 277 / 1130 / 92 |
| `Nat/RshRow` | 136 / 864 / 136 | 190 / 1268 / 39 |
| `Nat/LshRow` | 113 / 911 / 79 | 149 / 1266 / 33 |
| `Int/IntASRow` | 279 / 1192 / 94 | 299 / 1307 / 133 |
| `Int/IntSubRow` | 15 / 428 / 62 | — |
| `NatQ/BasicSqrRowQ` | 289 / 2848 / 63 | 301 / 6130 / 141 |
| `NatQ/SqrRowQ` | 347 / 3001 / 112 | 642 / 4330 / 131 |
| `NatQ/MulRowQ` | 375 / 2182 / 134 | 699 / 2346 / 136 |
| `Exp/MontRow` | 164 / 1746 / 77 | 306 / 3618 / 119 |
| `Exp/SubMod2NRow` | 264 / 2866 / 121 | 776 / 5155 / 196 |
| `Exp/ModInvRow` | 244 / 2341 / 82 | 545 / 2515 / 92 |
| `Nat/DivWRow` | 215 / 1194 / 95 | 220 / 1275 / 60 |
| `Nat/DivWVWRow` | 14 / 378 / 78 | 19 / 614 / 67 |
| `Nat/DivBasicRow` | 339 / 4449 / 80 | 508 / 3604 / 97 |
| `Nat/MulRow` | 448 / 2179 / 112 | — |
| `Nat/DrsRow` | 395 / 3387 / 89 | — |
| `Nat/DivRow` | 472 / 2649 / 125 | — |
| `Nat/DivMRow` | 344 / 3623 / 149 | — |
| `Nat/RemRow` | 283 / 4504 / 112 | — |
| `NatQ/DivBasicRowQ` | 570 / 4499 / 193 | 513 / 3680 / 112 |
| `NatQ/DrsRowQ` | 592 / 3857 / 140 | 901 / 2723 / 134 FAIL (cap); rerun PASS 33 / 1775 / 45, warm cache |
| `NatQ/DivRowQ` | 665 / 2678 / 215 | 864 / 5252 / 79 |
| `NatQ/DivMRowQ` | 262 / 3597 / 84 | — |
| `NatQ/RemRowQ` | 221 / 4475 / 87 | 214 / 2164 / 57 |
| `Int/ModRow` | 263 / 4064 / 100 | 370 / 3868 / 90 |
| `Exp/W2Row` | 752 / 2988 / 139 | 548 / 3201 / 135 |
| `Exp/W4Row` | 838 / 3149 / 218 | 683 / 3304 / 140 |
| `Exp/P2W2Row` | 544 / 3128 / 158 | 369 / 2991 / 78 |
| `Exp/P2W4Row` | 369 / 1560 / 132 | 363 / 3021 / 53 |
| `Exp/P2DRow` | 349 / 2216 / 77 | 218 / 2153 / 52 |
| `Exp/NRow` | 506 / 4579 / 62 | 535 / 3895 / 110 |
| `Exp/EvenRow` | 298 / 3932 / 83 | 490 / 4314 / 82 |
| `ExpQ/IExpRow` | 390 / 4381 / 87 | — |
| `RequiredGas` | 303 / 1782 / 66 | 483 / 3348 / 119 |
| `RunErr` | 420 / 1675 / 119 | 517 / 1330 / 74 |
| `RunSucc` | 757 / 5176 / 102 | 567 / 5062 / 99 |
| `RunTotal` | 107 / 4866 / 65 | 85 / 4782 / 51 |
| `Exp/P2PreRow` | — | 351 / 2957 / 136 |
| `Exp/SlowRow` | — | 345 / 3639 / 87 |
| `Exp/IExpRow` | — | 480 / 4415 / 101 |
<!-- /RELEASE-RUN -->

### Previous release run: rel50 on Janus v0.3.3

The previous reference run. The proofs were migrated to Janus v0.4.0 after this run, and the claim rows were
renamed (`Top/RunErr` → `RunErr`, and the same for `RunSucc` and `RunTotal`); the times below are those of the v0.3.3 tree.

**rel50**, Janus v0.3.3 (`6d65752215a09ceaf88d18e2f11bac7bcf19eb82`, binary sha256 `9127bf82…6c193d9d`), fresh cache per ISA,
one row at a time (`ROWS=1`), `JANUS_TIMINGS=1`, 2026-11-15:

| ISA | rows | result | wall (rows + warm-up) | sum of row times | slowest row | largest peak memory |
|---|---|---|---|---|---|---|
| arm64 | 43 | **43/43 PASS** | 9 995 s + 844 s | 9 938 s | `Exp/NRow` 538 s | 5.2 GB (`RunSucc`) |
| amd64 | 37 | **37/37 PASS** | 10 815 s + 894 s | 10 760 s | `NatQ/DrsRowQ` 532 s | 6.1 GB (`NatQ/BasicSqrRowQ`) |

No row exceeded 600 s. Host load (1-minute average) during the rows: median 14.2 (arm64) and 16.6 (amd64), maximum 31.1
and 33.5. The same tree passed `RELEASE=1 scripts/no-sorry.sh` (spec closure: 8 of 8 final rows) and the return-address
pin audit that v0.3.3 required (`scripts/check-ra-pin --release`: 43/43 and 37/37 clean; not needed since v0.4.0).

Per row, in arm64 release order (seconds / peak MB):

| row | arm64 | amd64 |
|---|---|---|
| `Nat/StackNatRow` | 128 / 2475 | 159 / 996 |
| `Nat/MulAddWWRow` | 149 / 961 | 210 / 1166 |
| `Nat/AddVWRow` | 55 / 1014 | 69 / 1069 |
| `Nat/SubVWRow` | 57 / 975 | 63 / 1050 |
| `Nat/BasicMulRow` | 115 / 3220 | — |
| `Nat/BasicSqrRow` | 311 / 3131 | 376 / 6085 |
| `Nat/TruncRow` | 113 / 902 | 182 / 1133 |
| `Nat/RshRow` | 115 / 836 | 136 / 1313 |
| `Nat/LshRow` | 93 / 923 | 123 / 1257 |
| `Int/IntASRow` | 218 / 1154 | 170 / 1313 |
| `Int/IntSubRow` | 14 / 450 | — |
| `NatQ/BasicSqrRowQ` | 257 / 2795 | 228 / 6127 |
| `NatQ/SqrRowQ` | 311 / 2903 | 401 / 4281 |
| `NatQ/MulRowQ` | 319 / 1675 | 390 / 2189 |
| `Exp/MontRow` | 138 / 1672 | 284 / 3577 |
| `Exp/SubMod2NRow` | 206 / 2759 | 490 / 5731 |
| `Exp/ModInvRow` | 190 / 2347 | 330 / 2441 |
| `Nat/DivWRow` | 150 / 1194 | 167 / 1287 |
| `Nat/DivWVWRow` | 12 / 319 | 15 / 423 |
| `Nat/DivBasicRow` | 274 / 4409 | 263 / 3563 |
| `Nat/MulRow` | 375 / 2161 | — |
| `Nat/DrsRow` | 341 / 1730 | — |
| `Nat/DivRow` | 357 / 2537 | — |
| `Nat/DivMRow` | 204 / 3582 | — |
| `Nat/RemRow` | 163 / 4471 | — |
| `NatQ/DivBasicRowQ` | 265 / 4501 | 267 / 3574 |
| `NatQ/DrsRowQ` | 291 / 1714 | 532 / 2062 |
| `NatQ/DivRowQ` | 333 / 2623 | 508 / 5218 |
| `NatQ/DivMRowQ` | 140 / 3598 | — |
| `NatQ/RemRowQ` | 125 / 4519 | 190 / 2120 |
| `Int/ModRow` | 164 / 3931 | 317 / 3849 |
| `Exp/W2Row` | 424 / 2944 | 460 / 3309 |
| `Exp/W4Row` | 440 / 3008 | 516 / 3094 |
| `Exp/P2PreRow` | — | 314 / 3089 |
| `Exp/P2W2Row` | 299 / 3088 | 330 / 2957 |
| `Exp/P2W4Row` | 228 / 1603 | 319 / 2956 |
| `Exp/P2DRow` | 326 / 2147 | 234 / 2050 |
| `Exp/SlowRow` | — | 226 / 3032 |
| `Exp/NRow` | 538 / 4575 | 424 / 3745 |
| `Exp/EvenRow` | 368 / 3746 | 516 / 4083 |
| `ExpQ/IExpRow` (arm64), `Exp/IExpRow` (amd64) | 310 / 4417 | 299 / 4208 |
| `RequiredGas` | 224 / 1601 | 269 / 3130 |
| `RunErr` | 243 / 1624 | 379 / 1306 |
| `RunSucc` | 476 / 5161 | 521 / 4834 |
| `RunTotal` | 79 / 4855 | 83 / 4713 |

The table lists rows by name; the exact order of each ISA is `scripts/release-rows.txt` (`LIST_ONLY=1 scripts/verify-all.sh`
prints it). A dash means the row does not exist on that ISA (see [`COVERAGE.md`](COVERAGE.md)).

## Techniques that mattered

Most slow proofs had one of a few causes. Each item gives the fix and a typical measured effect (module elaboration
time unless a row is named); the per-module numbers are in the history log.

1. **Prove summaries on a small library program, not on the whole extraction.** The Run extraction has 84 functions
   (82 on amd64). Running a proof on `(Extracted.program.onlySegments names).link impl` makes the kernel re-evaluate the
   segment filter (string comparisons on long symbol names) in every instruction-fetch fact. Proving the same `Ensures` on
   a generated constant holding only the needed segments (`scripts/gen-libprog-sub.py`), then rewriting with its
   `eq_only` theorem, took one Montgomery loop iteration from 254 s to 28 s. The amd64 window loops use one-segment
   programs the same way.
2. **Keep `omega` contexts small.** `omega` case-splits on every disjunction in the local context. After a large run,
   the context holds dozens of `Apart`/`Outside` facts (each a disjunction) and equations with `% 2^64`; a single
   `by omega` there took 10–80 s, and several such calls ran a module out of 8 GB. Fix: move the arithmetic into small
   lemmas with explicit arguments, `clear` the disjunctions a step does not need, and hide the rest behind an opaque
   wrapper during `janus_run` (unwrap after). Example: Run's operand-0 prelude went from 115 s / 6.7 GB to 0.6 s, and the
   whole module from out-of-memory to 25 s.
3. **Split long runs into one module per path or segment.** `janus_run until [pc]` stops at a join point, a loop head or
   a call; each segment is a separate lemma about the same runtime invariant. RequiredGas on arm64 did not finish in
   13 minutes as one run; split at four join points, the largest piece took 96–125 s.
4. **Cut import chains, not just module times.** A row compiles every module of its import closure that no earlier row
   compiled. Run's operand segments formed a sequential import chain; moving the shared program points and join
   relations into one small module made the segments independent and cut the critical path of the success row from
   1 137 s to about 280 s. Retiring rows whose modules a later row compiles anyway, and removing imports that only
   pulled in an older proof chain, fixed several rows that were over the margin.
5. **Close goals with reducible, exact-shape steps.** `show`/`exact` at default transparency can unfold `readLE` of huge
   memory terms: `with_reducible show` took RequiredGas's final closers from 6 minutes per path to 2–5 s. A failing
   `first | exact … | rfl | …` cascade over many goals is expensive because the failing branches unify state literals;
   prefer one named lemma per goal shape. Give every implicit argument that occurs only in a lemma's conclusion
   explicitly (an unassigned metavariable in a side `omega` cost one amd64 module more than 20 minutes; fixed: 28 s).
6. **Rewrite stack-argument addresses explicitly.** On amd64 a callee precondition reads its stack arguments at
   `sp - 8 + 16`, the caller has them at `sp + 8`; matching these by definitional unification cost 10–20 s each. An
   explicit `rw [show sp - 8 + 16 = sp + 8 by omega]` removes it.
7. **Kernel replay in parallel.** Janus sizes its replay workers by a memory estimate per worker. Our modules replay in at
   most 3 GB with one thread each, so `JANUS_REPLAY_THREADS=1` (the default in `verify-all.sh`) lets four modules replay
   at once under the 16 GB cap. Before, the error row replayed its 50–56 own modules one after another, 147–206 s of a
   545–629 s row.
8. **Profile before changing anything.** `set_option trace.profiler true` on the module and Janus's `janus.omega.log`
   point at the few calls that dominate. Most fixes above came from that, not from guessing.
