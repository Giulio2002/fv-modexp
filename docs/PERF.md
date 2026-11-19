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
**rel50**, Janus v0.3.3 (`6d65752215a09ceaf88d18e2f11bac7bcf19eb82`, binary sha256 `9127bf82…6c193d9d`), fresh cache per ISA,
one row at a time (`ROWS=1`), `JANUS_TIMINGS=1`, 2026-11-15:

| ISA | rows | result | wall (rows + warm-up) | sum of row times | slowest row | largest peak memory |
|---|---|---|---|---|---|---|
| arm64 | 43 | **43/43 PASS** | 9 995 s + 844 s | 9 938 s | `Exp/NRow` 538 s | 5.2 GB (`Top/RunSucc`) |
| amd64 | 37 | **37/37 PASS** | 10 815 s + 894 s | 10 760 s | `NatQ/DrsRowQ` 532 s | 6.1 GB (`NatQ/BasicSqrRowQ`) |

No row exceeded 600 s. Host load (1-minute average) during the rows: median 14.2 (arm64) and 16.6 (amd64), maximum 31.1
and 33.5. The same tree passed `RELEASE=1 scripts/no-sorry.sh` (spec closure: 8 of 8 final rows) and the return-address
pin check (`scripts/check-ra-pin --release`: 43/43 and 37/37 clean).

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
| `Top/RunErr` | 243 / 1624 | 379 / 1306 |
| `Top/RunSucc` | 476 / 5161 | 521 / 4834 |
| `Top/RunTotal` | 79 / 4855 | 83 / 4713 |

The table lists rows by name; the exact order of each ISA is `scripts/release-rows.txt` (`LIST_ONLY=1 scripts/verify-all.sh`
prints it). A dash means the row does not exist on that ISA (see [`COVERAGE.md`](COVERAGE.md)).
<!-- /RELEASE-RUN -->

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
