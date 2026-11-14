# What a human must review to trust the result

The kernel checks the proofs; it cannot check that the *statements* mean what you intend. Review, in this order.

## 1. The specification

### 1a. The reference: EthLib (not ours, not editable)

The MODEXP semantics is `EthLib.Execution.Evm.Precompiles.Modexp` from the pinned package `ethlibspec` (github.com/Giulio2002/EthLib branch
`modexp-spec-lean-v4.34.1` @ `f4756ef5`, a byte-identical copy of ethereum/EthLib@ffd60c4b, see its UPSTREAM.md): `parseLengths`, `checkLengths`, `requiredGas`,
`compute`, `chargedGas`, `modexp`. This project never edits or re-defines it. Read it: it is the specification being proved.

### 1b. `lean/FvModexp/Spec/` (ours: plain definitions the statements use)

A final statement may not use an instance or class of a dependency, so these plain defs replace instance-based notation.
`scripts/check-spec-closure` enforces: statements depend only on `FvModexp.Spec.*`, Janus, `Extracted`, EthLib, and reach no EthLib instance.

| Definition | Meaning, and why it is what it says |
|---|---|
| `Spec.PostFusaka fork` (`Spec/Fork.lean`) | `Fork.fusaka.ctorIdx ≤ fork.ctorIdx` in plain `Nat` order. EthLib's `Fork` order is `ctorIdx` (`instance : LE Fork := ⟨fun a b => a.ctorIdx ≤ b.ctorIdx⟩`); `postFusaka_iff : PostFusaka fork ↔ Fork.fusaka ≤ fork` (and `postFusaka_iff_ge`) are proved by `Iff.rfl`. geth uses the Osaka set from Osaka on (Bogota/Amsterdam reuse it), hence every fork `.fusaka ≤ fork` is covered. |
| `Spec.byteOf m a` (`Spec/Mem.lean`) | The byte at address `a` of the Janus memory `m`, as `UInt8`. |
| `Spec.bytesAt m p n` | The `n` bytes at address `p` as an EthLib `ByteArray`: `data[i] = byteOf m (p+i)`, `i < n`. A Go `[]byte` `(ptr = p, len = n, cap)` IS this call data (the capacity is irrelevant to MODEXP). `bytesAt_size`, `byteAt_bytesAt` relate it to EthLib's total read `byteAt` (zero past the end, "infinite right padding"). |
| `Spec.LengthsPass data` (`Spec/Modexp.lean`) | `checkLengths (parseLengths data) = Except.ok ()`, i.e. EIP-7823: the three length headers are at most 1024. `lengthsPass_iff` gives the explicit form (proved). `LengthsFail = ¬ LengthsPass`. |
| `Spec.OsakaReceiver m p` | The receiver `*bigModExp` at `p` has `eip2565`, `eip7823`, `eip7883` all `true`: the three bytes at `p`, `p+1`, `p+2` equal 1 (field order of `type bigModExp struct`, `core/vm/contracts.go:419`; Go keeps a `bool` as a byte 0/1). A precondition: the theorem says nothing about other receivers. |
| `Spec.u64 x` | A `uint64` result register read as a natural number. For `RequiredGas` the statement is `u64 result = requiredGas fork data (parseLengths data)` as an equality in `Nat`, so the value fits in 64 bits (the proof shows it; for lengths at most 1024 no saturation to `MaxUint64` occurs). |
| `Spec.Precompile`, `Spec.runPrecompiled` (`Spec/Geth.lean`) | geth's `RunPrecompiledContract` logic (`core/vm/contracts.go:272`): `gasCost := RequiredGas(input)`; `gas < gasCost` -> `ErrOutOfGas`; else charge and `Run`; an error from `Run` is passed up. `none` = failed call (the EVM caller then consumes all gas), `some (out, remaining)` = success. Cache and logger paths are not modelled (`cache = nil`, `logger = nil`). |
| `Spec.StkShape` (`Spec/Pool.lean`) | The pooled `*big.stack` object shape the row-1 statements fix for Janus's `sync.(*Pool).Get`/`Put` contracts (`PoolShape` row binder, precondition `S = StkShape`): Janus `SliceObj (2^40-1)` (24-byte header `{ptr, len, cap}`, its array when `cap > 0`), `len = 0` (`stk.free()` stores it before the `Put`), `cap = 0 → ptr = 0`. Byte-identical copy of the proof-side `FvModexp.StkSh` (`rfl`). |
| `Spec.WitSitesArm64.{stkT, mvSite, mkSite, clSite, wbSite, grSite, noSite, getSite, putSite}` (`Spec/WitSitesArm64.lean`) | `stkT`: the `*big.stack` type descriptor (`Extracted.dataAddr`), the `Pool.Put` element type. The `…Site` defs: the call-site premises the arm64 row-1 WITNESS exhibits, one per Janus runtime contract — each the conjunction of that contract's own precondition parts (`…Pre`, `StackRoom`, `LiveAt`/`LiveMemAt`, `LiveDest`, `CallOK`, `R.ok`, `R.inv`, `LiveSep`) at a call. Byte-identical reducible copies of the proof-side `AsmWit` defs (`rfl`). |
| `Spec.WitSitesAmd64.{stkT, mvSite, mkSite, noSite, clSite, wbSite, getSite, grSite, putSite}` (`Spec/WitSitesAmd64.lean`) | amd64 twins of `Spec.WitSitesArm64`: `stkT` (the `*big.stack` type descriptor) and the call-site premises (amd64 argument registers RAX/RBX/RCX/RDI/RSI, `liveWin64`, `CallOK64`, g in R14) the amd64 row-1 witnesses exhibit, one per Janus runtime contract — `mvSite`/`mkSite`/`noSite` by the error witness, all of them by the success witness. Byte-identical reducible copies of the proof-side `Amd64.AsmWit` defs (`Witness/AsmWit.lean`, `Witness/Sites.lean`) and of `Amd64.ModRowW.putSite` (with `stkT`/`StkShape` for `Free.stkT`/`StkSh`); `rfl`. |
| `Spec.RunAmd64.CpuOne m` (`Spec/RunAmd64X.lean`) | APPROVED (coordinator review, top s50) as a precondition conjunct of amd64 `RunSucc.correctness` (row 1, success half) only. Two conjuncts about `math/big` package globals at Run's entry: (1) `m.accessible hasADX 1 false = true` — the 1-byte `hasADX` (`arith_amd64.go:11`: `var hasADX = cpu.X86.HasADX && cpu.X86.HasBMI2`, `.noptrbss`) is READABLE; its VALUE is unconstrained (`addMulVVWW` in `arith_amd64.s` branches on it; both code paths are proved); (2) `Apart (m.readLE natOne 8) 8 divRecursiveThreshold 32` — the 8-byte word `natOne[0]` at the data pointer stored in `natOne`'s slice header (`nat.go:39`: `natOne = nat{1}`, a static array) does not overlap the 32 bytes of the four threshold globals that `Spec.RunAmd64.Globals` describes (distinct package variables). No other constraint (in particular nothing on the return address). Needed because amd64 `(*Int).Mod` / `(*Int).exp` (`ModSpecA` / `ExpSpecA`) read `hasADX` / `natOne`, and neither address is in the extraction's data objects; the witness `Run.WitnessOk.cpu2` discharges it (an 8-byte read-only region at 0xbb6b88 covers `hasADX`). |

## 2. The main theorem statements

* Row 2 `FvModexp.Arm64.RequiredGas.correctness` (`Proofs/Arm64/RequiredGas.lean`; amd64: todo). Arguments `[c, ptr, len, cap]` = receiver
  `*bigModExp` and the input slice. Precondition: the stack-growth check falls through with 464 bytes to spare (`GuardOK s 464`), the stack
  window `[SP-504, SP+40)` is writable (`StackOK s 504 40`; it covers RequiredGas's frame, the callees' frames and the argument spill slots),
  the `SetBytes` jump table is loaded (`DataLoaded`), `len ≤ cap < 2^48`, the `len` input bytes and the 3 receiver bytes are readable and
  apart from the window and from the stack-guard slot, and `Spec.OsakaReceiver s.mem c` (the three `bool` fields are `true`).
  Postcondition (besides the Go ABI, which `Ensures` adds): `∀ fork, Spec.PostFusaka fork → Spec.LengthsPass data →
  Spec.u64 (X0) = requiredGas fork data (parseLengths data)` with `data = Spec.bytesAt s.mem ptr len`. `Ensures` itself gives termination
  without panic or fault for EVERY input (also when the lengths fail EIP-7823). No runtime contract is assumed: `runtime.memmove` is
  executed from its extracted machine code (for the sizes ≤ 32 RequiredGas uses).
  Non-vacuity: `FvModexp.Arm64.RequiredGas.Witness.nonvacuous` (receiver `{1,1,1}`, 96 zero input bytes).
  Intermediate models (proof-internal, not in the statement): `Proofs/Common/GethGas.lean` (geth's `modexpIterationCount`,
  `osakaMultComplexity`, `osakaModexpGas` with uint64 saturation, contracts.go:470-598, proved equal to EthLib `gasCost` under EIP-7823:
  `Geth.osaka_gas_eq`) and `Proofs/Common/RgSpec.lean` (geth's reading of the input: `Uint64()`/`IsUint64()` saturation and `expHead`,
  contracts.go:606-646; `RgSpec.gas_eq` = EthLib `requiredGas`). geth and EthLib agree on every input passing EIP-7823 (no finding).
* Row 1 `FvModexp.<ISA>.Run.correctness` (agent `top`): see its module header.
* Row 3 `FvModexp.Proofs.Compose.composition` (`Proofs/Common/Compose.lean`): pure Lean. From the guarantees of rows 1 and 2 (hypothesis structure `RowsHold`), geth's `runPrecompiled` agrees with EthLib's
  `modexp fork data gas`: failure iff failure (error length bound, or out of gas), otherwise equal outputs and remaining gas `gas - cost` with `cost` = EthLib's `chargedGas`.

## 2b. Return-address pins (final gate; BRIEF "RETURN-ADDRESS PIN GAP")

No Janus release's audit rejects every precondition that constrains the caller's return address (amd64: the word `[RSP]`;
arm64: `X30`; probe forms `/srv/janus-ops/v033/probe/{RspBypass64,LrPin}.lean`). The final gate therefore audits every row
precondition by hand, from the checklist that `scripts/check-ra-pin` generates:

1. `scripts/check-ra-pin --selftest` must print `SELFTEST PASS` (all probe forms c1–c8, d0, e1/e2 + extra spellings are
   FLAGGED, the controls are CLEAN; `scripts/lint-tests/rapin/`).
2. After a full dev build (or with the release oleans), `scripts/check-ra-pin -j 2` elaborates every row's `correctness`,
   unfolds every fv-modexp definition/structure of each Janus form's `pre`, and writes `build/rapin/report.txt`.
3. Every `FLAG` line is a violation unless the reviewer writes down why it is not (expected: none — no row may constrain
   `[RSP]` / `X30` beyond the framework ABI predicates). Then read each row's `RSP-REL` / `STACK-ARG` lines (window bounds and
   stack arguments at `RSP + k`, `k ≥ 8`, are allowed) and its `FRAMEWORK` list (must be Janus ABI/contract predicates only).
4. The tool over-approximates syntactically after unfolding; it is a checklist, not a proof. Anything the tool cannot
   classify (`OPAQUE`, `ERROR`, `NO-FORM`) is reviewed directly in the source.

## 3. Assumptions and limits

* **Toolchain gap.** The binary under verification is built with Go 1.26.10 (Janus-pinned: `GOTOOLCHAIN=go1.26.10`, `CGO_ENABLED=0`, `GOAMD64=v1`, `-trimpath -buildvcs=false`, `scripts/harness.sha256`), because Janus v0.2.0's runtime pins do not
  cover Go 1.27.3, which geth's own release binaries use. geth v1.17.10 itself satisfies the module's `go` directive with 1.26. Verified code = geth v1.17.10 source compiled with 1.26.10, not the shipped release binary. amd64 is verified at `GOAMD64=v1` only.
* **EthLib pin.** The spec is the pinned EthLib revision; if upstream changes the MODEXP spec after `ffd60c4b`, nothing here follows.
* **Runtime contracts** (Janus-pinned, per row in `scripts/contract-flags.sh`): none for RequiredGas.
* Single-threaded execution, non-moving heap, the Go ABI, the harness binary (Janus assumptions, SOUNDNESS.md).
* Modeled `RunPrecompiledContract` is abstract (row 3); the stretch goal of verifying its machine code is not part of the claimed result.

## 4. Non-vacuity

Every main theorem has a kernel-checked `Witness.nonvacuous` (concrete returning run satisfying the precondition) which `janus verify` requires.

## Row 1 runtime assumptions: `RunIface.Serves R` and non-vacuity (agent top, DRAFT 2026-11-11)

`Serves R` (lean/FvModexp/Proofs/Arm64/Top/RunIface.lean) says the runtime serves every request of the Run extraction's
contracts up to: `makeslice` cap ≤ 2^17 elements, `memmove`/`memclrNoHeapPointers` ≤ 2^20 bytes, `growslice` new length
≤ 2^17; `newobject`, write barriers, `sync.Pool` Get/Put unconstrained (no size argument). An unbounded version is not
satisfiable by any Janus stub runtime (the stubs serve fixed / ≤ N sizes) and is not what a real runtime does (huge
requests throw `out of memory`), so it was rejected.

**Request sizes Run can make** (EIP-7823: each operand ≤ 1024 bytes = 128 words; `m` = len(modulus) ≤ 128 words). From the
go-bigmodexpfix code (to be confirmed by the `R.ok` needs of divmc's/expmc's summaries; this table is the review target):

| request | site | worst case |
|---|---|---|
| `make([]byte, n)` | `getData` (Run), `LeftPadBytes` (Run), `(*Int).Bytes` | 1024 B (Bytes: `8·len(abs)` ≤ 1032 B) |
| `nat.make(n)` = `makeslice(Word, n, n+4)` | setBytes (≤ 128), mul/sqr `z.make(len x + len y)` (≤ 256), div `u.make(len+1)`, `q.make(m-n+1)`, Montgomery `zz.make(2m)`, power table 16 × m | ≤ 260 words |
| `(*stack).nat(n)` → `growslice` of the pooled `[]Word` | karatsuba/karatsubaSqr scratch (≈ 3·n·log n words for n ≤ 256), divRecursive scratch | ≤ ~ 10 000 words (estimate) |
| `memmove` | getData/LeftPad copies (≤ 1024 B), `nat.set` / `copy` of nats (≤ 260 words ≈ 2 KiB) | ≤ 2 KiB (stack scratch copies ≤ ~80 KiB) |
| `memclrNoHeapPointers` | `clear(z)` of scratch nats | ≤ ~80 KiB |

The bounds 2^17 elements (1 MiB of words) and 2^20 bytes leave ≥ 10× margin over these estimates.

**Operand bound and budgets of the Int-level callee specs (coordinator decision 2026-11-11, `RunIface` both ISAs).**
`ModSpec`, `ExpSpec`, `BytesSpec` require every operand to have at most `maxW = 128` words (`IntLenLe m a 128`, i.e.
`len(abs) ≤ 128`): EIP-7823 caps each Run operand at 1024 bytes = 128 words, and Run's length check establishes it before
any of these calls (`Run`'s own statement is unaffected). Without the bound the specs are unprovable under the bounded
`Serves R` and a fixed budget (window-4 exponentiation alone reserves `23 · len m` stack words). The budget `B` of each
spec is a closed bound in the operands' word counts (read at the call; a callee proof may consume less, never more).
They are functions of the sizes, not constants for 128 words, so that the `correctness_ok` witness (1-word operands) fits
the Janus toy runtime's heap (budgets up to 2^22):

| constant | value | derivation |
|---|---|---|
| `opCost w` | `allocCost (1024 w + 1024)` | a request of a callee with operands of at most `w` words is at most `64 w + 64` words (window-4 `stk.reserve(23 · len m)`, Karatsuba / recursive-division scratch of `2 len m`-word products, `nat.make` results), at most doubled by `growslice`: a block of at most `1024 w + 1024` bytes; `blockSize_le_allocCost` |
| `ModBudget w` | `64 · opCost w` | `z.Mod(z, y)`, `w = max(len z, len y)`: `nat.make` of `u` (len x + 1), `q`, `z`; `getStack`; `(*stack).nat` scratch of `divLarge` / `divRecursiveStep` (w ≤ 128 ≥ divRecursiveThreshold 40: ≤ 4 blocks, depth ≤ 2) — under 64 requests |
| `ExpBudget w yW` | `(8 · 64 yW + 128) · opCost w` (= `BudQ.ExpBudgetF`; `RunSucc.expBudget_eq … := rfl`) | `z.exp(z, y, m, false)`, `w = max(len z, len y, len m)`, `yW = len y`: ≤ `64 yW` exponent bits; per bit at most one `sqr`, one `mul`, one reduction (`div` or `montgomery`), each with ≤ 2 allocating requests (its `nat.make` result when the capacity is short, `(*stack).nat` scratch): ≤ 8 per bit; setup ≤ 128 (power table 16 entries, `stk.reserve`, `m1 m2 z1 z2` of `expNNEven`, `lsh`, `getStack`). The per-bit allowance lets a loop invariant charge each iteration a constant without tracking capacities. NO SLACK FACTOR (top s40, commit 3e3c02b): the former temporary `2^32 · min w 1` factor is removed on both ISAs (Spec `okBudget` and `RunIface.ExpBudget`); the proved cost envelopes of the `nat` chain fit this formula (`BudQ.budOK` from the owners' per-term targets; numeric mirror scripts/gen/exp-budget-check.py transcribes the factor-free Lean definitions). CHANGE AT `w = 0`: with `min w 1` gone, the all-zero-lengths case (`Run` returns before any `Mod`/`exp` call) now has the exp allowance `128 · opCost 0` in `okBudget` instead of `0` — a slightly looser (larger) budget premise there; it is still a finite closed bound and no proof consumes it |
| `BytesBudget w` | `allocCost (8 w)` | `x.Bytes()`, `w = len x`: one `make([]byte, 8 w)` |

For 128-word operands: `opCost 128 ≈ 2.64e5 ≈ 2^18`, `ExpBudget 128 128 = 65664 · opCost 128 ≈ 1.73e10 ≈ 2^34.01` (`RunSucc.expBudget_gate : RunIface.ExpBudget 128 128 ≤ 2^35`, from `BudQ.gate`). For one-word operands the whole success
budget fits the Janus toy runtime's heap (`≤ 2^22`), so the success witness runs a real exponentiation.
**RELEASE GATE "TIGHT COSTS" (coordinator decision 2026-11-15)** requires (a) `RunIface.ExpBudget` / Spec `okBudget` ≤ `2^35`
bytes (32 GiB) over the whole spec range (operands and exponent ≤ 128 words) and (b) success witnesses on BOTH ISAs that run a
real exponentiation (`3^5 mod 7`) inside the toy runtime's `2^22` budget.
* **arm64: MET** (top s40, commit 3e3c02b): factor-free `ExpBudget := BudQ.ExpBudgetF`, Spec/RunArm64 `okBudget` without the
  `2^32 · min w 1` factor, `RunSucc.correctness` without the former budget premise `hbud`, `RunSucc.expBudget_gate`, and the
  premise-free `RunSucc.Witness.nonvacuous` running `Run` on `3^5 mod 7` (output `[5]`, budget checked by `decide +kernel`).
  Janus row verification of `Top_RunSucc` (arm64): see docs/COVERAGE.md.
* **amd64: PENDING** — the statement side is done (Spec/RunAmd64 `okBudget` and amd64 `RunIface.ExpBudget` factor-free,
  same commit), but the amd64 `RunSucc` success witness (`3^5 mod 7`) waits for the amd64 `Mod`/`exp` providers (IMod/IExp);
  until it exists the gate is not met on amd64 and amd64 success-row timings are PROVISIONAL.
* The `w = 0` change (all three lengths `0`): `okBudget` now includes `128 · opCost 0` for `exp` where the factor made it `0`;
  the bound is slightly looser there (the code allocates nothing for `Mod`/`exp` on that path).
If a callee proof finds a request count above an allowance it reports it here and the constant is raised (never the proof
weakened). Request sizes stay as in the table above.

**Non-vacuity plan (coordinator requirement, open):**
1. `correctness` (full row-1 statement) — `Witness.nonvacuous` runs the EIP-7823 error path (no `Serves` needed there).
2. `correctness_ok` (same statement restricted to `LengthsPass data`, `Serves R` in its precondition) — `Witness.correctness_ok`
   runs a small success input (base 3, exp 5, mod 7 → `0x05`) to the return. Its runtime must satisfy the bounded `Serves R`:
   this needs witness stubs that serve EVERY size up to the bound (a looping `memmove`/`memclr`, a general `growslice`,
   bump `makeslice` for any cap ≤ 2^17, `Pool.Get` returning nil, `Pool.Put` dropping), proved against the live contracts —
   Janus' stub library only has fixed-size / ≤N-size copies. Work item for top (or infra), tracked in NOTES-top.md.
3. Satisfiability of `Serves R` for the worst case (requirement (a)) follows from 2's stubs: they serve every request up to the
   bounds, sized with a heap ≥ the Run budget.

## 5. Tactic-definition files (`scripts/tactic-whitelist.txt`)

Metaprogramming (`macro`/`elab`/`syntax`/non-proof attributes) is rejected by `scripts/lint_source.py` outside the files listed in
`scripts/tactic-whitelist.txt` (sha256-pinned: under RELEASE a changed file fails until it is re-reviewed and the whitelist regenerated).
Tactics cannot weaken a result (the kernel checks every proof term; `#print axioms` / `janus verify` see any axiom), but a
metaprogram could do IO or tamper with the environment, so each listed file was read. Review (infra s7, 2026-11-11):

| file | constructs | verdict |
|---|---|---|
| Common/GenReg.lean | `gen_reg` (generalize a register value) | proof tactic only (earlier review) |
| Common/AsmTac.lean | macros `same_tac`, `same64_tac` (`obtain`/`refine`/`rfl`/`janus_simp`/`exact`) | proof tactics only; no IO, axioms, env changes |
| Common/Util.lean (adapted fv-uint256) | `partial def collectDecToNat` (pure `Expr` traversal), `elab dec_facts` / `dec_goal` (for each `(decide p).toNat` run `have := FvModexp.Util.dec_toNat p`) | proof tactics only; read-only `MetaM`/`TacticM` (`getMainTarget`, `getLCtx`, `evalTactic` of a `have`); no IO, axioms, `addDecl`, env changes |
| Arm64/RequiredGas/Defs.lean, Amd64/RequiredGas/Defs.lean | macro `dl_close` (`dsimp`/`assumption`/`DataLoaded.writeLE`) | proof tactic only |
| Arm64/RequiredGas/Pre.lean, Amd64/RequiredGas/Pre.lean | macros `rg_byte`, `rg_byte64` (`unfold`/`split`/`omega`/`simp only`/`exact` over lemmas of the same file) | proof tactics only |
| Arm64/Exp/Mont.lean, Amd64/Exp/Mont.lean | `local macro` `slotv`, `inputv` (`rw`/`simp only`/`omega`) | proof tactics only |
| Arm64/Witness/StubsGrow.lean, Amd64/Witness/StubsGrow.lean | macros `pre0_tac`, `ck_tac`, `ck2_tac` (`refine`/`rfl`/`assumption`/`simp`) | proof tactics only |
| Arm64/Witness/StubsMem.lean | macro `kp_tac` (same pattern) | proof tactics only |

Any later change to one of these files must be re-reviewed (diff) before `scripts/lint_source.py --update-whitelist`.
