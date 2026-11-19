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
| `Spec.Precompile`, `Spec.runPrecompiled p input gas cache` (`Spec/Geth.lean`) | geth's `RunPrecompiledContract` logic (`core/vm/contracts.go:272-304`): `gasCost := RequiredGas(input)`; `gas < gasCost` -> `ErrOutOfGas`; else charge; with a cache attached and a cache key, a stored output is returned (`err == nil`, same gas accounting); otherwise `Run`, and an error from `Run` is passed up (the store on a miss does not change the result). `none` = failed call (the EVM caller then consumes all gas), `some (out, remaining)` = success. `cache` defaults to `none` (`cache == nil`). The logger and the Amsterdam access-list `Touch` do not change the result and are not modelled. |
| `Spec.normalize`, `Spec.cacheKey` (`Spec/Geth.lean`) | geth's MODEXP cache key: `normalize` transcribes `(*bigModExp).NormalizeInput` (contracts.go:704-732: input of at most 96 bytes unchanged; a length header `≥ 2^64` -> not cacheable; base and modulus lengths 0 -> the 96-byte header; else the input cut to `96 + b + e + m` bytes unless that sum overflows `uint64` or is at least the input size), `cacheKey` adds `precompileCacheKey`'s cap (precompile_cache.go:223-238: key over `maxCacheablePrecompileInput = 8192` bytes -> not cacheable). `getData(input, k, 32)` on an input longer than 96 bytes is `readNat input k 32`; the `uint256` sum of three `< 2^64` values cannot wrap. |
| `Spec.Cache`, `Spec.cacheHit`, `Spec.CacheStoredBy p cache` (`Spec/Geth.lean`) | `Cache = Option (ByteArray → Option ByteArray)`: `none` = `cache == nil`, `some lookup` = the entries of this call's scope (active precompile set, address), `lookup key` = `cache.load` (a copy). `cacheHit` = the lookup of contracts.go:290-294 (needs a cache AND a key). `CacheStoredBy` (row 3 hypothesis) = what geth's stores guarantee: every entry `key ↦ out` was stored after `p.Run(d')` returned `out` with `err == nil` for some `d'` with `cacheKey d' = some key` (contracts.go:296-299; `store` copies key and output, precompile_cache.go:158-176). Concurrency/eviction only remove entries and keep this invariant. |
| `Spec.StkShape` (`Spec/Pool.lean`) | The pooled `*big.stack` object shape the row-1 statements fix for Janus's `sync.(*Pool).Get`/`Put` contracts (`PoolShape` row binder, precondition `S = StkShape`): Janus `SliceObj (2^40-1)` (24-byte header `{ptr, len, cap}`, its array when `cap > 0`), `len = 0` (`stk.free()` stores it before the `Put`), `cap = 0 → ptr = 0`. Byte-identical copy of the proof-side `FvModexp.StkSh` (`rfl`). |
| `Spec.WitSitesArm64.{stkT, mvSite, mkSite, clSite, wbSite, grSite, noSite, getSite, putSite}` (`Spec/WitSitesArm64.lean`) | `stkT`: the `*big.stack` type descriptor (`Extracted.dataAddr`), the `Pool.Put` element type. The `…Site` defs: the call-site premises the arm64 row-1 WITNESS exhibits, one per Janus runtime contract — each the conjunction of that contract's own precondition parts (`…Pre`, `StackRoom`, `LiveAt`/`LiveMemAt`, `LiveDest`, `CallOK`, `R.ok`, `R.inv`, `LiveSep`) at a call. Byte-identical reducible copies of the proof-side `AsmWit` defs (`rfl`). |
| `Spec.WitSitesAmd64.{stkT, mvSite, mkSite, noSite, clSite, wbSite, getSite, grSite, putSite}` (`Spec/WitSitesAmd64.lean`) | amd64 twins of `Spec.WitSitesArm64`: `stkT` (the `*big.stack` type descriptor) and the call-site premises (amd64 argument registers RAX/RBX/RCX/RDI/RSI, `liveWin64`, `CallOK64`, g in R14) the amd64 row-1 witnesses exhibit, one per Janus runtime contract — `mvSite`/`mkSite`/`noSite` by the error witness, all of them by the success witness. Byte-identical reducible copies of the proof-side `Amd64.AsmWit` defs (`Witness/AsmWit.lean`, `Witness/Sites.lean`) and of `Amd64.ModRowW.putSite` (with `stkT`/`StkShape` for `Free.stkT`/`StkSh`); `rfl`. |
| `Spec.RunAmd64.CpuOne m` (`Spec/RunAmd64X.lean`) | A precondition conjunct of the amd64 row-1 success theorem (`RunSucc.correctness`, and through it `Run.correctness_total`) only. Two conjuncts about `math/big` package globals at Run's entry: (1) `m.accessible hasADX 1 false = true` — the 1-byte `hasADX` (`arith_amd64.go:11`: `var hasADX = cpu.X86.HasADX && cpu.X86.HasBMI2`, `.noptrbss`) is READABLE; its VALUE is unconstrained (`addMulVVWW` in `arith_amd64.s` branches on it; both code paths are proved); (2) `Apart (m.readLE natOne 8) 8 divRecursiveThreshold 32` — the 8-byte word `natOne[0]` at the data pointer stored in `natOne`'s slice header (`nat.go:39`: `natOne = nat{1}`, a static array) does not overlap the 32 bytes of the four threshold globals that `Spec.RunAmd64.Globals` describes (distinct package variables). No other constraint (in particular nothing on the return address). Needed because amd64 `(*Int).Mod` / `(*Int).exp` (`ModSpecA` / `ExpSpecA`) read `hasADX` / `natOne`, and neither address is in the extraction's data objects; the witness `Run.WitnessOk.cpu2` discharges it (an 8-byte read-only region at 0xbb6b88 covers `hasADX`). |
| `Spec.RunArm64.fn` (`Spec/RunArm64.lean`) | The literal symbol `github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run`; `segAddr Extracted.program fn` is its entry in the extraction. |
| `Spec.RunArm64.window s` | The error row's stack window `[SP-4800, SP+40)`: Run's 624-byte frame + the deepest header-phase callee frame (`nat.setBytes`, 4160) below `SP`, and the return slot + the 4 argument words above. Only the proofs write inside it. |
| `Spec.RunArm64.Env R L s` | Error-row environment: `GuardOK s 4800` (the stack-growth prologues fall through, see §3 "Stack growth"), `StackOK s 4800 40` (`SP` 16-aligned, window writable), `DataLoaded` (the extraction's 48 data segments, all `.rodata`, hold their bytes: true in every process running the binary), the window and g's `stackguard0` word (`X28+16`) outside the runtime-owned ranges `R.rt` and apart, no caller live object in the window (`LiveSep`), `.rodata` outside `R.rt`. A modelling choice of the runtime invariant `R`; no real allocator invariant concerns these addresses. |
| `Spec.RunArm64.Held R L a n` | `[a, a+n)` is program memory: inside a live object of `L`, or outside `R.rt`. |
| `Spec.RunArm64.Input R L c p len cp s` | The receiver's 3 bytes and the `[]byte` `(p, len, cap)` are a real Go slice: `len ≤ cap < 2^48`, readable, `Held`, and not in the window (a caller never passes free stack below its `SP`). |
| `Spec.RunArm64.blockBound n` | `2n + 24`: the cost the budget charges for one runtime block of `n` bytes (any size class, rounding at most doubles, plus a header allowance). An abstract monotone quantity (Janus RUNTIME-CONTRACTS: no GC credit), not a measurement. |
| `Spec.RunArm64.wordT`, `errT` | The extraction's addresses of `type:big.Word` (element type of `nat.make`) and `type:errors.errorString` (the `errors.New` object). |
| `Spec.RunArm64.ErrReqs R b len` | The runtime serves the error path's requests: `makeslice(Word, 4, 8)` (three header `nat.make(4)`), the short-input `memmove` copies `n ≤ 32` (only when `len < 96`), `newobject(errorString)`; budget `b ≥ 3·blockBound 64 + blockBound 16 = 512`. Any real runtime serves these (tiny requests). |
| `Spec.RunArm64.Grows R L L'` | The live set only grows by runtime-allocated objects (inside `R.rt`, apart from `L` and from each other). |
| `Spec.RunArm64.Frame R b B L s s'` | Error-row frame: the live set grows, the budget drops by at most `B`, `R.inv` holds again, only `R.rt` and the window changed (`MemFrame`), the caller's live objects are byte-identical (`LiveFrame`). |
| `Spec.RunArm64.ErrRet s'` | `(nil, err)` with `err ≠ nil`: arm64 ABIInternal results X0..X4 = (ptr, len, cap, itab, data); `X0 = X1 = 0` is the nil `[]byte`, `X3 ≠ 0` a non-nil interface (its type word). |
| `Spec.RunArm64.windowW s W` | The success row's window `[SP-W, SP+40)`; the theorem needs `W ≥ 624 + 72944 = 73568` (Run's frame + `(*Int).exp`'s proved window, the deepest callee chain: window-4 Montgomery with its `nat` callees). |
| `Spec.RunArm64.EnvW R L s W` | `Env` with window `W`, plus: g's `stackguard0` word is apart from every caller live object (it lives in the runtime's `g` struct, never in a Go object of the caller). |
| `Spec.RunArm64.OkReqs R` | "No out-of-memory" for the success path: `makeslice` cap ≤ 2^17 elements, `memmove`/`memclrNoHeapPointers` ≤ 2^20 bytes, `growslice` new length ≤ 2^17; `newobject`, write barriers 2/4 and `Pool.Get/Put` unconstrained (no size). The bounds are ≥ 10× the largest request operands ≤ 1024 bytes can cause (table below); an unbounded version is not satisfiable by any runtime (huge requests throw "out of memory"). |
| `Spec.RunArm64.Globals R m w` | `math/big`'s writable thresholds at their Go initial values (`karatsubaThreshold = 40`, `basicSqrThreshold = 12`, `karatsubaSqrThreshold = 80` natmul.go:12,68,69; `divRecursiveThreshold = 40` natdiv.go:733; 32 contiguous bytes) and `runtime.writeBarrier`'s flag word (ANY value): readable, outside `R.rt` and the windows. Only `calibrate_test.go` writes the thresholds (no non-test writer, grep). The three address equalities are closed facts about the binary (true; the witness proves them). |
| `Spec.RunArm64.NatOne R m w` | `natOne = nat{1}` (nat.go:39, never written) at its initial value: header `(op, 1, 1)` and `op[0] = 1`, readable, outside `R.rt` and the windows. |
| `Spec.RunArm64.StackPool R m w` | `var stackPool sync.Pool` (nat.go:282) with `New` never set (word 0), outside `R.rt` and the windows; and address 0 is not runtime memory (page 0 unmapped). `getStack` = `stackPool.Get()`, nil → `new(stack)` (nat.go:286-298). |
| `Spec.RunArm64.okBudget l` | The success budget from the three lengths: headers + 3 operand reads + `Mod` (64 requests) + `exp` (`8·64·⌈e/8⌉ + 128` requests) + `Bytes` + `LeftPadBytes`, each request charged `blockBound (1024w + 1024)` (`w` = largest operand in words). Factor-free (no `2^32` slack), sound, NOT tight (≈30-60× real allocation volume); `RunGate.okBudget_gate`: ≤ 2^35 for every input passing EIP-7823 (corner value 17 366 406 472). Derivation: "Row 1 budgets" below. |
| `Spec.RunArm64.OkRet data s'` | `(out, nil)`: `X3 = 0` (nil error type word) and the `X1` bytes at `X0` are exactly `compute data (parseLengths data)` (EthLib). |
| `Spec.RunArm64.FrameW R b B L W s s'` | `Frame` with window `W`, plus: the output bytes are program memory (`Held` in the grown live set) when non-empty. |
| `Spec.RunAmd64.*` (`Spec/RunAmd64.lean`) | amd64 twins of every `Spec.RunArm64` definition above, same meaning: SP = `RSP` (`regs 4`), g = `R14`, `StackGuardOK`/`StackWritable` + `RSP % 8 = 0`, ABIInternal results RAX/RBX/RCX/RDI/RSI; `window` 4800/40, Run's frame 616. `okBudget` is the same formula (`Amd64.RunGate.okBudget_gate`). |

## 2. The main theorem statements

* Row 2 `FvModexp.Arm64.RequiredGas.correctness` (`Proofs/Arm64/RequiredGas.lean`) and `FvModexp.Amd64.RequiredGas.correctness`
  (`Proofs/Amd64/RequiredGas.lean`). Arguments `[c, ptr, len, cap]` = receiver
  `*bigModExp` and the input slice. Precondition: the stack-growth check falls through with 464 bytes to spare (`GuardOK s 464`), the stack
  window `[SP-504, SP+40)` is writable (`StackOK s 504 40`; it covers RequiredGas's frame, the callees' frames and the argument spill slots),
  the `SetBytes` jump table is loaded (`DataLoaded`), `len ≤ cap < 2^48`, the `len` input bytes and the 3 receiver bytes are readable and
  apart from the window and from the stack-guard slot, and `Spec.OsakaReceiver s.mem c` (the three `bool` fields are `true`).
  Postcondition (besides the Go ABI, which `Ensures` adds): `∀ fork, Spec.PostFusaka fork → Spec.LengthsPass data →
  Spec.u64 (X0) = requiredGas fork data (parseLengths data)` with `data = Spec.bytesAt s.mem ptr len`. `Ensures` itself gives termination
  without panic or fault for EVERY input (also when the lengths fail EIP-7823). No runtime contract is assumed: `runtime.memmove` is
  executed from its extracted machine code (for the sizes ≤ 32 RequiredGas uses).
  The amd64 twin states the same with `StackGuardOK s 456`, `StackWritable s 496 40`, the `R14`-relative guard slot and the
  return-address slot `[RSP]` readable.
  Non-vacuity: `RequiredGas.Witness.nonvacuous` on each ISA (receiver `{1,1,1}`, 96 zero input bytes).
  Intermediate models (proof-internal, not in the statement): `Proofs/Common/GethGas.lean` (geth's `modexpIterationCount`,
  `osakaMultComplexity`, `osakaModexpGas` with uint64 saturation, contracts.go:470-598, proved equal to EthLib `gasCost` under EIP-7823:
  `Geth.osaka_gas_eq`) and `Proofs/Common/RgSpec.lean` (geth's reading of the input: `Uint64()`/`IsUint64()` saturation and `expHead`,
  contracts.go:606-646; `RgSpec.gas_eq` = EthLib `requiredGas`). geth and EthLib agree on every input passing EIP-7823 (no finding).
* Row 1, arm64 (`Proofs/Arm64/Top/RunSucc.lean`, `Proofs/Arm64/Top/RunErr.lean`; both release rows). Arguments `[c, p, len, cp]` =
  receiver `*bigModExp` and the input slice; `data = Spec.bytesAt s.mem p len`.
  * **`FvModexp.Arm64.RunSucc.correctness`** (lengths pass). Premises: `ImplApart` + the 11 runtime-contract instances of §3
    ("Runtime contracts"), the Pool shape binder `S` (fixed by the pre `S = StkShape`), `W ≥ 624 + 72944`. Pre: `EnvW`, `Input`,
    `OsakaReceiver`, `R.inv b L g`, `OkReqs`, `Globals`, `NatOne`, `StackPool` (on `windowW s W`), `okBudget (parseLengths data) ≤ b`,
    `LengthsPass data`. Post (besides the Go ABI, which `Ensures` adds): `OkRet data s'` (`(compute data (parseLengths data), nil)`)
    and `FrameW … (okBudget …) …`. Witness: `FvModexp.Arm64.RunSucc.Witness.nonvacuous` (toy runtime, heap 2^22, window 0x20000,
    one call-site state per contract, a real `3^5 mod 7` run, output `[5]`).
  * **`FvModexp.Arm64.Run.correctness`** (lengths fail). Premises: `ImplApart`, `MakesliceLiveContract`, `MemmoveLive`,
    `NewobjectLiveContract`. Pre: `Env`, `Input`, `OsakaReceiver`, `R.inv`, `ErrReqs R b len`, `LengthsFail data`. Post: `ErrRet s'`
    (`(nil, err)`, `err ≠ nil`) and `Frame … 512 …`. Witness: `FvModexp.Arm64.Run.Witness.nonvacuous` (base-length header 1025).
  * **`FvModexp.Arm64.Run.correctness_total`** (`Proofs/Arm64/Top/RunTotal.lean`, its own release row `arm64 Top/RunTotal`): the row-1
    sentence as ONE theorem. RunSucc's premises and pre without `LengthsPass`, the budget only when the lengths pass
    (`LengthsPass data → okBudget … ≤ b`) plus `512 ≤ b`; post `(LengthsPass ∧ OkRet ∧ FrameW) ∨ (LengthsFail ∧ ErrRet ∧ Frame)`.
    Proved by cases from the two rows (`env_of_envW`, `errReqs_of_okReqs`); `Run.Witness.correctness_total` from the success witness.
  * Release gates on the statement: `FvModexp.Arm64.RunGate.okBudget_gate` (`LengthsPass data → okBudget (parseLengths data) ≤ 2^35`,
    `Proofs/Arm64/Top/RunGate.lean`; amd64 twin `FvModexp.Amd64.RunGate.okBudget_gate`), `RunSucc.expBudget_gate`
    (`ExpBudget 128 128 ≤ 2^35`); the return-address pin check (§2b) is clean on every release row. Build target: each ISA's `Top/RunSucc`
    row module imports its `Top/RunGate`, so the release run (`janus verify` of the RunSucc rows) compiles and kernel-checks both gates.
    `RunTotal` imports RunSucc + RunErr, so no row module can import it; it is compiled and checked by its own release row
    `Top/RunTotal` on each ISA, after `Top/RunSucc`; the default `lake build FvModexp` is extraction-free and cannot import any `Extracted`-based module.
* Row 1, amd64 (`Proofs/Amd64/Top/RunErr.lean`, `Proofs/Amd64/Top/RunSucc.lean`): `FvModexp.Amd64.Run.correctness` (lengths fail,
  release row, `Spec.RunAmd64` twins) and `FvModexp.Amd64.RunSucc.correctness` (lengths pass, `Spec.RunAmd64` twins + `Spec.RunAmd64.CpuOne` (§1b); every
  machine-code callee proved: `(*Int).Mod` = `Run.Closed.modA`, `(*Int).exp` = `Run.Closed.expA` = `IExp.ensCl`
  (depth 43 736), premises = eleven Janus runtime-contract hypotheses over nine runtime functions (§3 table, `…64` / `PoolAmd64`
  amd64 variants), the Pool shape binder `S` (pre `S = StkShape`),
  `W ≥ 616 + 43736 = 44 352`), with `RunSucc.Witness.nonvacuous` (`3^5 mod 7`, output `[5]`).
  **`FvModexp.Amd64.Run.correctness_total`** (`Proofs/Amd64/Top/RunTotal.lean`, release row `amd64 Top/RunTotal`): the twin of the
  arm64 total theorem (success environment incl. `CpuOne`, budget only under `LengthsPass`, plus `512 ≤ b`; post `(LengthsPass ∧ OkRet ∧
  FrameW) ∨ (LengthsFail ∧ ErrRet ∧ Frame)`), with `Run.Witness.correctness_total` from the amd64 success witness.
* Row 3 `FvModexp.Proofs.Compose.composition` (`Proofs/Common/Compose.lean`): pure Lean. From the guarantees of rows 1 and 2 (hypothesis structure `RowsHold`), for every
  result cache `cache` meeting `CacheStoredBy p cache` (`cacheStoredBy_none`: `cache == nil` does), geth's `runPrecompiled p data gas cache` agrees with EthLib's
  `modexp fork data gas`: failure iff failure (error length bound, or out of gas), otherwise equal outputs and remaining gas `gas - cost` with `cost` = EthLib's `chargedGas`.
  Cache step: `cacheHit_run` (a hit equals `Run data`, via `CacheKey.cacheKey_eq`) and `runPrecompiled_cache` (with such a cache = without one). Converse: `error_of_fail`.

## 2b. Return-address pins

No Janus release's audit rejects every precondition that constrains the caller's return address (amd64: the word `[RSP]`;
arm64: `X30`; Janus v0.3.3's probe forms `RspBypass64`, `LrPin`, reproduced in `scripts/lint-tests/rapin/`). The release therefore audits every row
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

* **Toolchain gap.** The binary under verification is built with Go 1.26.10 (Janus-pinned: `GOTOOLCHAIN=go1.26.10`, `CGO_ENABLED=0`,
  `GOAMD64=v1`, `-trimpath -buildvcs=false`, `scripts/harness.sha256`), because the Janus runtime pins (framework **Janus v0.3.3**,
  tag 6d657522, the lakefile pin) do not cover Go 1.27.3, which geth's own release binaries
  use. geth v1.17.10 itself satisfies the module's `go` directive with 1.26. Verified code = geth v1.17.10 source compiled with
  1.26.10, not the shipped release binary. amd64 is verified at `GOAMD64=v1` only.
* **EthLib pin.** The spec is the pinned EthLib revision; if upstream changes the MODEXP spec after `ffd60c4b`, nothing here follows.
* **Runtime contracts** (Janus-pinned, `scripts/contract-flags.sh`). RequiredGas (row 2): none. Run (row 1): the extraction treats 12
  runtime functions as contracts (`--contract`): `runtime.gcWriteBarrier{1,2,3,4,6}`, `growslice`, `makeslice`,
  `memclrNoHeapPointers`, `memmove`, `newobject`, `sync.(*Pool).Get`, `sync.(*Pool).Put`. The theorems assume Janus's pinned
  contract for each one the proved code calls, at frame size 4096, with one runtime invariant `R`:
  | premise | Janus contract | why a real runtime satisfies it |
  |---|---|---|
  | `hmk` | `MakesliceLiveContract` | `makeslice` returns a fresh zeroed object of `typ.size·cap` bytes in `R.rt`, apart from the live set, or throws (excluded by `OkReqs`) |
  | `hmkz` | `MakesliceZeroLive` | zero-size request returns the `zerobase` pointer, nothing allocated (malloc.go) |
  | `hmv` | `MemmoveLive` | `memmove` copies `n` bytes, writes only `[dst, dst+n)` |
  | `hmz` | `MemmoveZeroLive` | `n = 0` touches nothing |
  | `hno` | `NewobjectLiveContract` | `newobject(typ)` = `mallocgc(typ.size, typ, true)`: fresh zeroed object |
  | `hgr` | `GrowsliceLiveContract` | `growslice` returns a fresh array holding the old elements, new cap ≥ new length |
  | `hmc` | `MemclrNoHeapPointersLive` | clears exactly `[p, p+n)` |
  | `hwb` / `hwb4` | `WbLiveContract … 2` / `… 4` | the write-barrier buffer slots (2 / 4 pointers) are runtime memory; the barrier changes nothing the program can read |
  | `hget` / `hput` | `PoolGetLive` / `PoolPutLive` at `PoolShape = StkShape` | `Get` returns nil or an object this package `Put` (always a `*stack` with `len 0`, `cap = 0 → ptr = 0`: `free()` sets len 0, `slices.Grow(nil, 0)` stays nil); `Put` hands the object to the pool |
  `gcWriteBarrier1/3/6` are contract addresses of the extraction that the proved paths never reach (a call would need their contract).
* **Stack growth and preemption are NOT modelled.** Every callee prologue's stack check is proved to
  fall through; `runtime.morestack` is never executed. The theorems therefore cover only calls where, at entry,
  `SP − g.stackguard0 > 73 568` bytes (arm64 success: `GuardOK s W`, `W ≥ 624 + 72944`; arm64 error: `> 4 800`, `GuardOK s 4800`) and
  `stackguard0` is not the `stackPreempt` sentinel (no pending preemption request: `GuardOK` is false then). Row 2 (RequiredGas): arm64 `> 464` bytes (`GuardOK s 464`), amd64 `> 456` bytes (`StackGuardOK s 456`). amd64: error row
  `> 4 800` (`StackGuardOK s 4800`); success row `> 44 352` bytes (`StackGuardOK s W`, `W ≥ 616 + 43736`: Run's 616-byte frame + the closed
  amd64 `(*Int).exp` window 43 736, which covers `(*Int).Mod`'s 41 800). Derivation of 43 736: it is the
  summary-composition window of amd64 `(*Int).exp`, `IExp.ensCl` (`Proofs/Amd64/Exp/IExpCl.lean`) = `K + 0x5d0` with `K = 42 248`
  (`K` = the window handed to the inner `nat.expNN` call, `0x5d0` = the stack `(*Int).exp` and its frames use above it);
  `K ≥ 42 248` is forced by the largest callee window inside `nat.expNN` (`IExp.evH`, `Proofs/Amd64/Exp/IExpClD.lean`: the `expNNEven` call needs `ExpEven.stkE 41 640 = 43 152`
  bytes; the other callee windows are smaller: div 41 512, expNNSlow 41 952, p2 42 520, rem 41 720), and those windows bottom out in
  the runtime contracts, each of which reserves a flat 4 096 bytes below its caller's SP. So 43 736 is an upper bound the proof
  uses, NOT a measured Go stack depth (arm64 needs 72 944 for the same Go code: much of either figure is proof-side margin); a
  real call with less free stack is outside the claim, as stated below. A
  goroutine with less free stack (Go grows stacks on demand: a fresh 8 KiB stack, or a 32/64 KiB stack partly used by the EVM
  interpreter) or with a pending preemption calls morestack in real geth, which copies the stack / preempts and then continues
  with the same result; that continuation is outside the claim. Lifting this needs a `morestack` contract, which Janus v0.3.3 does not provide.
* **Precompile result cache (row 3 scope).** geth v1.17.10 attaches a precompile result cache by default
  (`core/blockchain.go:417-420`; `RunPrecompiledContract` contracts.go:289-301): on a hit for key `NormalizeInput(input)` it returns
  the stored output without running `Run` (gas is charged before the lookup, hit or miss). `Spec.runPrecompiled` models
  this cache (`cache` argument, `Spec.cacheKey` = a transcription of `NormalizeInput` + the 8192-byte cap of `precompileCacheKey`),
  and row 3 holds for every cache meeting `Spec.CacheStoredBy`. Soundness is proved in pure Lean: `FvModexp.CacheKey.cacheKey_sound` /
  `cacheKey_eq` (`Proofs/Common/CacheKey.lean`): equal keys give equal `LengthsPass` verdicts and equal `compute` outputs, and only
  `err == nil` results are stored, so a hit returns exactly what row 1 proves `Run` returns for the actual input
  (`Compose.cacheHit_run`). Remaining assumption: geth's cache only holds what its stores put there (`CacheStoredBy`, §1).
* **Single-threaded execution**, non-moving heap, the Go ABI, the harness binary (Janus's assumptions, its `SOUNDNESS.md`). Concretely, values
  another goroutine or the GC could change during the call are assumed stable: `runtime.writeBarrier` (any value at entry, but GC
  phase changes flip it), `math/big.stackPool` (another goroutine's `Put` between our `Get`/`Put`), and g's `stackguard0` (see
  "Stack growth").
* Modeled `RunPrecompiledContract` is abstract (row 3); the stretch goal of verifying its machine code is not part of the claimed result.

## 4. Non-vacuity

Every main theorem has a kernel-checked `Witness.nonvacuous` (concrete returning run satisfying the precondition) which `janus verify`
requires: row 2 `RequiredGas.Witness.nonvacuous`, row 1 arm64 `RunSucc.Witness.nonvacuous` (`3^5 mod 7` → `[5]`) and
`Run.Witness.nonvacuous` (header 1025), amd64 `RunSucc.Witness.nonvacuous` (`3^5 mod 7` → `[5]`) and `Run.Witness.nonvacuous` (header 1025); `Run.correctness_total` (both ISAs) has
`Run.Witness.correctness_total`. Optional extra coverage witnesses (`b = m = 0`, `mod = 0`, `base = 1`) are not required.

## Row 1 budgets and request sizes (derivation of `OkReqs` and `okBudget`)

**Request sizes Run can make** (EIP-7823: each operand ≤ 1024 bytes = 128 words). From the go-bigmodexpfix code; the proved
callee summaries' `R.ok` needs stay within `OkReqs`' bounds (otherwise the proofs would not close):

| request | site | worst case |
|---|---|---|
| `make([]byte, n)` | `getData` (Run), `LeftPadBytes` (Run), `(*Int).Bytes` | 1024 B (Bytes: `8·len(abs)` ≤ 1032 B) |
| `nat.make(n)` = `makeslice(Word, n, n+4)` | setBytes (≤ 128), mul/sqr `z.make(len x + len y)` (≤ 256), div `u.make(len+1)`, `q.make(m-n+1)`, Montgomery `zz.make(2m)`, power table 16 × m | ≤ 260 words |
| `(*stack).nat(n)` → `growslice` of the pooled `[]Word` | window-4 `stk.reserve(23·len m)`, karatsuba / divRecursive scratch | ≤ ~10 000 words |
| `memmove` | getData/LeftPad copies (≤ 1024 B), `nat.set` / `copy` of nats (≤ 2 KiB), stack scratch copies | ≤ ~80 KiB |
| `memclrNoHeapPointers` | `clear(z)` of scratch nats | ≤ ~80 KiB |

`OkReqs`' 2^17 elements / 2^20 bytes leave ≥ 10× margin.

<!-- anchor: "Operand bound and budgets" (cited by Spec.RunArm64.okBudget) -->
**Operand bound and budgets.** The Int-level callee specs (`RunIface` `ModSpec`, `ExpSpec`, `BytesSpec`, both ISAs; proof-internal)
require every operand to have at most `maxW = 128` words, which Run's length check establishes before any of these calls. Each
spec's budget is a closed bound in the operands' word counts:

| constant | value | derivation |
|---|---|---|
| `opCost w` | `blockBound (1024 w + 1024)` | a request of a callee with operands of at most `w` words is at most `64 w + 64` words (window-4 `stk.reserve(23 · len m)`, `2 len m`-word products, `nat.make` results), at most doubled by `growslice` |
| `ModBudget w` | `64 · opCost w` | `z.Mod(z, y)`: `nat.make` of `u`, `q`, `z`; `getStack`; `divLarge` / `divRecursiveStep` scratch — under 64 requests |
| `ExpBudget w yW` | `(8 · 64 yW + 128) · opCost w` (= `BudQ.ExpBudgetF`; `RunSucc.expBudget_eq … := rfl`) | ≤ `64 yW` exponent bits; per bit ≤ one `sqr`, one `mul`, one reduction, each ≤ 2 allocating requests: ≤ 8 per bit; setup ≤ 128. No slack factor. At `w = 0` (all lengths 0) `okBudget` keeps the `128 · opCost 0` exp allowance although Run allocates nothing there: a slightly looser premise, still finite |
| `BytesBudget w` | `blockBound (8 w)` | one `make([]byte, 8 w)` |

`okBudget` (§1b) adds Run's own requests to `ModBudget` / `ExpBudget` / `BytesBudget` at `w` = the largest operand. Two release
gates keep the budget meaningful: (a) `okBudget ≤ 2^35` over the whole spec range — arm64 and amd64 `RunGate.okBudget_gate` (value at the
corner 17 366 406 472 ≈ 2^34.02); (b) a success witness running a real exponentiation inside a toy `2^22`-byte heap — met on both ISAs
(`RunSucc.Witness.nonvacuous`, budget checked by `decide +kernel`).

## 5. Tactic-definition files (`scripts/tactic-whitelist.txt`)

Metaprogramming (`macro`/`elab`/`syntax`/non-proof attributes) is rejected by `scripts/lint_source.py` outside the files listed in
`scripts/tactic-whitelist.txt` (sha256-pinned: under RELEASE a changed file fails until it is re-reviewed and the whitelist regenerated).
Tactics cannot weaken a result (the kernel checks every proof term; `#print axioms` / `janus verify` see any axiom), but a
metaprogram could do IO or tamper with the environment, so each listed file was read:

| file | constructs | verdict |
|---|---|---|
| Common/GenReg.lean | `gen_reg` (generalize a register value) | proof tactic only (earlier review) |
| Common/AsmTac.lean | macros `same_tac`, `same64_tac` (`obtain`/`refine`/`rfl`/`janus_simp`/`exact`) | proof tactics only; no IO, axioms, env changes |
| Common/Util.lean (adapted fv-uint256) | `partial def collectDecToNat` (pure `Expr` traversal), `elab dec_facts` / `dec_goal` (for each `(decide p).toNat` run `have := FvModexp.Util.dec_toNat p`) | proof tactics only; read-only `MetaM`/`TacticM` (`getMainTarget`, `getLCtx`, `evalTactic` of a `have`); no IO, axioms, `addDecl`, env changes |
| Arm64/RG/Defs.lean, Amd64/RG/Defs.lean | macro `dl_close` (`dsimp`/`assumption`/`DataLoaded.writeLE`) | proof tactic only |
| Arm64/RG/Pre.lean, Amd64/RG/Pre.lean | macros `rg_byte`, `rg_byte64` (`unfold`/`split`/`omega`/`simp only`/`exact` over lemmas of the same file) | proof tactics only |
| Arm64/Exp/Mont.lean, Amd64/Exp/Mont.lean | `local macro` `slotv`, `inputv` (`rw`/`simp only`/`omega`) | proof tactics only |
| Arm64/Witness/StubsGrow.lean, Amd64/Witness/StubsGrow.lean | macros `pre0_tac`, `ck_tac`, `ck2_tac` (`refine`/`rfl`/`assumption`/`simp`) | proof tactics only |
| Arm64/Witness/StubsMem.lean | macro `kp_tac` (same pattern) | proof tactics only |
| Common/OmegaOnly.lean | `syntax`/`@[tactic]` `omega_only [h, …]`: clears every other propositional hypothesis (`tryClearMany`), then `evalTactic omega` | proof tactic only; clearing hypotheses only weakens the context; no IO, axioms, env changes |
| Amd64/Exp/W2S1.lean, W4S1.lean, W2Pow.lean, W4Pow.lean | macros `rdw`, `rdwP` (`simp (disch := omega) only [readLE_writeLE_of_disjoint, readLE_writeLE_self, …]`) | proof tactics only |

Any later change to one of these files must be re-reviewed (diff) before `scripts/lint_source.py --update-whitelist`.
