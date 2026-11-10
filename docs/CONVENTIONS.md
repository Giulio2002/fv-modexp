# Conventions for function proofs (fv-modexp)

Owner: agent `top`. Status: **v1** (2026-11-10). Every machine-code proof of a function that `(*bigModExp).Run` reaches
follows these rules, so that summaries compose bottom-up into the Run theorem. Lean vocabulary:
`lean/FvModexp/Proofs/Common/{Conv,Link}.lean` (ISA independent), `lean/FvModexp/Proofs/{Arm64,Amd64}/Conv.lean` (per ISA).
Pilot proofs that follow every rule: `lean/FvModexp/Proofs/{Arm64,Amd64}/Nat/SetBytes*.lean` (see §9).

## 1. One extraction per ISA: the Run extraction

All function proofs that feed row 1 are about **the same `Extracted`**: the extraction of
`github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run` from `build/harness-<isa>` with the `Run` flags of
`scripts/contract-flags.sh` (84 functions arm64, 82 amd64; `/srv/fv-modexp-ops/extract-Run-<isa>.log`). The final
`janus verify` of row 1 builds exactly that `Extracted` and imports the whole proof tree of the ISA, so a lemma about any
other extraction cannot be used. (Row 2, `RequiredGas`, is a separate extraction with its own tree.)

* Dev compile: `build/x-Run-<isa>/Extracted.lean` compiled once to `build/dev/<isa>/Extracted.olean`; a module is compiled with
  `build/dbuild.sh <isa> FvModexp/Proofs/<Isa>/…/X.lean` (LEAN_PATH = lake path + `build/dev/<isa>`), under `memcap 16G`.
* An `Arm64` module never imports an `Amd64` module (two different `Extracted`). `Proofs/Common/*` never imports `Extracted`.
* Addresses: never literals. Entry `segAddr Extracted.program fn`, loop heads `entry + 0x…` (offset inside the function),
  contracts `Extracted.program.contractAddr "runtime.makeslice"` (`cA` in `Conv`), data `Extracted.dataAddr.«type:big.Word#…»`.

## 2. Files, modules, names

* `lean/FvModexp/Proofs/Common/<Topic>.lean`: ISA-independent math / models (namespace `FvModexp` or `FvModexp.Mdl`).
* `lean/FvModexp/Proofs/Arm64/<Area>/<Name>.lean`, namespace **`FvModexp.Arm64.<Name>`**; amd64 twin
  `lean/FvModexp/Proofs/Amd64/<Area>/<Name>.lean`, namespace **`FvModexp.Amd64.<Name>`**. `<Name>` is unique per ISA
  (`SetBytes`, `SetBytesStd` for the std `math/big` copy, `IntMod`, `ExpNN`, `DivLarge`, …). Areas: `Nat`, `Int`, `Vec`
  (asm), `Div`, `Exp`, `Top`.
* A function too large for one module is split **one module per path/segment**: `<Name>Defs` (statement pieces: `Pre`,
  `Post`, `Rel`), `<Name>Loop1`, `<Name>Seg2`, …, and `<Name>` (the theorem `ens` composing them), as in Janus
  `examples/rtmisc/proofs/arm64/Chain`.
* The final rows: `lean/FvModexp/Proofs/<Isa>/Run.lean` (`FvModexp.<Isa>.Run.correctness` + `namespace Witness`).

Each function module `F` exports:

| name | what |
|---|---|
| `fn : String` | the full symbol (`"github.com/ethereum/go-bigmodexpfix/src/math/big.nat.setBytes"`) |
| `names : List String` | `fn` and **every extracted function it reaches** (transitively; callees executed through their summaries count) |
| `Pre …`, `Post …` (optional) | plain `def`s of the pre/postcondition when they are long |
| `ens` | the `Ensures` theorem (§3) |
| `sum` | `ens` moved into a caller's program (§4) |

## 3. The statement of a function proof (`ens`)

```lean
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)  -- one per runtime fn reached
    (b : Nat) (L : List (Nat × Nat)) (args… : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) entry [args…]
      (fun s => CallEnv R L s stk above ∧ <data facts> ∧ <argument objects> ∧ <values> ∧
                R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ <R.ok of each request> ∧ <budget>)
      (fun s s' => <results> ∧ ∃ L' b', LiveExt R L L' ∧ b - cost ≤ b' ∧
                R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ <result objects held in L'> ∧
                MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ ws) ∧ LiveFrame s.mem s'.mem L ws)
```

Rules, one by one:

1. **Program.** `(Extracted.program.onlySegments names).link impl`, written out literally (the executors need a syntactic
   closed `Extracted.program …`, an abbreviation such as `prog names impl` is rejected by `janus_run`). This is what makes the
   return site inside a caller an admissible `RetAddr` (Janus `InternalCall.lean`).
2. **Runtime.** One `R : RtInv` (the live runtime of Janus `Contracts/Live.lean`), threaded through everything. Every runtime
   contract is a hypothesis **about `Extracted.program.ofImpl impl`** (runtime code only) and the only premise on `impl` is
   `hap : ImplApart Extracted.program impl`; inside the proof move it with
   `MakesliceLiveContract.of_codeIn (codeIn_ofImpl_restrict_of_apart hap names) hmk`. Use exactly the live contracts:
   `MakesliceLiveContract`, `NewobjectLiveContract`, `MemmoveLive`, `MemclrNoHeapPointersLive`, `WbLiveContract … n`,
   `RtLiveContract … growsliceSpec growsliceLive` (byte slices) / `GrowsliceLiveContract` (8-byte noscan),
   `PoolGetLive`/`PoolPutLive` (sync.Pool), stack `4096`. amd64: the `…64` twins.
3. **Call environment** `CallEnv R L s stk above` (`Conv`): `GuardOK s stk ∧ StackOK s stk above ∧ DataLoaded ∧` window outside
   `R.rt` `∧` guard slot apart from window and outside `R.rt` `∧ LiveSep L (win s stk above)`.
   * `stk` = own frame + max over calls (callee's `stk`, or `framesize + 4096` for a runtime call); `above` = highest byte of
     the caller's spill area the function writes (`8 * #spilled arg slots`, usually `8 * nargs`). Read both off the
     disassembly (`go tool objdump -s 'symbol$' build/harness-<isa>`). arm64 frames: `MOVD.W R30, -F(RSP)` / `SUB $F` + `STP`.
   * Callers prove `CallEnv` of the callee from their own (`stk_caller ≥ frame_caller + stk_callee`).
4. **Values.** Go `nat` = (ptr, len, cap): value `natVal m p n` (= `m.readLE p (8n)`, LE limbs), `limbs m p n` for list models
   (`FvModexp.Mdl.val (limbs m p n) = natVal m p n`), normalisation `NatNorm m p n`. Go `[]byte` as number: `beVal m p n`
   (big-endian). Results are stated about the **pre-state values** (`natVal s.mem x xl`), never about `s'` of an input.
   Bridge to EthLib (`bytesToNat (bufferRead …)`) only in `Run`.
5. **Objects** (aliasing). An input array the function only reads: `s.mem.accessible p n false ∧ p + n ≤ 2^48 ∧
   Held R L p n ∧ Outside p n (win s stk above)`. An array it may write (a nat `z` it reuses): `NatLive s.mem R L p c`
   (`Held` + aligned + writable) `∧ (0 < c → Outside p (8 c) (win s stk above))` (a held range may be caller stack memory,
   so it must be stated outside the callee's window), and its range is in the post's `ws`. Distinct objects are related with `Apart a n b k`
   (one atomic fact each; never a big disjunction — PROOFS.md §Performance), stated only when the code needs it
   (`0 < zc → Apart zp (8 zc) bp bl`). `Held R L a n := InRanges a n L ∨ Outside a n R.rt`: a heap object of the caller or
   caller memory outside the runtime (stack buffers, data). **A held range is unchanged by every runtime call and every
   summary unless named in its `ws`** (`Held.readLE`, `Held.beVal`).
6. **Live set and budget.** Pre: `R.inv b L g (view R.rt L s.mem)` with `g = (s.regs 28).toNat` (amd64 `(s.regs 14).toNat`).
   Post: `∃ L' b', LiveExt R L L' ∧ b - cost ≤ b' ∧ R.inv b' L' g (view R.rt L' s'.mem)`, where `cost` is a closed upper
   bound (`allocCost bytes = 2·bytes + 24 ≥ blockSize`, `makeCost n` for `nat.make n`). New objects the function returns
   are in `L'` (`NatLive s'.mem R L' p' c'`); in the "fresh" case also `ApartAll p' (8c') L` and `InRanges p' (8c') R.rt`.
   Scratch objects the function drops stay in `L'` (the collector, not the program, frees memory) unless given back with
   `PoolPutLive` (then they leave `L'` via `removeRanges`/`dropAll`).
7. **Requests served** (`R.ok`). The pre states `R.ok addr args` for exactly the requests the function makes, as functions of
   its inputs (`R.ok (cA "runtime.makeslice") [wordT, n, makeCap n]`), guarded by the condition under which the request is
   made (`zc < n → …`). A request whose argument is a runtime-chosen pointer is quantified: `∀ d, R.ok (cA "runtime.memmove")
   [d, src, n]`. Do not assume `∀ args, R.ok …` (the Witness runtime must be able to serve the requests: toy memmove /
   memclr stubs serve fixed sizes).
8. **Frame.** `MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ ws) ∧ LiveFrame s.mem s'.mem L ws`, `ws` = the caller-visible
   ranges the function writes (a reused `z` array: `[(zp, zp + 8 zc)]`). Registers: nothing (the `Ensures` gives
   `ABIReturn`, `toSummaryIn` keeps `SP`, `X28`, `X29`, `X18` / amd64 `RSP+8`, `RBP`, `R14`, `X15`; Go callers reload the rest).
9. **Panics.** A function proof is an `Ensures` (no panic, no fault) **under its precondition**; every panic path
   (`panicBounds`, `panicdivide`, nil dereference) must be refuted by the precondition, and if the precondition needed to
   refute it is not implied by Run's call sites, that is a FINDING (BRIEF.md).
10. **Writable globals** (`karatsubaThreshold`, `natOne`, `intOne`, `stackPool`, `runtime.writeBarrier`): the pre states the
    value the function reads (`s.mem.readLE (Extracted.dataAddr.«…karatsubaThreshold») 8 = 40`) and that the global is
    `Outside … R.rt` (except `stackPool`, which the Pool contract places in `R.rt`). `Run` collects them in one `Globals` def.

## 4. Composition: callers use `sum`

```lean
set_option linter.defProp false in
/-- `F` as a callee of a function whose names `ms` include `F.names`. -/
def sum (impl) (hap) (R) (contracts…) … (ms : List String) (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R … args) (noExit_restrict hap names) (codeIn_restrict_mono hap hsub)
  -- amd64: Ensures.toSummaryIn (ens …) (A64.noExit_restrict64 hap names) (by decide : args.length ≤ 9) (A64.codeIn_restrict_mono64 hap hsub)
```

In the caller: `janus_run until [pc] calls [F.sum impl hap R … ms (by decide)]`. The callee's precondition at the call is
`RetAddr p0 X30 ∧ ArgsFrom s 0 args ∧ pre`; `janus_callpre` (run automatically) proves `RetAddr` and `DataLoaded`, the rest
comes from the caller's facts (`CallEnv` of the callee from the caller's `CallEnv`: arithmetic on `stk`). After the call the
post is destructured: results, `L'`, `b'`, `MemFrame`/`LiveFrame` (use `Held.readLE` for the caller's other objects), the
invariant for the next call. The final theorem lives in `Extracted.program.link impl`: `codeIn_restrict_full`.

A caller states the callee's `Pre` instantiated at its call; a summary is **never** weakened ad hoc for one caller: if a caller
needs more, strengthen the callee's post (and its proof) — the statement shape stays the one of §3.

**Hypothesis-first development.** A caller may be proved before its callee: take the callee's `sum` as a theorem *premise*
with exactly the statement `ens` will have (`(hF : ∀ args…, Summary …)`), so the caller's proof is unchanged when the real `sum`
replaces the premise. List every such open premise in `docs/COVERAGE.md` (`hypothesis`).

## 5. Loops

Loop lemma per head (`abbrev hWord : Nat := entry + 0xbc`), `Reaches ((… .link impl).withExit ret) S (IsReturn …)` by
induction on the iterations left, with the invariant as **equations on `S`** (registers, `S.sp`, `S.pc`) plus memory facts as
`MemFrame M₀ S.mem ws` and the words written so far as `readLE` equations (not an exact store chain once a call result
memory is involved). The runtime invariant `R.inv b' L' g (view R.rt L' S.mem)` is part of the loop invariant; a store into a
held range keeps it (`inv_store_held`).

## 6. Sanity budget (BRIEF hard caps)

* Module elaboration target ≤ 5 min, ≤ 8 GB; every compile under `memcap 16G` (`/usr/bin/time -f '%e s %M KB'`).
* **One module per path**: split at runtime calls and loop heads when a module passes ~2 min; each segment is one `Reaches`
  lemma about the same `R` (Chain pattern). Split aliasing / branch cases late; state disjointness as `Apart`.
* Never raise `maxHeartbeats` to pass a slow proof locally beyond `0`-in-`set_option … in` on the one theorem that runs the
  executor; profile with `set_option trace.profiler true` and `janus.omega.log`, fix, and record before/after in `docs/PERF.md`.
* `janus_run (budget := N)` while developing, to localise a slow step.
* No `sorry` in a committed module that is claimed done; WIP modules are listed in `WIP-SORRY.txt`.

## 7. amd64 differences

* Registers: args `RAX, RBX, RCX, RDI, RSI, R8, R9, R10, R11` (`argReg`), results `RAX, RBX, RCX`; `g = R14`
  (`(s.regs 14).toNat`), `SP = s.regs 4`, `X15 = 0`. `CallEnv` (Amd64/Conv) uses `StackGuardOK`/`StackWritable` with the
  return-address slot included in the window: `win s stk above = [(RSP - stk, RSP + 8 + above)]`.
* Contracts `…LiveContract64`, `MemmoveLive64`, …; `Ensures.toSummaryIn` needs `args.length ≤ numIntRegs`.

## 8. Spec bridge (Run only)

`FvModexp.Spec.bytesAt m p n` (infra) is the `ByteArray` of a Go `[]byte`; `beVal m p n = bytesToNat (bytesAt m p n).toList`
(`Common/Bytes.lean`). Statements never use EthLib instances (`Spec.PostFusaka`).

## 9. Pilot (arm64 DONE 2026-11-10, amd64 in progress)

`nat.setBytes` (both copies), arm64 + amd64: `FvModexp.Arm64.SetBytes.ens`, `FvModexp.Arm64.SetBytesStd.ens`,
`FvModexp.Amd64.SetBytes.ens`, `FvModexp.Amd64.SetBytesStd.ens` — a runtime call (`makeslice` through the inlined
`nat.make`), three loops, `nat.norm`, both the reuse and the allocation branch. Timings in `docs/PERF.md`.

Pilot files (arm64, no sorry, `#print axioms`: propext, Classical.choice, Quot.sound):
`Proofs/Arm64/Nat/SetBytes{Defs,Norm,Byte,Word,Mid,}.lean` and the `SetBytesStd*` twins (generated from them by `sed`: only `fn`,
`wordT` and the namespace differ). Pattern to copy for a function with loops and a runtime call:
* `Defs`: `Pre`, `Post`, and `Mid` = everything that holds at every loop head after the runtime call (frame record values,
  inputs unchanged, the new object's facts, `L'`, `b'`, `R.inv`, the two frames). `Mid.store` (a store into the object keeps `Mid`).
* one module per loop, each a `Reaches` lemma by induction over the iterations left, taking `Mid … m` and register equations;
  each loop exits by `refine nextLoop …` (the later loops are proved first).
* `Mid` module: `mid_of_reuse` / `mid_of_alloc` build `Mid` from the entry facts / from the contract postcondition
  (`LiveFrame M0 m L []`, `MemFrame M0 m (R.rt ++ calleeWindow)`, `ApartAll`, `InRanges`, `R.inv (b - round) (L ++ [obj])`).
* main module: per path `janus_run … until [loopHead] calls [hmk'.pos]`, `rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 …`
  to name the contract's results, then `refine loopLemma … (mid_of_alloc …) (by janus_simp) …`.
