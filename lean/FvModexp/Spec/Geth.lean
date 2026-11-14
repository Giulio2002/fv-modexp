import EthLib.Execution.Evm.Precompiles.Modexp

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1): the logic of geth v1.17.10 `core/vm.RunPrecompiledContract`
(`core/vm/contracts.go:272`) for a precompile with a `RequiredGas` and a `Run`, abstracted to what the composition theorem needs. -/

namespace FvModexp.Spec

/-- A precompile as geth sees it: `RequiredGas(input) uint64` (as a number below `2^64`) and `Run(input) ([]byte, error)`, where
`none` stands for a non-nil error (and `some out` for `out, nil`). -/
structure Precompile where
  requiredGas : ByteArray → Nat
  run : ByteArray → Option ByteArray

open EthLib.Base EthLib.Execution.Evm.Precompiles.Modexp in
/-- geth's `(*bigModExp).NormalizeInput(input)` (`core/vm/contracts.go:704-732`): the input up to the end of the operands the
header declares; `none` (`ok = false`) when a length header is not a `uint64`. (`getData(input, k, 32)` of an input longer
than the 96-byte header is the plain 32 bytes `readNat input k 32`, read big-endian by `uint256.SetBytes`; `IsUint64` is
`< 2^64`; the `uint256` sum `96 + b + e + m` of three `< 2^64` values does not wrap; `input[:n]` is `input.extract 0 n`.) -/
def normalize (input : ByteArray) : Option ByteArray :=
  if input.size ≤ 96 then some input
  else if ¬ (readNat input 0 32 < 2 ^ 64 ∧ readNat input 32 32 < 2 ^ 64 ∧ readNat input 64 32 < 2 ^ 64) then none
  else if readNat input 0 32 = 0 ∧ readNat input 64 32 = 0 then some (input.extract 0 96)
  else if ¬ 96 + readNat input 0 32 + readNat input 32 32 + readNat input 64 32 < 2 ^ 64 ∨
      input.size ≤ 96 + readNat input 0 32 + readNat input 32 32 + readNat input 64 32 then some input
  else some (input.extract 0 (96 + readNat input 0 32 + readNat input 32 32 + readNat input 64 32))

/-- geth's result-cache key for MODEXP: `precompileCacheKey(bigModExp, input)` (`core/vm/precompile_cache.go:223-238`) =
`NormalizeInput`, `none` when not cacheable (a length header ≥ 2^64, or a key over `maxCacheablePrecompileInput = 8192`
bytes, precompile_cache.go:40). -/
def cacheKey (input : ByteArray) : Option ByteArray :=
  match normalize input with
  | some k => if k.size > 8192 then none else some k
  | none => none

/-- geth's precompile result cache (`*PrecompileCache`) as seen by one MODEXP call: `none` = `cache == nil`; `some lookup` =
an attached cache whose entries, in this call's scope (active precompile set, address), are `lookup key` (`cache.load`,
a copy of the stored bytes, precompile_cache.go:147). -/
abbrev Cache := Option (ByteArray → Option ByteArray)

/-- What geth's stores guarantee about every cache entry (`RunPrecompiledContract`, contracts.go:296-299, and
`cache.store` copying key and output, precompile_cache.go:158-176): an entry `key ↦ out` was stored only after
`output, err := p.Run(input)` returned `err == nil` and `output = out` for some input `d'` with `precompileCacheKey(p, d') =
key`. (The scope (active set, address) fixes the precompile, so `p` is this call's precompile.) -/
def CacheStoredBy (p : Precompile) (cache : Cache) : Prop :=
  ∀ lookup, cache = some lookup → ∀ key out, lookup key = some out → ∃ d', cacheKey d' = some key ∧ p.run d' = some out

/-- The cache lookup of `RunPrecompiledContract` (contracts.go:290-294): with a cache and a cache key, the stored output if any. -/
def cacheHit (cache : Cache) (input : ByteArray) : Option ByteArray :=
  match cache with
  | none => none
  | some lookup =>
    match cacheKey input with
    | none => none
    | some key => lookup key

/-- Outcome of `RunPrecompiledContract` as far as the EVM observes it: `none` is a failed call (out of gas, or `Run` returned an error: the caller
then consumes all gas of the call), `some (out, remaining)` is success with the output and the gas left.
geth (contracts.go:272-304): `gasCost := p.RequiredGas(input)`; `gas < gasCost` → `ErrOutOfGas`; otherwise `gas -= gasCost`; with a
cache (`cache`, default `nil`) and a cache key, a stored output is returned with `err == nil` (gas accounting identical on hit and
miss); otherwise `output, err := p.Run(input)` and `err` is passed up (the store on a miss does not change the result).
The logger and the Amsterdam access-list `Touch` do not change the result and are not modelled. -/
def runPrecompiled (p : Precompile) (input : ByteArray) (gas : Nat) (cache : Cache := none) : Option (ByteArray × Nat) :=
  let cost := p.requiredGas input
  if gas < cost then none
  else match cacheHit cache input with
    | some out => some (out, gas - cost)
    | none =>
      match p.run input with
      | none => none
      | some out => some (out, gas - cost)

end FvModexp.Spec
