import FvModexp.Spec.Modexp
import FvModexp.Spec.Geth

set_option autoImplicit false

/-!
# geth's precompile result cache is sound for MODEXP (agent asm s77, REDTEAM-arm64 R3)

geth v1.17.10 attaches a precompile result cache by default (`core/blockchain.go:417-420`, `vm.NewPrecompileCache()` unless
`cfg.NoPrecompileCache`). In `RunPrecompiledContract` (`core/vm/contracts.go:289-301`) a cacheable precompile with a cache
key is served from the cache on a hit (gas accounting unchanged), and on a miss its `Run` output is stored only when
`err == nil`. `bigModExp` is `Cacheable` (contracts.go:701) and a `NormalizingPrecompile`: its key is
`NormalizeInput(input)` (contracts.go:704-732) under the 8192-byte cap of `precompileCacheKey`
(`core/vm/precompile_cache.go:223-238`, `maxCacheablePrecompileInput = 8192`, :40). Loads and stores copy the bytes
(precompile_cache.go:147,176); the scope is (active precompile set, address).

`Spec.cacheKey` / `Spec.normalize` (`Spec/Geth.lean`, moved there in s78 so row 3's `Spec.runPrecompiled` models the cache)
transcribe that key (pure Nat/ByteArray level; `getData(input, k, 32)` of an input longer than the 96-byte
header is the plain 32 bytes `readNat input k 32`, `uint256.SetBytes` reads them big-endian, `IsUint64 ↔ < 2^64`, and the
`uint256` sum `96 + b + e + m` of three `< 2^64` values does not wrap; `input[:n]` = `input.extract 0 n`).

`cacheKey_sound`: a key determines everything EthLib's MODEXP result depends on — the key has the same length headers,
the same `LengthsPass` verdict and the same `compute` output as the input. Hence `cacheKey_eq` (two inputs with equal keys
agree on `LengthsPass` and `compute`): a cache hit for `d` returns an output that `Run` produced, without error, for an
input `d'` with `cacheKey d' = cacheKey d`, i.e. (row 1: `err == nil` only when `LengthsPass d'`) `compute d' … =
compute d …` — exactly what `Run d` would return (row 1). Gas is charged from `RequiredGas(input)` of the actual input
before the lookup, hit or miss (contracts.go:273-276), so row 2 / row 3 are unaffected.
-/

namespace FvModexp.CacheKey

open EthLib.Base EthLib.Execution.Evm.Precompiles.Modexp FvModexp.Spec

theorem normalize_of_cacheKey {d k : ByteArray} (h : cacheKey d = some k) : normalize d = some k := by
  unfold cacheKey at h
  revert h
  cases normalize d with
  | none => intro h; cases h
  | some k' =>
    intro h
    by_cases hs : k'.size > 8192
    · simp [hs] at h
    · simp only [hs, ↓reduceIte] at h; exact h

theorem readNat_congr {d d' : ByteArray} {start size : Nat}
    (h : ∀ i, start ≤ i → i < start + size → byteAt d i = byteAt d' i) :
    readNat d start size = readNat d' start size := by
  unfold readNat EthLib.Execution.Evm.bufferRead
  congr 1
  apply List.map_congr_left
  intro i hi
  have := List.mem_range.1 hi
  exact h _ (by omega) (by omega)

/-- the first `n` bytes of `d` read like `d` below `n` -/
theorem byteAt_extract (d : ByteArray) (n i : Nat) (hi : i < n) : byteAt (d.extract 0 n) i = byteAt d i := by
  unfold byteAt
  have hs : (d.extract 0 n).size = min n d.size - 0 := ByteArray.size_extract
  by_cases h : i < d.size
  · have h' : i < (d.extract 0 n).size := by rw [hs]; omega
    simp only [h', h, ↓reduceDIte, ByteArray.getElem_extract, Nat.zero_add]
  · have h' : ¬ i < (d.extract 0 n).size := by rw [hs]; omega
    simp only [h', h, ↓reduceDIte]

theorem parseLengths_congr {d d' : ByteArray} (h : ∀ i, i < 96 → byteAt d i = byteAt d' i) :
    parseLengths d = parseLengths d' := by
  unfold parseLengths
  simp only [LENGTH_HEADER_BYTES]
  rw [readNat_congr (d := d) (d' := d') (fun i _ hi => h i (by omega)),
    readNat_congr (d := d) (d' := d') (start := 32) (fun i _ hi => h i (by omega)),
    readNat_congr (d := d) (d' := d') (start := 2 * 32) (fun i _ hi => h i (by omega))]

theorem compute_congr {d d' : ByteArray} (l : Lengths)
    (h : ∀ i, i < 96 + l.base + l.exponent + l.modulus → byteAt d i = byteAt d' i) :
    compute d l = compute d' l := by
  have hBO : BASE_OFFSET = 96 := rfl
  have e1 : readNat d BASE_OFFSET l.base = readNat d' BASE_OFFSET l.base :=
    readNat_congr fun i _ h2 => h i (by omega)
  have e2 : readNat d l.exponentStart l.exponent = readNat d' l.exponentStart l.exponent :=
    readNat_congr fun i _ h2 => h i (by unfold Lengths.exponentStart at h2; omega)
  have e3 : readNat d l.modulusStart l.modulus = readNat d' l.modulusStart l.modulus :=
    readNat_congr fun i _ h2 => h i (by unfold Lengths.modulusStart Lengths.exponentStart at h2; omega)
  unfold compute
  rw [e1, e2, e3]

/-- with an empty modulus the output does not read the data -/
theorem compute_zero {d d' : ByteArray} (l : Lengths) (hm : l.modulus = 0) :
    compute d l = compute d' l := by
  have hz : ∀ (x : ByteArray) (st : Nat), readNat x st l.modulus = 0 := by
    intro x st; rw [hm]; rfl
  unfold compute
  simp [hz]

/-- **The key determines the result**: the key has the input's length headers, its `LengthsPass` verdict and its
`compute` output. -/
theorem cacheKey_sound (d k : ByteArray) (h : cacheKey d = some k) :
    parseLengths k = parseLengths d ∧ (FvModexp.Spec.LengthsPass k ↔ FvModexp.Spec.LengthsPass d) ∧
      compute k (parseLengths k) = compute d (parseLengths d) := by
  have hkey := normalize_of_cacheKey h
  unfold normalize at hkey
  have hL : parseLengths d = ⟨readNat d 0 32, readNat d 32 32, readNat d 64 32⟩ := rfl
  -- the key is `d` itself, or a prefix `d.extract 0 n` with every byte that matters below `n`
  suffices hk : parseLengths k = parseLengths d ∧ compute k (parseLengths k) = compute d (parseLengths d) by
    refine ⟨hk.1, ?_, hk.2⟩
    unfold FvModexp.Spec.LengthsPass; rw [hk.1]
  split at hkey
  · simp only [Option.some.injEq] at hkey; subst hkey; exact ⟨rfl, rfl⟩
  split at hkey
  · simp at hkey
  split at hkey
  · next hbm =>
    simp only [Option.some.injEq] at hkey; subst hkey
    have hp : parseLengths (d.extract 0 96) = parseLengths d :=
      parseLengths_congr fun i hi => byteAt_extract d 96 i hi
    refine ⟨hp, ?_⟩
    rw [hp]
    exact compute_zero _ (by rw [hL]; exact hbm.2)
  split at hkey
  · simp only [Option.some.injEq] at hkey; subst hkey; exact ⟨rfl, rfl⟩
  · simp only [Option.some.injEq] at hkey; subst hkey
    have hp : parseLengths (d.extract 0 (96 + readNat d 0 32 + readNat d 32 32 + readNat d 64 32)) = parseLengths d :=
      parseLengths_congr fun i hi => byteAt_extract d _ i (by omega)
    refine ⟨hp, ?_⟩
    rw [hp]
    exact compute_congr _ fun i hi => byteAt_extract d _ i (by rw [hL] at hi; exact hi)

/-- **Equal keys, equal results**: two inputs with the same cache key agree on the EIP-7823 verdict and on EthLib's
output, so a hit returns what `Run` returns for the actual input (module header). -/
theorem cacheKey_eq (d d' k : ByteArray) (h : cacheKey d = some k) (h' : cacheKey d' = some k) :
    (FvModexp.Spec.LengthsPass d ↔ FvModexp.Spec.LengthsPass d') ∧
      compute d (parseLengths d) = compute d' (parseLengths d') := by
  have ⟨_, a2, a3⟩ := cacheKey_sound d k h
  have ⟨_, b2, b3⟩ := cacheKey_sound d' k h'
  exact ⟨a2.symm.trans b2, a3.symm.trans b3⟩

end FvModexp.CacheKey
