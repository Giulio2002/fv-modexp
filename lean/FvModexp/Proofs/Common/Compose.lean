import FvModexp.Spec

/-!
# Row 3: composition of geth's gas and run behaviour (pure Lean)

Hypotheses are the guarantees of the two machine-code rows (stated here over an abstract `Precompile`):
* `RunPrecompiled`-level `Run` row: when the lengths fail the EIP-7823 check `Run` returns an error, otherwise `compute data (parseLengths data)`;
* `RequiredGas` row: when the lengths pass, the gas is `requiredGas fork data (parseLengths data)`.
Conclusion: `runPrecompiled` (geth's `RunPrecompiledContract` logic) agrees with EthLib's `modexp fork data gas`: failure iff failure
(out of gas or length error, both "fail consuming all gas"), otherwise the same output, and the gas left is `gas - cost` with `cost` = EthLib's `chargedGas`.
-/

namespace FvModexp.Proofs.Compose

open EthLib.Base EthLib.Execution.Evm.Precompiles.Modexp FvModexp.Spec

/-- What the two machine-code rows give, in the shape of an abstract `Precompile`. -/
structure RowsHold (fork : Fork) (p : Precompile) : Prop where
  runFail : ∀ data, LengthsFail data → p.run data = none
  runOk : ∀ data, LengthsPass data → p.run data = some (compute data (parseLengths data))
  gas : ∀ data, LengthsPass data → p.requiredGas data = requiredGas fork data (parseLengths data)

theorem checkLengthsAt_post (fork : Fork) (h : PostFusaka fork) (l : Lengths) : checkLengthsAt fork l = checkLengths l := by
  unfold checkLengthsAt
  have : fork ≥ Fork.fusaka := h
  simp [this]

theorem modexp_pass {fork : Fork} (hp : PostFusaka fork) {data : ByteArray} (hl : LengthsPass data) (gas : Nat) :
    modexp fork data gas =
      if gas < requiredGas fork data (parseLengths data) then Except.error (ModexpError.outOfGas (requiredGas fork data (parseLengths data)) gas)
      else Except.ok (compute data (parseLengths data)) := by
  have hc : checkLengths (parseLengths data) = Except.ok () := hl
  have hca : checkLengthsAt fork (parseLengths data) = Except.ok () := by rw [checkLengthsAt_post fork hp, hc]
  unfold modexp
  dsimp only
  rw [hca]

theorem modexp_fail {fork : Fork} (hp : PostFusaka fork) {data : ByteArray} (hl : LengthsFail data) (gas : Nat) :
    ∃ e, modexp fork data gas = Except.error e := by
  have hca : ∃ e, checkLengthsAt fork (parseLengths data) = Except.error e := by
    rw [checkLengthsAt_post fork hp]
    cases hh : checkLengths (parseLengths data) with
    | error e => exact ⟨e, rfl⟩
    | ok u => exact absurd (by cases u; exact hh) hl
  obtain ⟨e, he⟩ := hca
  exact ⟨e, by unfold modexp; dsimp only; rw [he]⟩

theorem chargedGas_pass {fork : Fork} (hp : PostFusaka fork) {data : ByteArray} (hl : LengthsPass data) :
    chargedGas fork data = Except.ok (requiredGas fork data (parseLengths data)) := by
  have hc : checkLengths (parseLengths data) = Except.ok () := hl
  have hca : checkLengthsAt fork (parseLengths data) = Except.ok () := by rw [checkLengthsAt_post fork hp, hc]
  unfold chargedGas
  dsimp only
  rw [hca]

/-- **Row 3.** For every fork from Fusaka on, every call data and every gas, geth's `RunPrecompiledContract` logic on a precompile meeting the two
machine-code rows agrees with the EthLib MODEXP specification: a failed EthLib call (length bound, or out of gas) is a failed geth call, and a successful one is a
successful geth call with the same output and `gas - cost` left, `cost` being EthLib's `chargedGas`. -/
theorem composition {fork : Fork} {p : Precompile} (hp : PostFusaka fork) (H : RowsHold fork p) (data : ByteArray) (gas : Nat) :
    match modexp fork data gas with
    | Except.error _ => runPrecompiled p data gas = none
    | Except.ok out => ∃ cost, chargedGas fork data = Except.ok cost ∧ runPrecompiled p data gas = some (out, gas - cost) := by
  by_cases hl : LengthsPass data
  · have hg := H.gas data hl
    have hr := H.runOk data hl
    rw [modexp_pass hp hl gas]
    by_cases hlt : gas < requiredGas fork data (parseLengths data)
    · simp only [hlt, if_true]
      unfold runPrecompiled; rw [hg]; simp [hlt]
    · simp only [hlt, if_false]
      refine ⟨_, chargedGas_pass hp hl, ?_⟩
      unfold runPrecompiled; rw [hg, hr]; simp [hlt]
  · obtain ⟨e, he⟩ := modexp_fail hp hl gas
    rw [he]
    have hr := H.runFail data hl
    unfold runPrecompiled; rw [hr]
    by_cases hlt : gas < p.requiredGas data <;> simp [hlt]

/-- Converse direction: a failed geth call is a failed EthLib call, so the two outcomes agree exactly. -/
theorem error_of_fail {fork : Fork} {p : Precompile} (hp : PostFusaka fork) (H : RowsHold fork p) (data : ByteArray) (gas : Nat)
    (h : runPrecompiled p data gas = none) : ∃ e, modexp fork data gas = Except.error e := by
  have := composition hp H data gas
  cases hm : modexp fork data gas with
  | error e => exact ⟨e, rfl⟩
  | ok out =>
    rw [hm] at this
    obtain ⟨cost, _, hr⟩ := this
    rw [h] at hr; cases hr

end FvModexp.Proofs.Compose
