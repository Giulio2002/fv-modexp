import EthLib.Execution.Evm.Precompiles.Modexp

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1): the logic of geth v1.17.10 `core/vm.RunPrecompiledContract`
(`core/vm/contracts.go:272`) for a precompile with a `RequiredGas` and a `Run`, abstracted to what the composition theorem needs. -/

namespace FvModexp.Spec

/-- A precompile as geth sees it: `RequiredGas(input) uint64` (as a number below `2^64`) and `Run(input) ([]byte, error)`, where
`none` stands for a non-nil error (and `some out` for `out, nil`). -/
structure Precompile where
  requiredGas : ByteArray → Nat
  run : ByteArray → Option ByteArray

/-- Outcome of `RunPrecompiledContract` as far as the EVM observes it: `none` is a failed call (out of gas, or `Run` returned an error: the caller
then consumes all gas of the call), `some (out, remaining)` is success with the output and the gas left.
geth: `gasCost := p.RequiredGas(input)`; `gas < gasCost` → `ErrOutOfGas`; otherwise `gas -= gasCost`, `output, err := p.Run(input)`; `err` is passed up. -/
def runPrecompiled (p : Precompile) (input : ByteArray) (gas : Nat) : Option (ByteArray × Nat) :=
  let cost := p.requiredGas input
  if gas < cost then none
  else match p.run input with
    | none => none
    | some out => some (out, gas - cost)

end FvModexp.Spec
