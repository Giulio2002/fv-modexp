import Janus
import Extracted
import FvModexp.Spec.Mem
import FvModexp.Spec.Modexp

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1): the plain definitions the arm64 statements of row 1
(`(*bigModExp).Run`) use for the call environment, the input slice, the runtime requests, and the return.

They restate, in this reviewed layer, the conventions every proof of the project uses (docs/CONVENTIONS.md):
`FvModexp.Arm64.CallEnv` (environment), `Run.InputOK` (input), `LiveExt` (live set growth). The proofs show each
definition here equal (by unfolding) to the proof-side one. -/

namespace FvModexp.Spec.RunArm64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The function under verification. -/
def fn : String := "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run"

/-- The stack window of the call: 4800 bytes below `SP` (`Run`'s 624-byte frame plus the deepest callee frame of the
header phase, `nat.setBytes` 4160) and 40 bytes above (the return slot and the four argument words). -/
def window (s : State) : List (Nat × Nat) := [(s.sp.toNat - 4800, s.sp.toNat + 40)]

/-- The call environment: the stack-growth prologue falls through (`stackguard0 + 4800 < SP`), `SP` 16-aligned and the
window writable, the program's read-only data loaded, the window and the goroutine's `stackguard0` word outside the
runtime-owned ranges and apart, no live object in the window, the read-only data outside the runtime-owned ranges. -/
def Env (R : RtInv) (L : List (Nat × Nat)) (s : State) : Prop :=
  GuardOK s 4800 ∧ StackOK s 4800 40 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4800) (4800 + 40) R.rt ∧
    Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4800) (4800 + 40) ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    LiveSep L (window s) ∧ (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length R.rt)

/-- The bytes `[a, a + n)` are the program's: inside a live object, or outside the runtime-owned ranges. -/
def Held (R : RtInv) (L : List (Nat × Nat)) (a n : Nat) : Prop := InRanges a n L ∨ Outside a n R.rt

/-- The receiver `c` (3 bytes) and the input slice `(p, len, cap)` are readable program memory, apart from the window. -/
def Input (R : RtInv) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (s : State) : Prop :=
  s.mem.accessible c.toNat 3 false = true ∧ c.toNat + 3 ≤ 2 ^ 48 ∧ Held R L c.toNat 3 ∧
    Outside c.toNat 3 (window s) ∧
    p.toNat + len.toNat ≤ 2 ^ 48 ∧ len.toNat ≤ cp.toNat ∧ cp.toNat < 2 ^ 48 ∧
    s.mem.accessible p.toNat len.toNat false = true ∧ Held R L p.toNat len.toNat ∧
    Outside p.toNat len.toNat (window s)

/-- The runtime's cost bound for a block of `bytes` bytes (any size class): `2·bytes + 24`. -/
def blockBound (bytes : Nat) : Nat := 2 * bytes + 24

/-- `type:big.Word` and `type:errors.errorString` of the extraction (the element type of `nat.make` and the `errors.New`
object). -/
def wordT : Nat := Extracted.dataAddr.«type:big.Word#80ff275a»
def errT : Nat := Extracted.dataAddr.«type:errors.errorString#8e8100b7»

/-- The runtime requests of the error path: the three header `nat.make(4)` (`makeslice(Word, 4, 8)`), the short-input
copies (input below the 96 header bytes), the `errors.New` object; the budget covers their blocks. -/
def ErrReqs (R : RtInv) (b : Nat) (len : BitVec 64) : Prop :=
  R.ok (Extracted.program.contractAddr "runtime.makeslice") [wordT, 4, 8] ∧
    (len.toNat < 96 → ∀ d sr n, n ≤ 32 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, sr, n]) ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [errT] ∧ 3 * blockBound 64 + blockBound 16 ≤ b

/-- `L'` is `L` plus objects the runtime allocated: inside `R.rt`, apart from `L` and from each other. -/
def Grows (R : RtInv) (L L' : List (Nat × Nat)) : Prop :=
  ∃ ns : List (Nat × Nat), L' = L ++ ns ∧
    (∀ r ∈ ns, InRanges r.1 (r.2 - r.1) R.rt ∧ ApartAll r.1 (r.2 - r.1) L) ∧
    ns.Pairwise fun a b => Apart a.1 (a.2 - a.1) b.1 (b.2 - b.1)

/-- The frame of the return: the live set grows, the budget drops by at most `B`, the runtime invariant holds, only the
runtime-owned ranges and the window changed, and the caller's live objects are intact. -/
def Frame (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (s s' : State) : Prop :=
  ∃ (L' : List (Nat × Nat)) (b' : Nat), Grows R L L' ∧ b - B ≤ b' ∧
    R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
    MemFrame s.mem s'.mem (R.rt ++ window s) ∧ LiveFrame s.mem s'.mem L []

/-- `Run` returned `(nil, err)` with a non-nil `error`: `X0 = X1 = 0` (the nil `[]byte`), `X3 ≠ 0` (the error's type word). -/
def ErrRet (s' : State) : Prop := s'.regs 0 = 0#64 ∧ s'.regs 1 = 0#64 ∧ s'.regs 3 ≠ 0#64

/-! ### Success path (`LengthsPass`): environment with a window `W`, requests, globals, budget, return, frame -/

/-- The stack window of a successful call: `W` bytes below `SP` (`Run`'s 624-byte frame plus the deepest frame of the
big-number callees `Mod`/`exp`/`Bytes`) and 40 bytes above (the return slot and the four argument words). -/
def windowW (s : State) (W : Nat) : List (Nat × Nat) := [(s.sp.toNat - W, s.sp.toNat + 40)]

/-- The call environment of a successful call: `Env` with window `W`, and the goroutine's `stackguard0` word is not
inside a live object of the caller. -/
def EnvW (R : RtInv) (L : List (Nat × Nat)) (s : State) (W : Nat) : Prop :=
  (GuardOK s W ∧ StackOK s W 40 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - W) (W + 40) R.rt ∧
    Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - W) (W + 40) ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    LiveSep L (windowW s W) ∧ (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length R.rt)) ∧
  (∀ r ∈ L, Apart ((s.regs 28).toNat + 16) 8 r.1 (r.2 - r.1))

/-- The runtime serves every request of the success path up to these sizes (operands of at most 1024 bytes need at
most `2^17`-element slices and `2^20`-byte copies/clears; pointer arguments are unconstrained). -/
def OkReqs (R : RtInv) : Prop :=
  (∀ t n c, c ≤ 2 ^ 17 → R.ok (Extracted.program.contractAddr "runtime.makeslice") [t, n, c]) ∧
  (∀ d sr n, n ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, sr, n]) ∧
  (∀ d n, n ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [d, n]) ∧
  (∀ o n c k t, n ≤ 2 ^ 17 → R.ok (Extracted.program.contractAddr "runtime.growslice") [o, n, c, k, t]) ∧
  (∀ args, R.ok (Extracted.program.contractAddr "runtime.newobject") args) ∧
  (∀ args, R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") args) ∧
  (∀ args, R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier4") args) ∧
  (∀ args, R.ok (Extracted.program.contractAddr "sync.(*Pool).Get") args) ∧
  (∀ args, R.ok (Extracted.program.contractAddr "sync.(*Pool).Put") args)

/-- `math/big`'s writable globals at their initial Go values (`natmul.go:12,68,69`, `natdiv.go:733`:
`divRecursiveThreshold = 40` first, then `karatsubaThreshold = 40`, `basicSqrThreshold = 12`, `karatsubaSqrThreshold = 80`,
32 contiguous bytes), and `runtime.writeBarrier`'s flag word (any value): readable, outside the runtime-owned ranges and
outside the stack ranges `w`. -/
def Globals (R : RtInv) (m : Memory) (w : List (Nat × Nat)) : Prop :=
  let gA := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold»
  let wbA := Extracted.dataAddr.«runtime.writeBarrier»
  m.readLE (Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaThreshold») 8 = 40 ∧
  m.readLE (Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqrThreshold») 8 = 12 ∧
  m.readLE (Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqrThreshold») 8 = 80 ∧
  m.readLE gA 8 = 40 ∧
  Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaThreshold» = gA + 8 ∧
  Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqrThreshold» = gA + 16 ∧
  Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqrThreshold» = gA + 24 ∧
  m.accessible gA 32 false = true ∧ Outside gA 32 R.rt ∧ Outside gA 32 w ∧
  m.accessible wbA 4 false = true ∧ Outside wbA 4 R.rt ∧ Outside wbA 4 w

/-- `math/big`'s package global `natOne` (`nat.go:30`, `var natOne = nat{1}`, in `.data`) at its initial Go value: the
slice header `(op, 1, 1)` at its address and the word `op[0] = 1` of its (statically allocated) backing array, both
readable, outside the runtime-owned ranges and outside the stack ranges `w`. (`(*Int).exp` reads it: `nat.go` `set(natOne)`
/ `lsh(natOne, n)` / `add(z, natOne)` on the power-of-two and even-modulus paths.) -/
def NatOne (R : RtInv) (m : Memory) (w : List (Nat × Nat)) : Prop :=
  let nA := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne»
  let op := m.readLE nA 8
  m.readLE (nA + 8) 8 = 1 ∧ m.readLE (nA + 16) 8 = 1 ∧ m.readLE op 8 = 1 ∧
  m.accessible nA 24 false = true ∧ Outside nA 24 R.rt ∧ Outside nA 24 w ∧
  m.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧ Outside op 8 R.rt ∧ Outside op 8 w

/-- The budget of the success path, from the three lengths (bytes): the three length headers (`nat.make(4)`), the three
operand reads (a copy buffer and a `nat`), the `Mod` / `exp` call (per request at most `blockBound (1024 w + 1024)`
for operands of at most `w` words: `Mod` ≤ 64 requests, `exp` ≤ `8 · 64 · ⌈expLen/8⌉ + 128`), `Bytes` and the
`LeftPadBytes` buffer. Derivation: docs/HUMAN-REVIEW.md ("Operand bound and budgets"). -/
def okBudget (l : EthLib.Execution.Evm.Precompiles.Modexp.Lengths) : Nat :=
  let w := max (max ((l.base + 7) / 8) ((l.exponent + 7) / 8)) ((l.modulus + 7) / 8)
  let op := blockBound (1024 * w + 1024)
  3 * blockBound 64 + 3 * (blockBound 1024 + blockBound (8 * 132)) +
    (64 * op + (8 * (64 * ((l.exponent + 7) / 8)) + 128) * op + blockBound (8 * 128)) + blockBound 1024

/-- `Run` returned `(out, nil)`: the nil `error` (type word `X3 = 0`) and `out = (X0, X1)` holds exactly the bytes
`compute data (parseLengths data)` of the EthLib specification (`data` = the input bytes in the entry memory `m`). -/
def OkRet (data : ByteArray) (s' : State) : Prop :=
  s'.regs 3 = 0#64 ∧
    bytesAt s'.mem (s'.regs 0).toNat (s'.regs 1).toNat =
      EthLib.Execution.Evm.Precompiles.Modexp.compute data (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths data)

/-- The frame of a successful return with window `W`: the live set grows, the budget drops by at most `B`, the runtime
invariant holds, the output bytes `(X0, X1)` are the program's, only the runtime-owned ranges and the window changed,
and the caller's live objects are intact. -/
def FrameW (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (W : Nat) (s s' : State) : Prop :=
  ∃ (L' : List (Nat × Nat)) (b' : Nat), Grows R L L' ∧ b - B ≤ b' ∧
    R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
    (0 < (s'.regs 1).toNat → Held R L' (s'.regs 0).toNat (s'.regs 1).toNat) ∧
    MemFrame s.mem s'.mem (R.rt ++ windowW s W) ∧ LiveFrame s.mem s'.mem L []

end FvModexp.Spec.RunArm64
