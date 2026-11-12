import Janus
import Extracted
import FvModexp.Spec.Mem
import FvModexp.Spec.Modexp

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1): the plain definitions the amd64 statements of row 1
(`(*bigModExp).Run`) use for the call environment, the input slice, the runtime requests, and the return — the amd64
twin of `Spec.RunArm64`.

They restate, in this reviewed layer, the conventions every amd64 proof of the project uses (docs/CONVENTIONS.md):
`FvModexp.Amd64.CallEnv` (environment, incl. the goroutine pointer in TLS), `Run.InputOK` (input), `LiveExt` (live set
growth). The proofs show each definition here equal (by unfolding) to the proof-side one. -/

namespace FvModexp.Spec.RunAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

/-- The function under verification. -/
def fn : String := "github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run"

/-- The stack window of the call: 4800 bytes below `RSP` (`Run`'s 616-byte frame plus the deepest callee frame of the
header phase, `nat.setBytes` 4160) and 40 bytes above (the return address and the four argument words). -/
def window (s : State) : List (Nat × Nat) := [((s.regs 4).toNat - 4800, (s.regs 4).toNat + 40)]

/-- The call environment: the stack-growth prologue falls through (`stackguard0 + 4800 < RSP`), `RSP` 8-aligned and the
window writable, the program's read-only data loaded, the window and the goroutine's `stackguard0` word outside the
runtime-owned ranges and apart, no live object in the window, the read-only data outside the runtime-owned ranges, and
the goroutine pointer in TLS (`FS:-8` holds `R14`; the slot outside the runtime-owned ranges and apart from the window). -/
def Env (R : RtInv) (L : List (Nat × Nat)) (s : State) : Prop :=
  StackGuardOK s 4800 ∧ StackWritable s 4800 40 ∧ (s.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4800) (4800 + 40) R.rt ∧
    Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4800) (4800 + 40) ∧
    Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    LiveSep L (window s) ∧ (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length R.rt) ∧
    (TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 R.rt ∧ Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - 4800) (4800 + 40))

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

/-- The frame of the return: `FS` base and direction flag unchanged, the live set grows, the budget drops by at most `B`,
the runtime invariant holds, only the runtime-owned ranges and the window changed, and the caller's live objects are
intact. -/
def Frame (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (L' : List (Nat × Nat)) (b' : Nat), Grows R L L' ∧ b - B ≤ b' ∧
    R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
    MemFrame s.mem s'.mem (R.rt ++ window s) ∧ LiveFrame s.mem s'.mem L []

/-- `Run` returned `(nil, err)` with a non-nil `error`: `RAX = RBX = 0` (the nil `[]byte`), `RDI ≠ 0` (the error's type
word). -/
def ErrRet (s' : State) : Prop := s'.regs 0 = 0#64 ∧ s'.regs 3 = 0#64 ∧ s'.regs 7 ≠ 0#64

/-! ### Success path (`LengthsPass`): environment with a window `W`, requests, globals, budget, return, frame -/

/-- The stack window of a successful call: `W` bytes below `RSP` (`Run`'s 616-byte frame plus the deepest frame of the
big-number callees `Mod`/`exp`/`Bytes`) and 40 bytes above (the return address and the four argument words). -/
def windowW (s : State) (W : Nat) : List (Nat × Nat) := [((s.regs 4).toNat - W, (s.regs 4).toNat + 40)]

/-- The call environment of a successful call: `Env` with window `W`, and neither the goroutine's `stackguard0` word nor
the TLS slot `FS:-8` is inside a live object of the caller. -/
def EnvW (R : RtInv) (L : List (Nat × Nat)) (s : State) (W : Nat) : Prop :=
  (StackGuardOK s W ∧ StackWritable s W 40 ∧ (s.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - W) (W + 40) R.rt ∧
    Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - W) (W + 40) ∧
    Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    LiveSep L (windowW s W) ∧ (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length R.rt) ∧
    (TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 R.rt ∧ Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - W) (W + 40))) ∧
  (∀ r ∈ L, Apart ((s.regs 14).toNat + 16) 8 r.1 (r.2 - r.1)) ∧
  (∀ r ∈ L, Apart (s.fsBase.toNat - 8) 8 r.1 (r.2 - r.1))

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

/-- The budget of the success path, from the three lengths (bytes): the three length headers (`nat.make(4)`), the three
operand reads (a copy buffer and a `nat`), the `Mod` / `exp` call (per request at most `blockBound (1024 w + 1024)`
for operands of at most `w` words: `Mod` ≤ 64 requests, `exp` ≤ `8 · 64 · ⌈expLen/8⌉ + 128`), `Bytes` and the
`LeftPadBytes` buffer. Derivation: docs/HUMAN-REVIEW.md ("Operand bound and budgets"). Same formula as arm64. -/
def okBudget (l : EthLib.Execution.Evm.Precompiles.Modexp.Lengths) : Nat :=
  let w := max (max ((l.base + 7) / 8) ((l.exponent + 7) / 8)) ((l.modulus + 7) / 8)
  let op := blockBound (1024 * w + 1024)
  3 * blockBound 64 + 3 * (blockBound 1024 + blockBound (8 * 132)) +
    (64 * op + (8 * (64 * ((l.exponent + 7) / 8)) + 128) * op + blockBound (8 * 128)) + blockBound 1024

/-- `Run` returned `(out, nil)`: the nil `error` (type word `RDI = 0`) and `out = (RAX, RBX)` holds exactly the bytes
`compute data (parseLengths data)` of the EthLib specification (`data` = the input bytes in the entry memory `m`). -/
def OkRet (data : ByteArray) (s' : State) : Prop :=
  s'.regs 7 = 0#64 ∧
    bytesAt s'.mem (s'.regs 0).toNat (s'.regs 3).toNat =
      EthLib.Execution.Evm.Precompiles.Modexp.compute data (EthLib.Execution.Evm.Precompiles.Modexp.parseLengths data)

/-- The frame of a successful return with window `W`: `FS` base and direction flag unchanged, the live set grows, the
budget drops by at most `B`, the runtime invariant holds, the output bytes `(RAX, RBX)` are the program's, only the
runtime-owned ranges and the window changed, and the caller's live objects are intact. -/
def FrameW (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (W : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (L' : List (Nat × Nat)) (b' : Nat), Grows R L L' ∧ b - B ≤ b' ∧
    R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
    (0 < (s'.regs 3).toNat → Held R L' (s'.regs 0).toNat (s'.regs 3).toNat) ∧
    MemFrame s.mem s'.mem (R.rt ++ windowW s W) ∧ LiveFrame s.mem s'.mem L []

end FvModexp.Spec.RunAmd64
