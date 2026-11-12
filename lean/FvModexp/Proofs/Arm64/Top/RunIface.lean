import FvModexp.Proofs.Arm64.Conv

set_option autoImplicit false

/-!
# `(*bigModExp).Run` (arm64): the interface of the big callees (DRAFT v1, agent top)

The Int-level callees `Run` makes, stated as the `Ensures` theorems their proofs will have (`docs/CONVENTIONS.md` §3), so
that `Run`'s body can be proved against them as premises (hypothesis-first) and the premises discharged when the proofs land.

* `IntV m a`: the value of the `*Int` at `a` (`neg` byte at `a`, `abs = (ptr, len, cap)` at `a + 8, + 16, + 24`).
* `IntOK m R L a`: the header is a held, writable, 8-aligned 32-byte object and its `abs` array is `NatLive`, normalised,
  `neg = false`.
* `Serves R`: the runtime serves every request of the Run extraction's contracts up to a size bound (the budget bounds the total).
* `names*`: the functions each callee executes (call graph closure in the Run extraction, deferred wrappers included).
-/

namespace FvModexp.Arm64.RunIface

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

def P : String := "github.com/ethereum/go-bigmodexpfix/src/math/big."

/-- `(*Int).Mod` and every function it reaches. -/
def namesMod : List String := [
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Add",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Mod",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).QuoRem",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Sub",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).mul",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*stack).nat",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.addMulVVWW.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.addTo",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.addVV.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.addVW",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.basicMul",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqr",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqr.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.divWVW",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.divWW",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsuba",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsuba.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqr",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqr.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.lshVU.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.mulAddVWW.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.add",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.cmp",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.div",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.div.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divBasic",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divBasic.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divLarge",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divLarge.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divRecursiveStep",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divRecursiveStep.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divW",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul.deferwrap2",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mulAddWW",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sqr",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sqr.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sub",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.reciprocalWord",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.rshVU.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.subVV.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.subVW",
    "math/bits.Div64"]
/-- `(*Int).exp` and every function it reaches. -/
def namesExp : List String := [
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Add",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Cmp",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Div",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).GCD",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Mod",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).ModInverse",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).QuoRem",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).SetInt64",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Sub",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).exp",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).lehmerGCD",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).mul",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.(*stack).nat",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.addMulVVWW.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.addTo",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.addVV.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.addVW",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.basicMul",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqr",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqr.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.buildPrecomputationWindowModPower2",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.divWVW",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.divWW",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.euclidUpdate",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsuba",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsuba.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqr",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqr.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.lehmerSimulate",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.lehmerUpdate",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.lshVU.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.mulAddVWW.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.add",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.cmp",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.div",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.div.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divBasic",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divBasic.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divLarge",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divLarge.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divRecursiveStep",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divRecursiveStep.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divW",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNN",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNN.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOdd",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwo",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize4",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize4.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNSlow",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.lsh",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.modularInverseModPowerOfTwo",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.montgomery",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul.deferwrap2",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mulAddWW",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rem",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rem.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rsh",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.setUint64",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sqr",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sqr.deferwrap1",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.sub",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.subMod2N",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.trunc",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.reciprocalWord",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.rshVU.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.subVV.abi0",
    "github.com/ethereum/go-bigmodexpfix/src/math/big.subVW",
    "math/bits.Div64"]
def fnBytes : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Bytes"

/-- The value of the `*Int` at `a`. -/
def IntV (m : Memory) (a : Nat) : Nat := natVal m (m.readLE (a + 8) 8) (m.readLE (a + 16) 8)

/-- A non-negative, normalised `*Int` whose header and array are held objects. -/
def IntOK (m : Memory) (R : RtInv) (L : List (Nat × Nat)) (a : Nat) : Prop :=
  m.readLE a 1 = 0 ∧ a % 8 = 0 ∧ a + 32 ≤ 2 ^ 48 ∧ m.accessible a 32 true = true ∧ Held R L a 32 ∧
    NatLive m R L (m.readLE (a + 8) 8) (m.readLE (a + 24) 8) ∧ m.readLE (a + 16) 8 ≤ m.readLE (a + 24) 8 ∧
    NatNorm m (m.readLE (a + 8) 8) (m.readLE (a + 16) 8) ∧
    (0 < m.readLE (a + 24) 8 → Apart a 32 (m.readLE (a + 8) 8) (8 * m.readLE (a + 24) 8)) ∧
    m.readLE (a + 24) 8 < 2 ^ 40

/-- The requests of the Run extraction's contracts the runtime serves: every request up to a size bound (1 MiB for a copy or
clear, 2^17 elements for a new or grown slice; Run's operands are at most 1024 bytes by EIP-7823). Pointer arguments are
unconstrained. Bounded so that a real runtime meets it (an unbounded request throws `out of memory`); the non-vacuity
witness of row 1 does not need it (its input fails the EIP-7823 check, where `Run` requires only the requests of
`RunServes`, see `RunDefs`). -/
def Serves (R : RtInv) : Prop :=
  (∀ t n c, c ≤ 2 ^ 17 → R.ok (cA "runtime.makeslice") [t, n, c]) ∧
  (∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n]) ∧
  (∀ d n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memclrNoHeapPointers") [d, n]) ∧
  (∀ o n c k t, n ≤ 2 ^ 17 → R.ok (cA "runtime.growslice") [o, n, c, k, t]) ∧
  (∀ args, R.ok (cA "runtime.newobject") args) ∧ (∀ args, R.ok (cA "runtime.gcWriteBarrier2") args) ∧
  (∀ args, R.ok (cA "runtime.gcWriteBarrier4") args) ∧ (∀ args, R.ok (cA "sync.(*Pool).Get") args) ∧
  (∀ args, R.ok (cA "sync.(*Pool).Put") args)

/-- The address of the first threshold global (`divRecursiveThreshold`); the other three follow at `+8, +16, +24`. -/
@[reducible] def gA : Nat := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold»

/-- `runtime.writeBarrier`'s flag word (a `.noptrbss` global; not in the extraction's data, but its address is known). -/
@[reducible] def wbA : Nat := Extracted.dataAddr.«runtime.writeBarrier»

/-- The writable globals the big callees read, at their initial values (`natmul.go:12,68,69`, `natdiv.go:733`), outside
the runtime-owned ranges. The four words are contiguous, `divRecursiveThreshold` first (`gA`, 32 bytes, both ISAs):
readable, outside the runtime-owned ranges and outside the stack ranges `w` (`IntPre` passes the callee's window), so a
load does not fault and the values survive stack stores. (`natOne`, `intOne`, `stackPool` are added when a proof needs
them.) -/
-- (`runtime.writeBarrier`'s flag word `wbA` is read by the pointer stores of `(*stack).nat` (divmc's StackNat pre); its
-- value is irrelevant (both branches are proved), only readability and separation are stated.)
def Globals (R : RtInv) (m : Memory) (w : List (Nat × Nat) := []) : Prop :=
  m.readLE (Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaThreshold») 8 = 40 ∧
  m.readLE (Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqrThreshold») 8 = 12 ∧
  m.readLE (Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqrThreshold») 8 = 80 ∧
  m.readLE (Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold») 8 = 40 ∧
  Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaThreshold» = gA + 8 ∧
  Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.basicSqrThreshold» = gA + 16 ∧
  Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.karatsubaSqrThreshold» = gA + 24 ∧
  m.accessible gA 32 false = true ∧ Outside gA 32 R.rt ∧ Outside gA 32 w ∧
  m.accessible wbA 4 false = true ∧ Outside wbA 4 R.rt ∧ Outside wbA 4 w

/-- The callee frame shared by the three specs: the `*Int` objects `xs` (headers on the caller's frame or the heap) are
outside the callee's window and apart from the `stackguard0` word, `Globals`, `Serves`, the invariant, the budget `B`.
Facts about an `abs` array are stated only when its capacity is positive (an empty array is never accessed; its
pointer is whatever `make(0)` / a nil `nat` left there). -/
def IntPre (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (stk above : Nat) (xs : List Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ Globals R s.mem (win s stk above) ∧ B ≤ b ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (∀ a ∈ xs, IntOK s.mem R L a ∧ Outside a 32 (win s stk above) ∧
      (0 < s.mem.readLE (a + 24) 8 → Outside (s.mem.readLE (a + 8) 8) (8 * s.mem.readLE (a + 24) 8) (win s stk above)) ∧
      Apart a 32 ((s.regs 28).toNat + 16) 8 ∧
      (0 < s.mem.readLE (a + 24) 8 → Apart (s.mem.readLE (a + 8) 8) (8 * s.mem.readLE (a + 24) 8) ((s.regs 28).toNat + 16) 8)) ∧
    (xs.Pairwise fun a a' => Apart a 32 a' 32 ∧
      (0 < s.mem.readLE (a' + 24) 8 → Apart a 32 (s.mem.readLE (a' + 8) 8) (8 * s.mem.readLE (a' + 24) 8)) ∧
      (0 < s.mem.readLE (a + 24) 8 → Apart a' 32 (s.mem.readLE (a + 8) 8) (8 * s.mem.readLE (a + 24) 8)) ∧
      (0 < s.mem.readLE (a + 24) 8 → 0 < s.mem.readLE (a' + 24) 8 →
        Apart (s.mem.readLE (a + 8) 8) (8 * s.mem.readLE (a + 24) 8) (s.mem.readLE (a' + 8) 8) (8 * s.mem.readLE (a' + 24) 8)))

/-- Operand size bound of the three specs, in words: EIP-7823 caps every Run operand at 1024 bytes = 128 words (Run's
length check establishes it before any call). Without it the specs are unprovable under the bounded `Serves R` and a
fixed budget (e.g. window-4 exponentiation reserves `23 · len m` stack words). -/
def maxW : Nat := 128

/-- The `*Int` at `a` has at most `k` words (`len(abs) ≤ k`). -/
def IntLenLe (m : Memory) (a k : Nat) : Prop := m.readLE (a + 16) 8 ≤ k

/-- The word count `len(abs)` of the `*Int` at `a`. -/
def lenW (m : Memory) (a : Nat) : Nat := m.readLE (a + 16) 8

/-- Budget of one request of a callee whose operands have at most `w` words: the request is at most `64 w + 64` words
(window-4 exponentiation's `stk.reserve(23 · len m)`, the Karatsuba / recursive-division scratch of `2 len m`-word
products, `nat.make` results), at most doubled by `growslice`: a block of at most `1024 w + 1024` bytes, which costs at
most `allocCost (1024 w + 1024)` (`blockSize_le_allocCost`). -/
def opCost (w : Nat) : Nat := allocCost (1024 * w + 1024)

/-- Budget of `z.Mod(z, y)` for operands of at most `w` words: at most 64 allocating requests (`nat.make` of `u`, `q`, `z`,
the `(*stack).nat` scratch of `divLarge`/`divRecursiveStep`, `getStack`). Derivation in docs/HUMAN-REVIEW.md. -/
def ModBudget (w : Nat) : Nat := 64 * opCost w

/-- Budget of `z.exp(z, y, m, false)` for operands of at most `w` words and an exponent of `yW` words: per exponent bit
(`64 yW` bits) at most 8 allocating requests (one `sqr`, one `mul`, one reduction by `div`/`montgomery`: their `nat.make`
results and `(*stack).nat` scratch), plus 128 setup requests (power table of 16 entries, `stk.reserve`, `m1 m2 z1 z2` of
`expNNEven`, `lsh`, `getStack`). Derivation in docs/HUMAN-REVIEW.md. -/
def ExpBudget (w yW : Nat) : Nat := (8 * (64 * yW) + 128) * opCost w

/-- Budget of `x.Bytes()` for `x` of `w` words: one `make([]byte, 8 w)`. -/
def BytesBudget (w : Nat) : Nat := allocCost (8 * w)

/-- The old array of the `*Int` at `z` as a written range: none when its capacity is `0` (its pointer is arbitrary). -/
@[reducible] def arrW (m : Memory) (z : Nat) : List (Nat × Nat) :=
  if 0 < m.readLE (z + 24) 8 then [(m.readLE (z + 8) 8, m.readLE (z + 8) 8 + 8 * m.readLE (z + 24) 8)] else []

/-- What every spec returns about the receiver `z` (written: its header and a new or reused array) and the runtime:
the array of the result is the old one (same pointer and capacity) or a fresh runtime object apart from `L`. The
window is `winA`: the caller's saved frame pointer / link register slots `[SP-8, SP+8)` are not written (arm64 ABI). -/
def IntPost (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (stk above : Nat) (z : Nat) (v : Nat) (s s' : State) : Prop :=
  IntV s'.mem z = v ∧ ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - B ≤ b' ∧
    R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ IntOK s'.mem R L' z ∧
    (0 < s'.mem.readLE (z + 24) 8 →
      (s'.mem.readLE (z + 8) 8 = s.mem.readLE (z + 8) 8 ∧ s'.mem.readLE (z + 24) 8 = s.mem.readLE (z + 24) 8) ∨
      (InRanges (s'.mem.readLE (z + 8) 8) (8 * s'.mem.readLE (z + 24) 8) R.rt ∧
        ApartAll (s'.mem.readLE (z + 8) 8) (8 * s'.mem.readLE (z + 24) 8) L)) ∧
    MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ (z, z + 32) :: arrW s.mem z) ∧
    LiveFrame s.mem s'.mem L ((z, z + 32) :: arrW s.mem z)

/-- The address of `math/big`'s package global `stackPool` (`arith.go`/`nat.go` `var stackPool sync.Pool`, `.bss`). -/
@[reducible] def stackPoolA : Nat := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.stackPool»

/-- What the `stk == nil` paths of `(*Int).exp` / `(*Int).Mod` need (`getStack()` = `stackPool.Get()` or `newobject`,
deferred `stk.free()`; NOTES-conventions "[expmc s32] REQUEST"): address 0 is not runtime memory (a new stack object is
never nil), and `stackPool`'s `New` word (`Janus.Spec.Pool.newOffset`) is 0 (`New` is never set; Pool.Get's pre),
outside the runtime-owned ranges and the stack ranges `w`. -/
def PoolG (R : RtInv) (m : Memory) (w : List (Nat × Nat)) : Prop :=
  Outside 0 1 R.rt ∧ m.readLE (stackPoolA + Pool.newOffset) 8 = 0 ∧ Outside (stackPoolA + Pool.newOffset) 8 R.rt ∧
    Outside (stackPoolA + Pool.newOffset) 8 w

/-- **`z.Mod(z, y)`** as Run calls it (`int.go:325`; `X0 = z`, `X1 = x = z`, `X2 = y`): returns `z` with `z = x mod y`. -/
def ModSpec (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y : BitVec 64),
    Ensures ((Extracted.program.onlySegments namesMod).link impl) (segAddr Extracted.program (P ++ "(*Int).Mod")) [z, z, y]
      (fun s => IntPre R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat))) L stk above [z.toNat, y.toNat] s ∧
        0 < IntV s.mem y.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ PoolG R s.mem (win s stk above))
      (fun s s' => s'.regs 0 = z ∧ IntPost R b (ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)))
          L stk above z.toNat (IntV s.mem z.toNat % IntV s.mem y.toNat) s s' ∧
        IntV s'.mem y.toNat = IntV s.mem y.toNat)

/-- The address of `math/big`'s package global `natOne` (`nat.go:30`, `.data`). -/
@[reducible] def natOneA : Nat := Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne»

/-- `natOne` as `(*Int).exp` reads it (NOTES-conventions "[top s18]"): header `(op, 1, 1)` at `natOneA`, `op[0] = 1`,
readable, outside the runtime-owned ranges and the stack ranges `w`, the word held (the conjuncts before `∀` are
`EvenHyp.NatOne R L m op w` verbatim), and apart from the operand `*Int`s `xs` (headers and arrays), which the call
writes. -/
def OneG (R : RtInv) (L : List (Nat × Nat)) (m : Memory) (w : List (Nat × Nat)) (xs : List Nat) : Prop :=
  ∃ op, (m.readLE natOneA 8 = op ∧ m.readLE (natOneA + 8) 8 = 1 ∧ m.readLE (natOneA + 16) 8 = 1 ∧ m.readLE op 8 = 1 ∧
    m.accessible natOneA 24 false = true ∧ Outside natOneA 24 R.rt ∧ Outside natOneA 24 w ∧
    m.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧ Held R L op 8 ∧ Outside op 8 w) ∧
    ∀ a ∈ xs, Apart a 32 natOneA 24 ∧ Apart a 32 op 8 ∧
      (0 < m.readLE (a + 24) 8 → Apart (m.readLE (a + 8) 8) (8 * m.readLE (a + 24) 8) natOneA 24 ∧
        Apart (m.readLE (a + 8) 8) (8 * m.readLE (a + 24) 8) op 8)

/-- **`z.exp(z, y, m, false)`** as Run calls it (`int.go:575`; `X0 = z`, `X1 = x = z`, `X2 = y`, `X3 = m`, `X4 = slow = 0`):
returns `z` with `z = x ^ y mod m` (`m > 0`; `y ≥ 0`, so the `ModInverse` path is not taken). -/
def ExpSpec (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64),
    Ensures ((Extracted.program.onlySegments namesExp).link impl) (segAddr Extracted.program (P ++ "(*Int).exp"))
      [z, z, y, mm, 0#64]
      (fun s => IntPre R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat)) (lenW s.mem y.toNat))
        L stk above [z.toNat, y.toNat, mm.toNat] s ∧ 0 < IntV s.mem mm.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ IntLenLe s.mem mm.toNat maxW ∧
        OneG R L s.mem (win s stk above) [z.toNat, y.toNat, mm.toNat] ∧
        PoolG R s.mem (win s stk above))
      (fun s s' => s'.regs 0 = z ∧
        IntPost R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat)) (lenW s.mem y.toNat))
          L stk above z.toNat (IntV s.mem z.toNat ^ IntV s.mem y.toNat % IntV s.mem mm.toNat) s s')

/-- **`x.Bytes()`** (`int.go:527`; `X0 = x`): a fresh `[]byte` `(p, n, n)` holding the minimal big-endian form of `x`
(no leading zero byte), `x` unchanged. -/
def BytesSpec (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64),
    Ensures ((Extracted.program.onlySegments [fnBytes]).link impl) (segAddr Extracted.program fnBytes) [x]
      (fun s => IntPre R b (BytesBudget (lenW s.mem x.toNat)) L stk above [x.toNat] s ∧ IntLenLe s.mem x.toNat maxW)
      (fun s s' => ∃ p n c : Nat, (s'.regs 0).toNat = p ∧ (s'.regs 1).toNat = n ∧ (s'.regs 2).toNat = c ∧ n ≤ c ∧
        beVal s'.mem p n = IntV s.mem x.toNat ∧ (n = 0 ∨ (s'.mem.bytes p).toNat ≠ 0) ∧
        ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - (BytesBudget (lenW s.mem x.toNat)) ≤ b' ∧
          R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ (0 < n → InRanges p n L' ∧ InRanges p n R.rt ∧ ApartAll p n L ∧
            s'.mem.accessible p n true = true ∧ p + n ≤ 2 ^ 48) ∧
          MemFrame s.mem s'.mem (R.rt ++ winA s stk above) ∧ LiveFrame s.mem s'.mem L [])

end FvModexp.Arm64.RunIface
