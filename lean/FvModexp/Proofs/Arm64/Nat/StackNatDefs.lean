import FvModexp.Proofs.Arm64.Nat.LibStackNat
import FvModexp.Proofs.Arm64.Top.RunIface
import FvModexp.Proofs.Common.StackNatMath

/-!
# `(*stack).nat(n)` (go-bigmodexpfix nat.go:319-329), arm64 — statement (agent expmc's `ExpHyp.StackNatHyp` shape)

```go
func (s *stack) nat(n int) nat {
	nr := (n + 3) &^ 3 // round up to multiple of 4
	off := len(s.w)
	s.w = slices.Grow(s.w, nr)     // growslice(w, off+nr, cap, off+nr-cap, Word) + memclr of the new words, if cap < off+nr
	s.w = s.w[:off+nr]
	x := s.w[off : off+n : off+n]
	if n > 0 { x[0] = 0xfedcb }
	return x
}
```
Args `X0 = st` (the `*stack`: header `(w, len, cap)` at `st`), `X1 = n`. Frame 112 (`MOVD.W R30, -112(RSP)`), spills
`X0, X1` at `SP + 8, SP + 16` (`above = 24`); deepest callee a runtime call (4096) from `SP - 112`: `stk = 4208`.
The store `s.w = …` is a pointer store into the header: write barrier (`runtime.writeBarrier` flag read, both values
explored; `gcWriteBarrier2`).

Amendments to expmc's posted shape (forced by the code; NOTES-divmc "[divmc s5] StackNat landed"):
* pre: `runtime.writeBarrier`'s flag word readable (`wbA`, a `.noptrbss` global, not in the extraction's data) and apart
  from the header (it is read after the header's `len`/`cap` stores); the
  header apart from the free part of the array (the result's first word is stored there before the return);
* post: `X0` (the result pointer) is stated for `0 < n` (Go returns `s.w[off:off:off]`, whose pointer is masked to the
  array base, for `n = 0`); "array kept" when `len + nr ≤ cap` (not `len + n ≤ cap`: the code grows when
  `len + n ≤ cap < len + nr`), "array fresh" when `cap < len + nr`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.StackNat

open FvModexp.Arm64.RunIface (Serves)

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*stack).nat"
def names : List String := LibStackNat.names

/-- `runtime.writeBarrier` (its `enabled` word, read by `MOVWU` before the pointer store into the header) -/
abbrev wbA : Nat := Extracted.dataAddr.«runtime.writeBarrier»

/-- the rounded size `nr` -/
@[reducible] def rnd (n : Nat) : Nat := (n + 3) / 4 * 4

@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above st n : Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ StkOK s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8) ∧
    n ≤ 2 ^ 16 ∧ stLen s.mem st + n + 3 ≤ 2 ^ 16 ∧ stackNatCost (stLen s.mem st) n ≤ b ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ s.mem.accessible wbA 4 false = true ∧ Apart st 24 wbA 4 ∧
    Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))

@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above st n : Nat) (s s' : State) : Prop :=
  (0 < n → s'.regs 0 = BitVec.ofNat 64 (stW s'.mem st + 8 * stLen s.mem st)) ∧ s'.regs 1 = BitVec.ofNat 64 n ∧
    s'.regs 2 = BitVec.ofNat 64 n ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), (LiveExt R L L' ∧ b - stackNatCost (stLen s.mem st) n ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem)) ∧
      StkOK s'.mem R L' st ∧ stLen s'.mem st = stLen s.mem st + rnd n ∧
      (stLen s.mem st + rnd n ≤ stCap s.mem st → stW s'.mem st = stW s.mem st ∧ stCap s'.mem st = stCap s.mem st) ∧
      (stCap s.mem st < stLen s.mem st + rnd n → InRanges (stW s'.mem st) (8 * stCap s'.mem st) R.rt ∧
        ApartAll (stW s'.mem st) (8 * stCap s'.mem st) L) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ stkWs s.mem st) ∧ LiveFrame s.mem s'.mem L (stkWs s.mem st)

def Hyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn) [st, n]
      (fun s => Pre R b L stk above st.toNat n.toNat s)
      (fun s s' => Post R b L stk above st.toNat n.toNat s s')

end FvModexp.Arm64.StackNat
