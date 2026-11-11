import FvModexp.Proofs.Amd64.Nat.LibStackNat
import FvModexp.Proofs.Amd64.Top.RunIface
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
Args `RAX = st`, `RBX = n`; results `(RAX, RBX, RCX)`. Frame `PUSHQ BP; SUBQ $0x50` (`RSP' = RSP - 0x58`), spills
`AX, BX` at `RSP + 8, RSP + 16` (`above = 24`, incl. the return slot); runtime calls from `RSP'` (return address at
`RSP' - 8`, 4096 bytes below): `stk = 4192`. Write barrier: `CMPL runtime.writeBarrier, $0`, `gcWriteBarrier2` (`R11`).
Same statement as the arm64 twin (Amd64 vocabulary: `g = R14`, `win` in the post, `fsBase` kept).

Amendments to expmc's posted shape (forced by the code; NOTES-divmc "[divmc s5] StackNat landed"):
* pre: `runtime.writeBarrier`'s flag word readable (`wbA`, a `.noptrbss` global, not in the extraction's data) and apart
  from the header (it is read after the header's `len`/`cap` stores); the
  header apart from the free part of the array (the result's first word is stored there before the return);
* post: `X0` (the result pointer) is stated for `0 < n` (Go returns `s.w[off:off:off]`, whose pointer is masked to the
  array base, for `n = 0`); "array kept" when `len + nr ≤ cap` (not `len + n ≤ cap`: the code grows when
  `len + n ≤ cap < len + nr`), "array fresh" when `cap < len + nr`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.StackNat

open FvModexp.Amd64.RunIface (Serves)

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*stack).nat"
def names : List String := LibStackNat.names

/-- `runtime.writeBarrier` (its `enabled` word, read by `MOVWU` before the pointer store into the header) -/
abbrev wbA : Nat := Extracted.dataAddr.«runtime.writeBarrier»

/-- the rounded size `nr` -/
@[reducible] def rnd (n : Nat) : Nat := (n + 3) / 4 * 4

@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above st n : Nat) (s : State) : Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ StkOK s.mem R L st ∧ Outside st 24 (win s stk above) ∧
    (0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s stk above) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8) ∧
    n ≤ 2 ^ 16 ∧ stLen s.mem st + n + 3 ≤ 2 ^ 16 ∧ stackNatCost (stLen s.mem st) n ≤ b ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ s.mem.accessible wbA 4 false = true ∧ Apart st 24 wbA 4 ∧
    Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))

@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above st n : Nat) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  (0 < n → s'.regs 0 = BitVec.ofNat 64 (stW s'.mem st + 8 * stLen s.mem st)) ∧ s'.regs 3 = BitVec.ofNat 64 n ∧
    s'.regs 1 = BitVec.ofNat 64 n ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), (LiveExt R L L' ∧ b - stackNatCost (stLen s.mem st) n ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem)) ∧
      StkOK s'.mem R L' st ∧ stLen s'.mem st = stLen s.mem st + rnd n ∧
      (stLen s.mem st + rnd n ≤ stCap s.mem st → stW s'.mem st = stW s.mem st ∧ stCap s'.mem st = stCap s.mem st) ∧
      (stCap s.mem st < stLen s.mem st + rnd n → InRanges (stW s'.mem st) (8 * stCap s'.mem st) R.rt ∧
        ApartAll (stW s'.mem st) (8 * stCap s'.mem st) L) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ stkWs s.mem st) ∧ LiveFrame s.mem s'.mem L (stkWs s.mem st)

def Hyp (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn) [st, n]
      (fun s => Pre R b L stk above st.toNat n.toNat s)
      (fun s s' => Post R b L stk above st.toNat n.toNat s s')

end FvModexp.Amd64.StackNat
