import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
namespace Scout2
def montFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.montgomery"
def amvFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addMulVVWW.abi0"
def subFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.subVV.abi0"
abbrev head : Nat := segAddr Extracted.program montFn + 0x1cc

set_option trace.profiler true in
set_option trace.profiler.threshold 200 in
theorem fullP (ret : Nat) (hret : RetAddr Extracted.program ret) (Q : Outcome → Prop) (S : State)
    (hpc : S.pc = BitVec.ofNat 64 head) (h : Reaches (Extracted.program.withExit ret) { S with pc := S.pc + 4, regs := setReg S.regs 14 (S.regs 7 + S.regs 13) } Q) :
    Reaches (Extracted.program.withExit ret) S Q := by
  janus_step
  sorry

set_option trace.profiler true in
set_option trace.profiler.threshold 200 in
theorem linkP (impl : List Segment) (ret : Nat) (hret : RetAddr ((Extracted.program.onlySegments [montFn, amvFn, subFn]).link impl) ret) (Q : Outcome → Prop) (S : State)
    (hpc : S.pc = BitVec.ofNat 64 head) :
    Reaches (((Extracted.program.onlySegments [montFn, amvFn, subFn]).link impl).withExit ret) S Q := by
  janus_step
  sorry
end Scout2
