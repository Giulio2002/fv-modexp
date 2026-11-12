import FvModexp.Proofs.Arm64.Top.RunH2SA
import FvModexp.Proofs.Arm64.Top.RunH2SB

set_option autoImplicit false

/-! # `Run` (arm64): `B1` to `B2`, `len < 64` (header 1 = `expLen`: `getData(input, 32, 32)`, std `setBytes`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem h2s (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (hokr : HdrOkR R b len)
    (Q : Outcome → Prop)
    (hk : ∀ S L2 b2, RelH R b L c p len cp s ret 2 L2 b2 S → S.pc = BitVec.ofNat 64 pcB2 →
      Reaches ((LibRun.program.link impl).withExit ret) S Q)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 1 L1 b1 S)
    (hpc : S.pc = BitVec.ofNat 64 pcB1) (h64 : len.toNat < 64) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  by_cases h32 : len.toNat < 32
  · exact h2sA impl hap R hmk hmv b L c p len cp ret hret s henv hin hokr Q hk S L1 b1 hrel hpc h64 h32
  · exact h2sB impl hap R hmk hmv b L c p len cp ret hret s henv hin hokr Q hk S L1 b1 hrel hpc h64 h32

end FvModexp.Arm64.Run
