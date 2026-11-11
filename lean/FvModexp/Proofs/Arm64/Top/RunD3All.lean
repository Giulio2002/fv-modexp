import FvModexp.Proofs.Arm64.Top.RunD3L
import FvModexp.Proofs.Arm64.Top.RunD3P
import FvModexp.Proofs.Arm64.Top.RunD3ZA
import FvModexp.Proofs.Arm64.Top.RunD3ZE
import FvModexp.Proofs.Arm64.Top.RunD3ZN

/-! # `Run` (arm64): `D1` to `D2`, all paths of the exponent operand (direct slice, stack buffer, `makeslice` buffer
with or without input bytes to copy) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

theorem d2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelD R b L c p len cp s ret 2 L1 b1 S)
    (hpc : S.pc = BitVec.ofNat 64 pcD2)
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 3 L2 b2 S2 →
      (S2.regs 0).toNat = S2.mem.readLE (s.sp.toNat - 192) 8 → (S2.regs 1).toNat = S2.mem.readLE (s.sp.toNat - 184) 8 →
      S2.pc = BitVec.ofNat 64 pcD3 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  by_cases hdir : min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2 ≤ len.toNat - 96
  · exact d2x impl hap R hmk hmv hokS b L c p len cp ret hret s henv hin Q hbudD S L1 b1 hrel hpc hdir hk
  by_cases hsm : hdrV s p len 2 ≤ 32
  · exact d2p impl hap R hmk hmv hokS b L c p len cp ret hret s henv hin Q hbudD S L1 b1 hrel hpc (by omega) hsm hokM hk
  by_cases hn0 : 0 < len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)
  · exact d2l impl hap R hmk hmv hokS b L c p len cp ret hret s henv hin Q hbudD S L1 b1 hrel hpc (by omega) (by omega)
      hn0 hokB hokM hk
  · refine d3zA impl hap R hmk hokS b L c p len cp ret hret s henv hin Q hbudD S L1 b1 hrel hpc (by omega) (by omega)
      (by omega) hokB fun U Lk bk B src hj hUpc => ?_
    by_cases heq : B = src
    · exact d3zE impl hap R hmk hokS b L c p len cp ret hret s henv hin Q hbudD hk U Lk bk B src hj hUpc heq
    · exact d3zN impl hap R hmk hmv hokS b L c p len cp ret hret s henv hin Q hbudD hokM hk U Lk bk B src hj hUpc heq

end FvModexp.Arm64.Run
