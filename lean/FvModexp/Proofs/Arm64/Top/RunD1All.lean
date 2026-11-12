import FvModexp.Proofs.Arm64.Top.RunD1
import FvModexp.Proofs.Arm64.Top.RunD1L
import FvModexp.Proofs.Arm64.Top.RunD1P

/-! # `Run` (arm64): `C0` to `D1`, all paths of the base operand (direct slice, stack buffer, `makeslice` buffer) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

theorem d1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 3 L1 b1 S)
    (T : State) (hTpc : T.pc = BitVec.ofNat 64 pcC0) (hTm : T.mem = S.mem) (hTsp : T.sp = S.sp)
    (hT28 : T.regs 28 = S.regs 28) (hT29 : T.regs 29 = S.regs 29) (hT18 : T.regs 18 = S.regs 18)
    (hl0 : hdrV s p len 0 ≤ 1024) (hl1 : hdrV s p len 1 ≤ 1024) (hl2 : hdrV s p len 2 ≤ 1024)
    (hnz : ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0))
    (hr8 : (T.regs 8).toNat = hdrV s p len 0) (hr11 : (T.regs 11).toNat = hdrV s p len 1)
    (hr12 : (T.regs 12).toNat = hdrV s p len 2)
    (hr1 : (T.regs 1).toNat = p.toNat + (if 96 < len.toNat then 96 else 0))
    (hr3 : (T.regs 3).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0)) (hr7 : (T.regs 7).toNat = len.toNat - 96)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b) 
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 1 L2 b2 S2 → S2.pc = BitVec.ofNat 64 pcD1 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  by_cases hdir : hdrV s p len 0 ≤ len.toNat - 96
  · exact d1x impl hap R hmk hmv hokS b L c p len cp ret hret s henv hin Q S L1 b1 hrel T hTpc hTm hTsp hT28 hT29 hT18
      hl0 hl1 hl2 hnz hr8 hr11 hr12 hr1 hr3 hr7 hbudD hdir hk
  by_cases hsm : hdrV s p len 0 ≤ 32
  · exact d1p impl hap R hmk hmv hokS b L c p len cp ret hret s henv hin Q S L1 b1 hrel T hTpc hTm hTsp hT28 hT29 hT18 hl0 hl1 hl2 hnz hr8 hr11 hr12 hr1 hr3 hr7 hbudD (by omega) hsm hokM hokB hk
  · exact d1l impl hap R hmk hmv hokS b L c p len cp ret hret s henv hin Q S L1 b1 hrel T hTpc hTm hTsp hT28 hT29 hT18 hl0 hl1 hl2 hnz hr8 hr11 hr12 hr1 hr3 hr7 hbudD (by omega) (by omega) hokM hokB hk

end FvModexp.Arm64.Run
