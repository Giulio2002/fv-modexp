import FvModexp.Proofs.Arm64.Top.RunH1
import FvModexp.Proofs.Arm64.Top.RunH2
import FvModexp.Proofs.Arm64.Top.RunH3
import FvModexp.Proofs.Arm64.Top.RunL

/-! # `Run` (arm64): entry to `C0` — the three headers, `BitLen`/`Uint64`, EIP-7823 (error return) and the empty case

Composition of `h1`, `h2`, `h3`, `la`, `lb`: from the entry either `Run` returns (the error or the empty output) or it
reaches `C0` (the operands' `getData`) with the three lengths, all at most 1024. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

theorem runPre (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (hs : CallSetup ((LibRun.program.link impl).withExit ret) (segAddr Extracted.program fn) [c, p, len, cp] s)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)) (hokr : HdrOkR R b len)
    (hrecv : s.mem.readLE c.toNat 3 = 65793) (hokn : R.ok (cA "runtime.newobject") [errT])
    (hcostE : 3 * makeCost 4 + allocCost 16 ≤ b)
    (Q : Outcome → Prop)
    (hErr : ∀ S' : State, (1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2) →
      ABIReturn s S' → ErrRet S' → RunFrame R b (3 * makeCost 4 + allocCost 16) L s S' → Q (.returned S'))
    (hZero : ∀ S' : State, hdrV s p len 0 = 0 → hdrV s p len 1 ≤ 1024 → hdrV s p len 2 = 0 →
      ABIReturn s S' → S'.regs 1 = 0#64 → S'.regs 3 = 0#64 → RunFrame R b (3 * makeCost 4) L s S' → Q (.returned S'))
    (hk : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 : Nat), RelH R b L c p len cp s ret 3 L1 b1 S →
      ∀ T' : State, T'.pc = BitVec.ofNat 64 pcC0 → T'.mem = S.mem → T'.sp = S.sp → T'.regs 28 = S.regs 28 →
      T'.regs 29 = S.regs 29 → T'.regs 18 = S.regs 18 →
      hdrV s p len 0 ≤ 1024 → hdrV s p len 1 ≤ 1024 → hdrV s p len 2 ≤ 1024 →
      ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0) →
      (T'.regs 8).toNat = hdrV s p len 0 → (T'.regs 11).toNat = hdrV s p len 1 → (T'.regs 12).toNat = hdrV s p len 2 →
      (T'.regs 1).toNat = p.toNat + (if 96 < len.toNat then 96 else 0) →
      (T'.regs 3).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0) → (T'.regs 7).toNat = len.toNat - 96 →
      Reaches ((LibRun.program.link impl).withExit ret) T' Q) :
    Reaches ((LibRun.program.link impl).withExit ret) s Q :=
  h1 impl hap R hmk hmv b L c p len cp ret hret s hs henv hin hinv hokr Q fun S1 L1 b1 hr1 hp1 =>
    h2 impl hap R hmk hmv b L c p len cp ret hret s henv hin hokr Q (fun S2 L2 b2 hr2 hp2 =>
      h3 impl hap R hmk hmv b L c p len cp ret hret s henv hin hokr Q (fun S3 L3 b3 hr3 hp3 hq0 hq1 =>
        la impl hap R b L c p len cp ret hret s henv Q S3 L3 b3 hr3 hp3 hq0 hq1
          (fun T hTpc hTm hTsp hT28 hT29 hT18 hL0 hL1 hL2 =>
            lb impl hap R hno b L c p len cp ret hret s henv hin hrecv hokn hcostE Q S3 L3 b3 hr3 T hTpc hTm hTsp
              hT28 hT29 hT18 hL0 hL1 hL2 hErr hZero (hk S3 L3 b3 hr3)))
        S2 L2 b2 hr2 hp2)
      S1 L1 b1 hr1 hp1

end FvModexp.Arm64.Run
