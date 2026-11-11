import FvModexp.Proofs.Amd64.Top.RunH1
import FvModexp.Proofs.Amd64.Top.RunH2
import FvModexp.Proofs.Amd64.Top.RunH3
import FvModexp.Proofs.Amd64.Top.RunLa
import FvModexp.Proofs.Amd64.Top.RunL

/-! # `Run` (amd64): entry to `C0` — the three headers, `BitLen`/`Uint64`, EIP-7823 (error return) and the empty case

Composition of `h1`, `h2`, `h3`, `la`, `lb` (twin of the arm64 `runPre`): from the entry either `Run` returns (the error
or the empty output) or it reaches `C0` (the operands' `getData`) with the three lengths, all at most 1024. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

theorem runPre (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (hs : CallSetup ((LibRun.program.link impl).withExit ret) (segAddr Extracted.program fn) [c, p, len, cp] s)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)) (hokr : HdrOkR R b len)
    (hrecv : s.mem.readLE c.toNat 3 = 65793) (hokn : R.ok (cA "runtime.newobject") [errT])
    (hcostE : 3 * makeCost 4 + allocCost 16 ≤ b)
    (Q : Janus.Amd64.Outcome → Prop)
    (hErr : ∀ S' : State, (1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2) →
      ABIReturn s S' → ErrRet S' → RunFrame R b (3 * makeCost 4 + allocCost 16) L s S' → Q (.returned S'))
    (hZero : ∀ S' : State, hdrV s p len 0 = 0 → hdrV s p len 1 ≤ 1024 → hdrV s p len 2 = 0 →
      ABIReturn s S' → S'.regs 3 = 0#64 → S'.regs 7 = 0#64 → RunFrame R b (3 * makeCost 4) L s S' → Q (.returned S'))
    (hk : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 : Nat), RelH R b L c p len cp s ret 3 L1 b1 S →
      ∀ T' : State, T'.rip = BitVec.ofNat 64 pcC0 → T'.mem = S.mem → T'.regs 4 = S.regs 4 →
      T'.regs 14 = S.regs 14 → T'.regs 5 = S.regs 5 → T'.xmm 15 = S.xmm 15 → T'.fsBase = S.fsBase → T'.df = S.df →
      hdrV s p len 0 ≤ 1024 → hdrV s p len 1 ≤ 1024 → hdrV s p len 2 ≤ 1024 →
      ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0) →
      (T'.regs 1).toNat = hdrV s p len 0 → (T'.regs 13).toNat = hdrV s p len 1 → (T'.regs 0).toNat = hdrV s p len 2 →
      (T'.regs 3).toNat = p.toNat + (if 96 < len.toNat then 96 else 0) →
      (T'.regs 7).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0) → (T'.regs 9).toNat = len.toNat - 96 →
      Reaches ((LibRun.program.link impl).withExit ret) T' Q) :
    Reaches ((LibRun.program.link impl).withExit ret) s Q :=
  h1 impl hap R hmk hmv b L c p len cp ret hret s hs henv hin hinv hokr Q fun S1 L1 b1 hr1 hp1 =>
    h2 impl hap R hmk hmv b L c p len cp ret hret s hs.zero hs.df henv hin hokr Q (fun S2 L2 b2 hr2 hp2 =>
      h3 impl hap R hmk hmv b L c p len cp ret hret s hs.zero hs.df henv hin hokr Q (fun S3 L3 b3 hr3 hp3 hq0 hq1 =>
        la impl hap R b L c p len cp ret hret s henv Q S3 L3 b3 hr3 hp3 hq0 hq1
          (fun T hTpc hTm hT4 hT14 hT5 hTx hTfs hTdf hL0 hL1 hL2 =>
            lb impl hap R hno b L c p len cp ret hret s hs.df henv hin hrecv hokn hcostE Q S3 L3 b3 hr3 T hTpc hTm hT4
              hT14 hT5 hTx hTfs hTdf hL0 hL1 hL2 hErr hZero (hk S3 L3 b3 hr3)))
        S2 L2 b2 hr2 hp2)
      S1 L1 b1 hr1 hp1

end FvModexp.Amd64.Run
