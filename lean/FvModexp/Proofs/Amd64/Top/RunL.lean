import FvModexp.Proofs.Amd64.Top.RunLLo
import FvModexp.Proofs.Amd64.Top.RunLHi

/-! # `Run` (amd64): `P1` to `C0` — composition of `lbLo` (`len ≤ 96`) and `lbHi` (`96 < len`) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
theorem lb (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (hrecv : s.mem.readLE c.toNat 3 = 65793) (hokn : R.ok (cA "runtime.newobject") [errT])
    (hcostE : 3 * makeCost 4 + allocCost 16 ≤ b)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 3 L1 b1 S)
    (T : State) (hTpc : T.rip = BitVec.ofNat 64 pcP1) (hTm : T.mem = S.mem) (hT4 : T.regs 4 = S.regs 4)
    (hT14 : T.regs 14 = S.regs 14) (hT5 : T.regs 5 = S.regs 5) (hTx : T.xmm 15 = S.xmm 15)
    (hTfs : T.fsBase = S.fsBase) (hTdf : T.df = S.df)
    (hL0 : LenRegs (hdrV s p len 0) (T.regs 2) (T.regs 10)) (hL1 : LenRegs (hdrV s p len 1) (T.regs 9) (T.regs 13))
    (hL2 : LenRegs (hdrV s p len 2) (T.regs 11) (T.regs 0))
    (hErr : ∀ S' : State, (1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2) →
      ABIReturn s S' → ErrRet S' → RunFrame R b (3 * makeCost 4 + allocCost 16) L s S' → Q (.returned S'))
    (hZero : ∀ S' : State, hdrV s p len 0 = 0 → hdrV s p len 1 ≤ 1024 → hdrV s p len 2 = 0 →
      ABIReturn s S' → S'.regs 3 = 0#64 → S'.regs 7 = 0#64 → RunFrame R b (3 * makeCost 4) L s S' → Q (.returned S'))
    (hk : ∀ T' : State, T'.rip = BitVec.ofNat 64 pcC0 → T'.mem = S.mem → T'.regs 4 = S.regs 4 →
      T'.regs 14 = S.regs 14 → T'.regs 5 = S.regs 5 → T'.xmm 15 = S.xmm 15 → T'.fsBase = S.fsBase → T'.df = S.df →
      hdrV s p len 0 ≤ 1024 → hdrV s p len 1 ≤ 1024 → hdrV s p len 2 ≤ 1024 →
      ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0) →
      (T'.regs 1).toNat = hdrV s p len 0 → (T'.regs 13).toNat = hdrV s p len 1 → (T'.regs 0).toNat = hdrV s p len 2 →
      (T'.regs 3).toNat = p.toNat + (if 96 < len.toNat then 96 else 0) →
      (T'.regs 7).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0) → (T'.regs 9).toNat = len.toNat - 96 →
      Reaches ((LibRun.program.link impl).withExit ret) T' Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  by_cases h96 : len.toNat ≤ 96
  · exact lbLo impl hap R hno b L c p len cp ret hret s hdf0 henv hin hrecv h96 hokn hcostE Q S L1 b1 hrel T hTpc hTm hT4 hT14 hT5 hTx hTfs hTdf hL0 hL1 hL2 hErr hZero hk
  · exact lbHi impl hap R hno b L c p len cp ret hret s hdf0 henv hin hrecv (by omega) hokn hcostE Q S L1 b1 hrel T hTpc hTm hT4 hT14 hT5 hTx hTfs hTdf hL0 hL1 hL2 hErr hZero hk

end FvModexp.Amd64.Run
