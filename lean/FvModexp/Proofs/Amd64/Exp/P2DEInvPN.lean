import FvModexp.Proofs.Amd64.Exp.P2DEPre
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-! `P2PreS` (= `P2Hyp`'s precondition) survives installing the return address (Janus v0.4.0 `hinv` of `P2D.ens`, top s53):
the `∃ op` (`natOne`) is pulled out and the operand list expanded first; `XGc` reads the `natOne` word, apart from the
return slot by `NatOne`'s `Outside natOneA 24 (win …)`. Case `PN` of the guards `0 < zc`, `0 < stCap` (one module per case). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.NHyp

open FvModexp.Amd64.ExpHyp (stWs)

set_option maxHeartbeats 16000000 in
theorem p2pre_setRet_pn (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat → Nat) (z zl zc st x xl xc lm : BitVec 64) (y yl yc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {e : Nat} {args : List W64} (hs : CallSetup0 e args s) (hret : RetAddr p ret) (h2 : 0 < zc.toNat) (h3 : ¬ 0 < stCap s.mem st.toNat)
    (hp : P2PreS R b L stk above need cost z zl zc st x xl xc lm y yl yc s) : P2PreS R b L stk above need cost z zl zc st x xl xc lm y yl yc (s.setRet ret) := by
  have hnA : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne» + 8 ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne» := by
    obtain ⟨-, ⟨-, -, -, -, -, -, op, hN, -⟩, -⟩ := hp
    have h := hN.2.2.2.2.2.2.1
    simp only [EvenHyp.natOneA, win, outside_append, outside_cons, outside_nil, and_true] at h
    have := hab
    omega
  simp only [P2PreS] at hp ⊢
  simp only [FvModexp.Amd64.NHyp.StkArg, FvModexp.Amd64.NHyp.CPre, FvModexp.stLen, FvModexp.natVal, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.win, FvModexp.Amd64.ExpHyp.stWs, FvModexp.Amd64.NHyp.StkApart, FvModexp.Amd64.NHyp.XGc, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.StackNat.wT, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.NatNorm, FvModexp.Amd64.NHyp.freeOf, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.EvenHyp.natOneA, FvModexp.stkWs, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK] at hp h3 ⊢
  simp only [forall_mem_pair2, ← exists_and_left, ← exists_and_right] at hp ⊢
  obtain ⟨op, hp⟩ := hp
  refine ⟨op, ?_⟩
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.NHyp.StkArg, FvModexp.Amd64.NHyp.CPre, FvModexp.stLen, FvModexp.natVal, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.win, FvModexp.Amd64.ExpHyp.stWs, FvModexp.Amd64.NHyp.StkApart, FvModexp.Amd64.NHyp.XGc, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.StackNat.wT, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.NatNorm, FvModexp.Amd64.NHyp.freeOf, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.EvenHyp.natOneA, FvModexp.stkWs, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, List.cons_append, List.nil_append, h2, h3, false_implies, true_implies]

end FvModexp.Amd64.NHyp
