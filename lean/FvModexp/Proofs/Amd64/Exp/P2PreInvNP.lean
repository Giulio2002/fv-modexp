import FvModexp.Proofs.Amd64.Exp.P2PreDefE
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-! `PreE` survives installing the return address (Janus v0.4.0 `hinv` of `ens`, top s53): the `∃ op` (`natOne`) is pulled
out first, the guards `0 < xl`, `0 < stCap` are case-split, one declaration per case.
This module: case `np` (one module per case keeps each compile small and lets them run in parallel). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

set_option maxHeartbeats 16000000 in
theorem preE_setRet_np {R : RtInv} {kc b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} (s : State) (ret : Nat) {p : Janus.Amd64.Program} {e : Nat} {args : List W64} (hs : CallSetup0 e args s) (hret : RetAddr p ret) (h1 : ¬ 0 < xl) (h2 : 0 < stCap s.mem st)
    (hp : PreE R kc b L st pw pl ws lm x xl s) : PreE R kc b L st pw pl ws lm x xl (s.setRet ret) := by
  simp only [FvModexp.Amd64.P2Pre.PreE, FvModexp.Amd64.CallEnv, FvModexp.Amd64.P2Pre.A, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.Q.NatSqr.guard, FvModexp.Amd64.Q.NatSqr.tls, FvModexp.Amd64.Q.NatSqr.StkSep, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.NatNorm, FvModexp.Amd64.Q.NatSqr.StkPre, FvModexp.stLen, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.P2Pre.LW, FvModexp.stkR, FvModexp.Amd64.NatAdd.wordT, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.wbA, FvModexp.Amd64.Q.BasicSqr.freeP, FvModexp.Amd64.Q.BasicSqr.freeN, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.EvenHyp.natOneA, FvModexp.stkWs, FvModexp.stkRes, FvModexp.potK, FvModexp.NatLive] at hp ⊢
  simp only [← exists_and_left, ← exists_and_right] at hp ⊢
  obtain ⟨op, hp⟩ := hp
  refine ⟨op, ?_⟩
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.P2Pre.PreE, FvModexp.Amd64.CallEnv, FvModexp.Amd64.P2Pre.A, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.Q.NatSqr.guard, FvModexp.Amd64.Q.NatSqr.tls, FvModexp.Amd64.Q.NatSqr.StkSep, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.NatNorm, FvModexp.Amd64.Q.NatSqr.StkPre, FvModexp.stLen, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.P2Pre.LW, FvModexp.stkR, FvModexp.Amd64.NatAdd.wordT, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.wbA, FvModexp.Amd64.Q.BasicSqr.freeP, FvModexp.Amd64.Q.BasicSqr.freeN, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.EvenHyp.natOneA, FvModexp.stkWs, FvModexp.stkRes, FvModexp.potK, FvModexp.NatLive, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, List.cons_append, List.nil_append, h1, h2, false_implies, true_implies]

end FvModexp.Amd64.P2Pre
