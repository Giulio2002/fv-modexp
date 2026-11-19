import FvModexp.Proofs.Amd64.NatQ.DivCG
import FvModexp.Proofs.Amd64.Exp.MontW
import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.W4Defs
import FvModexp.Proofs.Amd64.Exp.W2Defs
import FvModexp.Proofs.Common.StackPot
import FvModexp.Proofs.Amd64.SetRetLemmas

set_option autoImplicit false

/-!
# `nat.div` (amd64) as the windows' / `expNNOdd`'s / `expNN`'s premise `ExpHyp.DivHypL` (agent expmc s66; twin of
`Arm64.DivInst` + the `nat.div` part of `Arm64.Q` Bridge)

top's CLOSED Q-form `nat.div` (`Q.NatDiv.ensCL : ExpHyp.DivHypLQ impl R names 41512 112 (costQ drsCQ)`, NatQ/DivCG.lean:
only live runtime contracts on `Extracted.program.ofImpl impl` remain) bridged to the level-cost form the windows take
(`divL_of_Q`: reserve level `H := stLen + 16·len u + 64` per call, cost `C ul vl + stkRes (ℓ + 16·ul + 64)`), as on
arm64 (ExpQ/Bridge `divL_of_Q`). Plus the name facts the callers' statements ask of `nsD`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.DivInst

theorem divpre_setRet_ppp (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < ul) (hg1 : 0 < zc.toNat) (hg2 : 0 < z2c.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  simp only [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.forall_mem_pair2] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, hg2, false_implies, true_implies]

theorem divpre_setRet_ppn (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < ul) (hg1 : 0 < zc.toNat) (hg2 : ¬ 0 < z2c.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  simp only [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.forall_mem_pair2] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, hg2, false_implies, true_implies]

theorem divpre_setRet_pp (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < ul) (hg1 : 0 < zc.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  by_cases hg2 : 0 < z2c.toNat
  · exact divpre_setRet_ppp R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hg2 hp
  · exact divpre_setRet_ppn R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hg2 hp

theorem divpre_setRet_pnp (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < ul) (hg1 : ¬ 0 < zc.toNat) (hg2 : 0 < z2c.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  simp only [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.forall_mem_pair2] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, hg2, false_implies, true_implies]

theorem divpre_setRet_pnn (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < ul) (hg1 : ¬ 0 < zc.toNat) (hg2 : ¬ 0 < z2c.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  simp only [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.forall_mem_pair2] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, hg2, false_implies, true_implies]

theorem divpre_setRet_pn (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < ul) (hg1 : ¬ 0 < zc.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  by_cases hg2 : 0 < z2c.toNat
  · exact divpre_setRet_pnp R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hg2 hp
  · exact divpre_setRet_pnn R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hg2 hp

theorem divpre_setRet_p (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : 0 < ul)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  by_cases hg1 : 0 < zc.toNat
  · exact divpre_setRet_pp R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hp
  · exact divpre_setRet_pn R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hp

theorem divpre_setRet_npp (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ul = 0) (hg1 : 0 < zc.toNat) (hg2 : 0 < z2c.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  simp only [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.forall_mem_pair2] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, hg2, false_implies, true_implies]

theorem divpre_setRet_npn (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ul = 0) (hg1 : 0 < zc.toNat) (hg2 : ¬ 0 < z2c.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  simp only [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.forall_mem_pair2] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, hg2, false_implies, true_implies]

theorem divpre_setRet_np (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ul = 0) (hg1 : 0 < zc.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  by_cases hg2 : 0 < z2c.toNat
  · exact divpre_setRet_npp R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hg2 hp
  · exact divpre_setRet_npn R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hg2 hp

theorem divpre_setRet_nnp (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ul = 0) (hg1 : ¬ 0 < zc.toNat) (hg2 : 0 < z2c.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  simp only [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.forall_mem_pair2] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, hg2, false_implies, true_implies]

theorem divpre_setRet_nnn (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ul = 0) (hg1 : ¬ 0 < zc.toNat) (hg2 : ¬ 0 < z2c.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  simp only [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.forall_mem_pair2] at hp ⊢
  janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.ExpHyp.DivPre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.StkOK, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, hg0, hg1, hg2, false_implies, true_implies]

theorem divpre_setRet_nn (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ul = 0) (hg1 : ¬ 0 < zc.toNat)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  by_cases hg2 : 0 < z2c.toNat
  · exact divpre_setRet_nnp R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hg2 hp
  · exact divpre_setRet_nnn R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hg2 hp

theorem divpre_setRet_n (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) (hg0 : ul = 0)
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  by_cases hg1 : 0 < zc.toNat
  · exact divpre_setRet_np R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hp
  · exact divpre_setRet_nn R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hg0 hg1 hp

theorem divpre_setRet (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (hab : 8 ≤ above) (s : State) (ret : Nat) {p : Janus.Amd64.Program} {entry : Nat} {args : List W64} (hs : CallSetup0 entry args s) (hret : RetAddr p ret) 
    (hp : FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s) :
    FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc (s.setRet ret) := by
  by_cases hg0 : 0 < ul
  · exact divpre_setRet_p R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret  hg0 hp
  · exact divpre_setRet_n R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret  (Nat.eq_zero_of_not_pos hg0) hp

/-- `ExpHyp.DivPre` survives writing the return address (the `hinv` of `divL_of_Q`; `8 ≤ above`: the return slot lies in the window above `RSP`, which is what
keeps the stack header `st` and the operands apart from it): the empty dividend (`ul = 0`) and `0 < zc` / `0 < z2c` are case-split, one declaration per case
(`divpre_setRet_<ul><zc><z2c>`), the quantifier over the two results is expanded (`forall_mem_pair2`). -/
theorem divpre_inv (R : RtInv) (b : Nat) (cost : Nat → Nat → Nat → Nat) (L : List (Nat × Nat)) (stk above : Nat) (hab : 8 ≤ above)
    (z zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (p : Janus.Amd64.Program) (entry : Nat) (args : List W64) :
    Ensures.SetRetInv p entry args (fun s => FvModexp.Amd64.ExpHyp.DivPre R b cost L stk above z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat
      u ul uc v vl vc s) :=
  fun s ret hs hret hp => divpre_setRet R b cost L stk above z zl zc st z2 z2l z2c u ul uc v vl vc hab s ret hs hret hp

/-- an `Ensures` for every reserve level gives one whose level is a function of the entry state -/
theorem ens_param {p : Amd64.Program} {e : Nat} {args : List (BitVec 64)} {pre : Nat → State → Prop}
    {post : Nat → State → State → Prop} {pre' : State → Prop} {post' : State → State → Prop}
    (h : ∀ H, Ensures p e args (pre H) (post H)) (f : State → Nat) (hpre : ∀ s, pre' s → pre (f s) s)
    (hpost : ∀ s s', post (f s) s s' → post' s s') (hinv : Ensures.SetRetInv p e args pre' := by janus64_pre_setRet) : Ensures p e args pre' post' := by
  refine Ensures.of_old hinv ?_
  exact (fun ret hret s hs hp => ((h (f s)).toOld ret hret s hs (hpre s hp)).mono fun _ h' => ⟨h'.1, hpost _ _ h'.2⟩)

theorem bud_br {b b' C H r r' : Nat} (hr : r ≤ stkRes H) (h : b - (C + r) + r' ≤ b') : b - (C + stkRes H) ≤ b' := by
  omega

theorem cost_br {b C H : Nat} {m : Janus.Arm64.Memory} {st : Nat} (h : C + stkRes H ≤ b) : C + stkR H m st ≤ b :=
  Nat.le_trans (Nat.add_le_add_left (stkR_le H m st) C) h

/-- the bridged cost of `nat.div` (level bound `16·len u + 64`) -/
@[reducible] def divBr (C : Nat → Nat → Nat) (l ul vl : Nat) : Nat := C ul vl + stkRes (l + 16 * ul + 64)

set_option maxRecDepth 20000 in
open FvModexp.Amd64.ExpHyp in
/-- **`nat.div`**: `DivHypLQ` gives `DivHypL` at the cost `C ul vl + stkRes (ℓ + 16·ul + 64)` -/
theorem divL_of_Q {impl : List Amd64.Segment} {R : RtInv} {ns : List String} {stk above : Nat} {C : Nat → Nat → Nat}
    (h : DivHypLQ impl R ns stk above C) (hab : 8 ≤ above := by omega) : DivHypL impl R ns stk above (divBr C) := by
  intro b L z zl zc st z2 z2l z2c u ul uc v vl vc
  refine ens_param (fun H => h H b L z zl zc st z2 z2l z2c u ul uc v vl vc)
    (fun s => stLen s.mem st.toNat + 16 * ul + 64) (fun s hp => ?_) (fun s s' hq => ?_)
    (divpre_inv R b (divBr C) L stk above hab z zl zc st z2 z2l z2c u ul uc v vl vc _ _ _)
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
      h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, hc, h40, h41, hinv⟩ := hp
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
      h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, ⟨Nat.le_refl _, cost_br hc⟩,
      h40, h41, hinv⟩
  · obtain ⟨hf, hd, q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b', hq, hr, ⟨hLE, hb, hinv⟩, hsb, ha, hfr, hl⟩ := hq
    exact ⟨hf, hd, q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b', hq, hr,
      ⟨hLE, bud_br (stkR_le _ _ _) hb, hinv⟩, hsb, ha, hfr, hl⟩

/-- the cost function of the closed `nat.div` in the level-cost form -/
abbrev divC : Nat → Nat → Nat → Nat := divBr (Q.NatDiv.costQ Q.drsCQ)

/-- `nat.div` (amd64), every callee discharged, `ExpHyp.DivHypL` form (program `Q.NatDiv.names`, window 41512 / 112) -/
theorem hyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (hmk0 : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv0 : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz0 : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    ExpHyp.DivHypL impl R Q.NatDiv.names 41512 112 divC :=
  divL_of_Q (Q.NatDiv.ensCL impl hap R hgr hmc hwb hmk0 hmv0 hmz0)

set_option maxHeartbeats 64000000 in
theorem ns_sub : ∀ x, Q.NatDiv.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide +kernel)

theorem ns_w4 : Q.NatDiv.names.contains W4Loop.fn = false := by decide

theorem ns_w2 : Q.NatDiv.names.contains W2Loop.fn = false := by decide

end FvModexp.Amd64.DivInst
