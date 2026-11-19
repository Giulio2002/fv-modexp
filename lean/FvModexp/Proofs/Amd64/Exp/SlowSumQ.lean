import FvModexp.Proofs.Amd64.Exp.SlowFunQ
import FvModexp.Proofs.Amd64.Exp.SlowEP

set_option autoImplicit false

/-!
# **`nat.expNNSlow`** amd64 — the Q-form export `Q.ExpSlow.hyp : NHyp.SlowHypQ …` (agent expmc s82; twin of arm64
`Arm64/ExpQ/SlowSumQ.hyp`)

`hyp`: `SlowHypQ impl R LibW.names stk 0x70 need needH (costQ sqrCQ mulCQ dvC)` for every frame depth
`41512 + 0x1b8 ≤ stk ≤ 2^20 + 0x1b8` covering the callee windows (`stk - 0x1b8` = the window below the frame), from
`bodyQ` (`epre_of`); the value by `Exp.expNNSlow_correct` (`2 ≤ y`, `0 < m`). Premises: the callee shapes on a
program `ns ⊆ LibW.names` without `nat.expNNSlow` (`SqrE0`, `MulHypQE`, `DivHypLGQ`) and the live `makeslice` /
`memmove` contracts of the whole extraction.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.ExpSlow

open FvModexp.Amd64.ExpSlow
open Janus.Contracts.EqHashModel (CodeIn64)

theorem bvT (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`nat.expNNSlow`** (amd64): `z.expNNSlow(stk, x, y, m) = x^y mod m` (see the module doc) -/
theorem hyp {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false)
    {W1 W2 W3 : Nat} {dvC : Nat → Nat → Nat}
    (hsq : SqrE0 impl R ns W1) (hW1 : 7104 ≤ W1)
    (hml : Q.DivRec.MulHypQE impl R ns W2) (hW2 : mulWX64 ≤ W2)
    (hdv : DivHypLGQ impl R ns W3 0x70 dvC)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {stk : Nat} (hk1 : 41512 + 0x1b8 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x1b8)
    (hW1K : W1 ≤ stk - 0x1b8) (hW2K : W2 ≤ stk - 0x1b8) (hW3K : W3 ≤ stk - 0x1b8) :
    NHyp.SlowHypQ impl R LibW.names stk 0x70 need needH (costQ sqrCQ mulCQ dvC) := by
  have h1b8 : 0x1b8 ≤ stk := by omega
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  have hmkL : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R := by
    rw [show mkE = cA "runtime.makeslice" by decide]; exact MakesliceLiveContract64.of_codeIn hc hmk
  have hmvL : MemmoveLive64 (LibW.program.link impl) mvE 4096 R := by
    rw [show mvE = cA "runtime.memmove" by decide]; exact MemmoveLive64.of_codeIn hc hmv
  have hmzL : MemmoveZeroLive64 (LibW.program.link impl) mvE 4096 R := by
    rw [show mvE = cA "runtime.memmove" by decide]; exact MemmoveZeroLive64.of_codeIn hc hmz
  intro H b L z zl zc st x xl xc y yl yc m ml mc
  rw [← LibW.eq_only, ← fn_eq, fnBaseX]
  janus64_ensures_old [FvModexp.Amd64.NHyp.StkArg, FvModexp.Amd64.NHyp.CPre, FvModexp.stkR, FvModexp.natVal, FvModexp.stLen, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.StackNat.wT, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.NatNorm, FvModexp.Amd64.NHyp.freeOf, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.stkRes, FvModexp.potK, FvModexp.Amd64.TlsOK, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK]
  intro ret hret s hs hp
  janus64_intro hs
  obtain ⟨⟨hy, hm⟩, ⟨hC, hX0, hY, hM, hst⟩, hX, hH0⟩ := hp
  have hH : stLen s.mem st.toNat + 48 * max xl.toNat ml + 64 ≤ H := by
    rw [Nat.add_assoc]; exact hH0
  have hP := epre_of hC hM hY hst hk1 hk2 z.isLt xc.isLt h_x15 h_df hy hm (by rw [h_ret]; exact hret.user)
  have hcst : costQ sqrCQ mulCQ dvC xl.toNat yl ml + stkR H s.mem st.toNat ≤ b := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hC
    exact h
  have hS : Summary (LibW.program.link impl) fnE (fun t => t = s)
      (fun _ s' => FQS R b H L (stk - 0x1b8) z.toNat zc.toNat st.toNat
        (Exp.expNNSlow (natVal s.mem x.toNat xl.toNat) (natVal s.mem y yl) (natVal s.mem m ml))
        (costQ sqrCQ mulCQ dvC xl.toNat yl ml) s s') := by
    intro t _ ht
    subst ht
    exact bodyQ hap hns hnf hsq hW1K hW1 hml hW2K hW2 hdv hW3K hmkL hmvL hmzL hP hX hX0 hM hH hcst
      h_rip (h_a0.trans (bvT _).symm) (h_a2.trans (bvT _).symm) (h_a3.trans (bvT _).symm)
      (h_a4.trans (bvT _).symm) (h_a5.trans (bvT _).symm) (h_a6.trans (bvT _).symm)
  refine Summary.returns hS hret h_rip (by rw [retAddrOf, h_ret]) rfl fun s' ⟨⟨a, b', c, d⟩, hq⟩ => ⟨⟨a, b', c, d⟩, ?_⟩
  rw [Nat.sub_add_cancel h1b8, Exp.expNNSlow_correct _ _ _ hY,
    ite_eq_right (Nat.pos_iff_ne_zero.mp hM)] at hq
  exact hq

end FvModexp.Amd64.Q.ExpSlow
