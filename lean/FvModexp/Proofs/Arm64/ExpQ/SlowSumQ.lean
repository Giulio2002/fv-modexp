import FvModexp.Proofs.Arm64.ExpQ.SlowFunQ
import FvModexp.Proofs.Arm64.Exp.SlowSum

set_option autoImplicit false

/-! (Q-form copy of Exp/SlowSum.lean, TIGHT COSTS, agent expmc s43)
# **`nat.expNNSlow`** arm64 — the Q-form export `Q.ExpSlow.hyp : NHyp.SlowHypQ …` (agent expmc s43)

`hyp`: `SlowHypA impl R LibW.names stk 112 need (cost sqC mlC dvC)` (NHyp's `SlowHyp` + `SlowX`, post `CPostR0`) for
every frame depth `4736 ≤ stk ≤ 2^20 + 432` covering the callees (`stk - 432` = the window below the frame), from
`body` (`epre_of`) via `ensures_of_summary`; the value by `Exp.expNNSlow_correct` (`2 ≤ y`, `0 < m`).
Premises: the callee shapes on a program `ns ⊆ LibW.names` without `nat.expNNSlow` — `SqrHypG` (= `sqrG`, from
divmc's `NatSqr.ens`), `MulHypG` (infra, from `NatMul.ens`), `DivHypLG` (asm, requested) — and the live `makeslice` /
`memmove` contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`nat.expNNSlow`** (arm64): `z.expNNSlow(stk, x, y, m) = x^y mod m` (see the module doc) -/
theorem hyp {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS aS kM aM kD aD : Nat} {sqC : Nat → Nat} {mlC dvC : Nat → Nat → Nat}
    (hsq : SqrHypGQ impl R ns kS aS sqC) (hmu : MulHypGQ impl R ns kM aM mlC) (hdv : DivHypLGQ impl R ns kD aD dvC)
    (haS : aS ≤ 120) (haM : aM ≤ 120) (haD : aD ≤ 120)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {stk : Nat} (hk1 : 4736 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 432)
    (hkS : kS ≤ stk - 432) (hkM : kM ≤ stk - 432) (hkD : kD ≤ stk - 432) :
    NHyp.SlowHypQ impl R LibW.names stk 112 need needH (costQ sqC mlC dvC) := by
  intro H b L z zl zc st x xl xc y yl yc m ml mc
  have hc := codeIn_ofImpl_restrict_of_apart hap LibW.names
  rw [← LibW.eq_only] at hc
  have hmk' : MakesliceLiveContract (LibW.program.link impl) mkA 4096 R := by
    rw [← mkA_eq]; exact MakesliceLiveContract.of_codeIn hc hmk
  have hmv' : MemmoveLive (LibW.program.link impl) mvE 4096 R := by
    rw [show mvE = Extracted.program.contractAddr "runtime.memmove" from mvA_eq.symm]
    exact MemmoveLive.of_codeIn hc hmv
  rw [← LibW.eq_only, fn_addr]
  refine AsmDiv.A64.ensures_of_summary _ _
    (pre := fun s => ((Pre R b L stk 112 (fun _ a c d => costQ sqC mlC dvC a c d + stkR H s.mem st.toNat) z.toNat
        zl.toNat zc.toNat st.toNat x.toNat xl.toNat y.toNat yl.toNat m.toNat ml.toNat s ∧
        SlowX R L x.toNat xl.toNat xc.toNat ∧ stLen s.mem st.toNat + needH xl.toNat ml.toNat ≤ H) ∧
      (s.regs 0 = z ∧ s.regs 1 = zl ∧ s.regs 2 = zc ∧ s.regs 3 = st ∧ s.regs 4 = x ∧ s.regs 5 = xl ∧
        s.regs 6 = xc ∧ s.regs 7 = y ∧ s.regs 8 = yl ∧ s.regs 9 = yc ∧ s.regs 10 = m ∧ s.regs 11 = ml ∧
        s.regs 12 = mc)) ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48)
    (post := fun s s' => FQQ R b H L (stk - 432) z.toNat zc.toNat st.toNat
      (Exp.expNNSlow (natVal s.mem x.toNat xl.toNat) (natVal s.mem y.toNat yl.toNat) (natVal s.mem m.toNat ml.toNat))
      (costQ sqC mlC dvC xl.toNat yl.toNat ml.toNat) s s') ?_ ?_ ?_
  · intro s hpc ⟨⟨⟨hPre, hX, hH⟩, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, hr4, hr48⟩
    have hP := epre_of (cost := fun _ a c d => costQ sqC mlC dvC a c d + stkR H s.mem st.toNat) hPre mc.isLt hk1 hk2
      z.isLt xc.isLt yc.isLt
    have hcst : costQ sqC mlC dvC xl.toNat yl.toNat ml.toNat + stkR H s.mem st.toNat ≤ b :=
      hPre.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact bodyQ hap hns hnf hsq hmu hdv hkS haS hkM haM hkD haD hmk' hmv' hP hX hPre.2.1 hPre.2.2.2.1 (by simp only [needH] at hH; omega) hcst zl.isLt
      hr4 hr48 hpc (by rw [h0, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h1, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [h2, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h3, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [h4, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h5, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [h6, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h7, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [h8, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h9, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [h10, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [h11, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [h12, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  · intro ret hret s hsu hpre
    have hlr := hsu.lr
    have hr : (s.regs 30).toNat = ret := by
      have := congrArg BitVec.toNat hlr
      simp only [Program.withExit, BitVec.toNat_ofNat] at this
      rw [this]; exact Nat.mod_eq_of_lt (by have := hret.user; omega)
    refine ⟨⟨⟨hpre.1, hpre.2.1, hpre.2.2⟩, hsu.args 0 (by simp), hsu.args 1 (by simp), hsu.args 2 (by simp), hsu.args 3 (by simp),
      hsu.args 4 (by simp), hsu.args 5 (by simp), hsu.args 6 (by simp), hsu.args 7 (by simp),
      hsu.args 8 (by simp), hsu.args 9 (by simp), hsu.args 10 (by simp), hsu.args 11 (by simp),
      hsu.args 12 (by simp)⟩, by rw [hr]; exact hret.aligned, by rw [hr]; exact hret.user⟩
  · intro ret hret s hsu hpre s' ⟨q1, q2, q3, q4, q5⟩
    refine ⟨⟨q1, q3, q4, q2⟩, ?_⟩
    obtain ⟨⟨-, -, hY, hM, -⟩, -⟩ := hpre
    rw [Nat.sub_add_cancel (by omega : 432 ≤ stk), Exp.expNNSlow_correct _ _ _ hY,
      ite_eq_right (by omega : ¬ natVal s.mem m.toNat ml.toNat = 0)] at q5
    exact q5

end FvModexp.Arm64.Q.ExpSlow
