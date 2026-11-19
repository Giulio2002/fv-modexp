import FvModexp.Proofs.Amd64.Exp.P2DFull
import FvModexp.Proofs.Amd64.Exp.P2DEInv

set_option autoImplicit false

/-!
# **`nat.expNNPowerOfTwo`** (amd64): `P2D.ens : NHyp.P2Hyp …` (agent asm s71; twin of infra's arm64 `P2DE`)

The `Ensures` form of `sumF` on the restricted program `LibW.names` (the caller `nat.expNN` is outside it), from the live
`makeslice` contract of the whole extraction, the two window summaries (`WSum`, on `LibW.program.link impl`) and the
`rsh` / `lsh` callee shapes on a program `ns ⊆ LibW.names` without `expNNPowerOfTwo`. Window `[RSP - stk, RSP + 112)`,
stack need `needP` (`2^13`), budget `costP c2 c4`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open Janus.Contracts.EqHashModel (CodeIn64)
open FvModexp.Amd64.ExpHyp FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`expNNPowerOfTwo`** (amd64): `z = x^y mod 2^logM` for every positive `x`, `y` and `1 ≤ logM ≤ 2^13` -/
theorem ens {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    {kW2 kW4 : Nat} {c2 c4 : Nat → Nat → Nat → Nat} (hW2 : WSum impl R w2E kW2 c2) (hW4 : WSum impl R w4E kW4 c4)
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains NHyp.fnP2 = false)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (haR : aboveR ≤ 0x60)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (haL : aboveL ≤ 0x60)
    (stk : Nat) (hk1 : 4320 + 0x78 ≤ stk) (hkW2 : kW2 + 0xf0 ≤ stk) (hkW4 : kW4 + 0xf0 ≤ stk)
    (hk2 : stk ≤ 2 ^ 20 + 0x78) (hkR : stkR + 0x78 ≤ stk) (hkL : stkL + 0x78 ≤ stk) :
    NHyp.P2Hyp impl R LibW.names stk 112 needP (costP c2 c4) := by
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibW.names
  have hmkL : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R := by
    rw [show mkE = cA "runtime.makeslice" by decide]; exact MakesliceLiveContract64.of_codeIn hc hmk
  intro b L z zl zc st x xl xc lm y yl yc
  have hS := sumF hap hmkL hW2 hW4 hns hnf hrh haR hlh haL b L stk 112 hk1 hkW2 hkW4 hk2 hkR hkL (by decide)
    z.toNat zl.toNat zc.toNat st.toNat x.toNat xl.toNat xc.toNat y yl yc lm.toNat
  rw [← LibW.eq_only, fnE_eq]
  refine Ensures.of_old (NHyp.p2pre_inv R b L stk 112 needP (costP c2 c4) z zl zc st x xl xc lm y yl yc (by decide) _ _ _) ?_
  intro ret hret s hs ⟨hy, hP, hxl, hxc, hX1, hX2, hX3, _⟩
  janus64_intro hs
  refine Summary.returns hS hret h_rip (by rw [retAddrOf, h_ret])
    ⟨⟨h_a0.trans (bv_tn _).symm, h_a1.trans (bv_tn _).symm, h_a2.trans (bv_tn _).symm, h_a3.trans (bv_tn _).symm,
      h_a4.trans (bv_tn _).symm, h_a5.trans (bv_tn _).symm, h_a6.trans (bv_tn _).symm, h_a7.trans (bv_tn _).symm,
      hy⟩, hP, ⟨h_x15, h_df, z.isLt⟩, hxl, hxc, ⟨hX1, hX2, hX3⟩, by rw [h_ret]; exact hret.user⟩
    fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

end FvModexp.Amd64.P2D
