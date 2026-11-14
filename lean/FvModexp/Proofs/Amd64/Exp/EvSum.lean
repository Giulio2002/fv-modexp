import FvModexp.Proofs.Amd64.Exp.EvFull
import FvModexp.Proofs.Amd64.Exp.EvEP
import FvModexp.Proofs.Amd64.Exp.EvMiEns

set_option autoImplicit false

/-!
# **`nat.expNNEven`** amd64 — the export `EvenSum` (asm s65; twin of infra's arm64 `EvSum`)

`full`: `ExpEven.EvenSum impl R stk 0x70 (needE needR needS needP) (costE bU cU sqrC mulC)` for every frame depth
`stk` that covers the callees (`stk - 0x150` = the window below the function's frame), from `body` (`epre_of`,
`zw_of`, `xc_of`). The `ModInv` premise `MiEns` is discharged by `miEns_of` from infra's amd64 `ModInv.ens`; its
callee premises (`nat.sqr`/`nat.trunc`/`nat.mul`/`nat.lsh` Q-forms on sub-programs of `LibW`, `subMod2N`'s calls,
`makeslice`/`growslice`) become `full`'s.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

variable {R : RtInv}

open FvModexp.Amd64.ModInv in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`nat.expNNEven`** (amd64): the export (see the module doc) -/
theorem full {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (haN : aboveN ≤ 0x7f)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (haL : aboveL ≤ 0x7f)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (haR : aboveR ≤ 0x7f)
    {KN : Nat} {costF : Nat → Nat → Nat → Nat} {cDf : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    (hE : ∀ costD, EvenHyp.ExpNNHypNE1 impl R KN costF costD needR costR needS needP costS costP)
    (hKN : 41640 ≤ KN) (hKN2 : KN + 0x98 ≤ 2 ^ 20)
    (hmv : MemmoveLive64 (LibNE.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive64 (LibNE.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibNE.program.link impl) mkE 4096 R)
    (hSE : SubMod2N.EnsG impl R)
    -- `ModInv` (infra's amd64 `ModInv.ens` premises, through `miEns_of`)
    {nsS nsT nsM nsL : List String} (hnsS : ∀ x, nsS.contains x = true → LibW.names.contains x = true)
    (hnsT : ∀ x, nsT.contains x = true → LibW.names.contains x = true)
    (hnsM : ∀ x, nsM.contains x = true → LibW.names.contains x = true)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true)
    (hnfS : nsS.contains ModInv.fn = false) (hnfT : nsT.contains ModInv.fn = false)
    (hnfM : nsM.contains ModInv.fn = false) (hnfL : nsL.contains ModInv.fn = false)
    (hnfTS : nsT.contains SubMod2N.fn = false)
    (hmkW : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : SubMod2N.K ≤ kc)
    {kS : Nat} (hsq : SqrE impl R nsS kS) (hkS : kS ≤ kc) (hkS1 : sqrW 513 ≤ kS)
    {stkT aboveT : Nat} (htrW : Trunc.Hyp2 impl R nsT stkT aboveT) (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80)
    {kM : Nat} (hmuW : Q.DivRec.MulHypQE impl R nsM kM) (hkM : kM ≤ kc) (hkM1 : mulWX64 ≤ kM)
    {stkLW aboveLW : Nat} (hlsW : Lsh.Hyp2 impl R nsL stkLW aboveLW) (hkLW : stkLW ≤ kc) (haLW : aboveLW ≤ 88)
    (hsub : SubMod2N.SubHypR0 impl R) (haddW : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    (hsmQ : ∀ a a', a ≤ a' → sqrCQ a ≤ sqrC a') (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmmQ : ∀ a a' c, a ≤ a' → mulCQ a c ≤ mulC a' c)
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    -- the body's own `nat.mul` / `nat.trunc` / `nat.add` calls
    {W : Nat} (hmu : Q.DivRec.MulHypQE impl R ns W) (hWX : mulWX64 ≤ W)
    (htr : TrHyp0 impl R ns 4192 64) (hadd : AddHypR0 impl R)
    (hRm : ∀ x a a', a ≤ a' → needR x a ≤ needR x a')
    (hSm : ∀ x y a a', a ≤ a' → needS x y a ≤ needS x y a')
    (hPm : ∀ x y a a', a ≤ a' → needP x y a ≤ needP x y a')
    {bU cU : Nat → Nat → Nat → Nat → Nat → Nat}
    (hNB : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      NBudO (cDf x a l) costR costS costP x y a l k ≤ bU x y a' l' k')
    (hNC : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      ExpN.NCost (cDf x a l) costR costS costP x y a l k ≤ cU x y a' l' k')
    (hFD : ∀ x lm lv l' a, x ≤ 128 → lm ≤ 128 → l' ≤ lv + needO x lm → (a ≤ 2 * lm + 1 ∨ a ≤ x) →
      costF l' a lm ≤ cDf x lm lv)
    {stk : Nat} (hk1 : 42816 + 0x150 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x150)
    (hK : stkN ≤ stk - 0x150 ∧ stkL ≤ stk - 0x150 ∧ stkR ≤ stk - 0x150 ∧ KN + 0x498 ≤ stk - 0x150 ∧
      232 + kc ≤ stk - 0x150 ∧ W ≤ stk - 0x150) :
    EvenSum impl R stk 0x70 (needE needR needS needP) (costE bU cU sqrC mulC) := by
  have hMi := miEns_of hap hnsS hnsT hnsM hnsL hnfS hnfT hnfM hnfL hnfTS hmkW hkc hsq hkS hkS1 htrW hkT haT hmuW hkM
    hkM1 hlsW hkLW haLW hsub haddW hgr hsmQ hsm hmmQ
  intro b L zp zl zc st xp xl xc yp yl yc mp ml mc s hpc hs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hy, hm, hPre, hzp, hxc, hyc, hr47, hX, hXG, hXw⟩ := hs
  have hle : stk ≤ (s.regs 4).toNat := hPre.1.1.2.1.1
  have hP := epre_of hPre hk1 hk2 hzp hxc hyc h0 h1 hy hm hr47
  have hzw := zw_of hPre (by omega) hle
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · have := hPre.2.1; subst h; simp [natVal] at this
    · exact h
  have hXC := xc_of (by omega) hle hxl0 hX hXG hXw
  have hneed := hPre.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcost := hPre.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hM := hPre.2.2.2.1
  have hev := hPre.2.2.2.2.1
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hK
  have hb := body hap hns hnf hsn k1 haN hlh k2 haL hrh k3 haR hE hKN k4 hKN2 hmv hmz hmk hSE hMi k5 hmu hWX k6
    htr hadd hRm hSm hPm hNB hNC hFD hsm hmm hP hM hev hX hXC hXG hzw hneed hcost hpc h2 h4 h5 h6 h7 h8
  have e : stk - 0x150 + 0x150 = stk := by omega
  exact ReachesRet.mono hb (fun s' h => by simp only [FQ] at h; rw [e] at h; exact h)

end FvModexp.Amd64.ExpEven
