import FvModexp.Proofs.Arm64.Exp.EvFull

set_option autoImplicit false

/-!
# **`nat.expNNEven`** arm64 — the export `EvenSum` (agent infra)

`full`: `ExpEven.EvenSum impl R stk 112 (needE needR needS needP) (costE costF costR costS costP sqC mlC mlG)` for every
frame depth `stk` that covers the callees (`stk - 336` = the window below the function's frame), from `body`
(`epre_of`, `zw_of`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

variable {R : RtInv}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`nat.expNNEven`** (arm64): the export (see the module doc) -/
theorem full {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN)  (haN : aboveN ≤ 88)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL)  (haL : aboveL ≤ 88)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR)  (haR : aboveR ≤ 88)
    {KN : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    (hE : EvenHyp.ExpNNHypNE1 impl R KN costF needR costR needS needP costS costP)
    (hKN : 4304 ≤ KN)  (hKN2 : KN + 288 ≤ 2 ^ 20)
    (hmv : MemmoveLive (LibNE.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive (LibNE.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract (LibNE.program.link impl) mkE 4096 R)
    (hSE : SubMod2N.EnsG impl R) 
    {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} (hMi : MiEns impl R kc sqC mlC)
     (hkc : 4608 ≤ kc)
    {stkM aboveM : Nat} {mlG : Nat → Nat → Nat → Nat} (hmu : MulHypG impl R ns stkM aboveM mlG)
     (haM : aboveM ≤ 88)
    (htr : TrHyp0 impl R ns 4208 64) (hadd : AddHypR0 impl R)
    (hRm : ∀ x a a', a ≤ a' → needR x a ≤ needR x a')
    (hSm : ∀ x y a a', a ≤ a' → needS x y a ≤ needS x y a')
    (hPm : ∀ x y a a', a ≤ a' → needP x y a ≤ needP x y a')
    (hNB : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      NBudE costF costR costS costP x y a l k ≤ NBudE costF costR costS costP x y a' l' k')
    (hNC : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      ExpN.NCost costF costR costS costP x y a l k ≤ ExpN.NCost costF costR costS costP x y a' l' k')
    (hsm : ∀ ℓ ℓ' a a', ℓ ≤ ℓ' → a ≤ a' → sqC ℓ a ≤ sqC ℓ' a')
    (hmm : ∀ ℓ ℓ' a a' c c', ℓ ≤ ℓ' → a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ' a' c')
    (hgm : ∀ ℓ ℓ' a a' c c', ℓ ≤ ℓ' → a ≤ a' → c ≤ c' → mlG ℓ a c ≤ mlG ℓ' a' c')
    {stk : Nat} (hk1 : 4640 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 336)
    (hK : stkN ≤ stk - 336 ∧ stkL ≤ stk - 336 ∧ stkR ≤ stk - 336 ∧ KN + 1312 ≤ stk - 336 ∧ 240 + kc ≤ stk - 336 ∧
      stkM ≤ stk - 336 ∧ 4608 ≤ stk - 336) :
    EvenSum impl R stk 112 (needE needR needS needP) (costE costF costR costS costP sqC mlC mlG) := by
  intro b L zp zl zc st xp xl xc yp yl yc mp ml mc s hpc hs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hPre, hzp, hxc, hyc, hr4, hr48⟩ := hs
  have hP := epre_of hPre hk1 hk2 hzp hxc hyc
  have hle : stk ≤ s.sp.toNat := hPre.1.1.2.1.2.1
  have hzw := zw_of hPre (by omega) hle
  have hneed := hPre.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcost := hPre.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzl : zl < 2 ^ 64 := by
    have := hPre.1.2.2.2.2.2.1; have := hPre.1.2.2.2.2.2.2.1.1; omega
  have hM := hPre.2.2.2.1
  have hev := hPre.2.2.2.2.1
  have h30 : s.regs 30 = BitVec.ofNat 64 (s.regs 30).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hK
  have hb := body hap hns hnf hsn k1 haN hlh k2 haL hrh k3 haR hE hKN k4 hKN2 hmv hmz hmk hSE k7 hMi k5 hkc hmu k6 haM
    htr hadd hRm hSm hPm hNB hNC hsm hmm hgm zl hP hM hev hzw hneed hcost hr4 hr48 hzl hpc h0 h1 h2 h3 h4 h5 h6 h7 h8
    h9 h10 h11 h12 h30
  rw [← h30] at hb
  obtain ⟨k, s', hs', hr', q1, q2, q3, q4, q5⟩ := hb
  rw [Nat.sub_add_cancel (by omega : 336 ≤ stk)] at q5
  exact ⟨k, s', hs', hr', q1, q2, q3, q4, q5⟩

end FvModexp.Arm64.ExpEven
