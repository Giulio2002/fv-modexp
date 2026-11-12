import FvModexp.Proofs.Arm64.Exp.EvCost
import FvModexp.Proofs.Arm64.Exp.EvEP
import FvModexp.Proofs.Arm64.Exp.EvN1
import FvModexp.Proofs.Arm64.Exp.EvLsh
import FvModexp.Proofs.Arm64.Exp.EvN2
import FvModexp.Proofs.Arm64.Exp.EvRsh
import FvModexp.Proofs.Arm64.Exp.EvN3
import FvModexp.Proofs.Arm64.Exp.EvE1
import FvModexp.Proofs.Arm64.Exp.EvN4
import FvModexp.Proofs.Arm64.Exp.EvE2
import FvModexp.Proofs.Arm64.Exp.EvSet
import FvModexp.Proofs.Arm64.Exp.EvSmS
import FvModexp.Proofs.Arm64.Exp.EvMi
import FvModexp.Proofs.Arm64.Exp.EvM1
import FvModexp.Proofs.Arm64.Exp.EvTr
import FvModexp.Proofs.Arm64.Exp.EvM2
import FvModexp.Proofs.Arm64.Exp.EvFin

set_option autoImplicit false

/-!
# **`nat.expNNEven`** (go-bigmodexpfix nat.go:801-847), arm64 — the summary (agent infra)

`body`: from `EPre` at the entry, the 16 segments `seg1 → J1 → segL → … → segAdd → J15 → segFin` with the budget
chain `r1 … r15` (each segment consumes its worst-case cost, `costE` = their sum) and the stack bounds from `needE`.
`full`: the `Summary` on `LibNE` (`.full` form: no return-address condition — the recursive pair expNN ↔ expNNEven)
from `ExpEven.Pre` (`epre_of`, `zw_of`). `sum`: the export `EvenSum impl R stk 112 (needE …) (costE …)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

open StackNat (rnd)

/-! ### small arithmetic facts (kept out of the big contexts) -/

theorem bud_chain {c1' c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 b b1 C : Nat}
    {r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Nat} (h1' : c1' ≤ c1)
    (hC : C = c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15) (hcost : C ≤ b)
    (hb1 : b - c1' ≤ b1) (e15 : r15 = b - C) (e14 : r14 = c15 + r15) (e13 : r13 = c14 + r14) (e12 : r12 = c13 + r13)
    (e11 : r11 = c12 + r12) (e10 : r10 = c11 + r11) (e9 : r9 = c10 + r10) (e8 : r8 = c9 + r9) (e7 : r7 = c8 + r8)
    (e6 : r6 = c7 + r7) (e5 : r5 = c6 + r6) (e4 : r4 = c5 + r5) (e3 : r3 = c4 + r4) (e2 : r2 = c3 + r3)
    (e1 : r1 = c2 + r2) : r1 ≤ b1 := by omega

theorem c1_le_b {c1' c1 C b : Nat} (h1' : c1' ≤ c1) {c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : Nat}
    (hC : C = c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15) (hcost : C ≤ b) :
    c1' ≤ b := by omega

theorem max2_le {l1 l2 ml : Nat} (h1 : l1 ≤ ml) (h2 : l2 ≤ ml) : 2 * max l1 l2 ≤ 2 * ml := by omega

theorem alloc_le {c C : Nat} (h : c ≤ C) : allocCost (8 * c) ≤ allocCost (8 * C) := by unfold allocCost; omega

section
variable {needR : Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {ℓ0 xl yl ml : Nat}

theorem need1 (hneed : ℓ0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) {a : Nat} (ha : a ≤ ml) :
    ℓ0 + a + 3 ≤ 2 ^ 16 := by unfold needE at hneed; omega

theorem need2 (hneed : ℓ0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) {a c : Nat} (ha : a ≤ ml) (hc : c ≤ ml) :
    ℓ0 + rnd a + c + 3 ≤ 2 ^ 16 := by
  have := rnd_mono ha; unfold needE at hneed; omega

theorem need3 (hneed : ℓ0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) {l : Nat} (hl : l ≤ wL4 ℓ0 ml) :
    l + 2 * ml + 3 ≤ 2 ^ 16 := by unfold needE at hneed; simp only [wL4, wL3, wL2] at hl; omega

theorem needMi (hneed : ℓ0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) {l w : Nat} (hl : l ≤ wL4 ℓ0 ml)
    (hw : w ≤ ml) : l + 8 * w + 72 ≤ 2 ^ 16 := by
  unfold needE at hneed; simp only [wL4, wL3, wL2] at hl; omega

theorem needM (hneed : ℓ0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) {l : Nat} (hl : l ≤ wL4 ℓ0 ml) :
    l + 8 * ml + 64 ≤ 2 ^ 16 := by unfold needE at hneed; simp only [wL4, wL3, wL2] at hl; omega

end

theorem wL3_le (ℓ0 ml : Nat) : wL3 ℓ0 ml ≤ wL4 ℓ0 ml := by simp only [wL4]; omega
theorem wL2_le (ℓ0 ml : Nat) : wL2 ℓ0 ml ≤ wL4 ℓ0 ml := by simp only [wL4, wL3]; omega
theorem wL0_le (ℓ0 ml : Nat) : ℓ0 ≤ wL4 ℓ0 ml := by simp only [wL4, wL3, wL2]; omega

theorem costE_eq (costF : Nat → Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat) (bU cU : Nat → Nat → Nat → Nat → Nat → Nat) (sqC : Nat → Nat → Nat) (mlC mlG : Nat → Nat → Nat → Nat)
    (ℓ0 xl yl ml : Nat) :
    costE costF costR costS costP bU cU sqC mlC mlG ℓ0 xl yl ml =
      stackNatCost ℓ0 ml + makeB (ml + 1) + stackNatCost (ℓ0 + rnd ml) ml + makeB ml +
        stackNatCost (wL2 ℓ0 ml) (2 * ml) + eC costF costR costS costP bU cU xl yl ml (wL3 ℓ0 ml) +
        stackNatCost (wL3 ℓ0 ml) (2 * ml) + eC costF costR costS costP bU cU xl yl ml (wL4 ℓ0 ml) +
        allocCost (8 * (ml + 4)) + SubMod2N.costG (64 * ml) +
        ModInv.cost (sqC (wL4 ℓ0 ml)) (mlC (wL4 ℓ0 ml)) (64 * ml) + mlG (wL4 ℓ0 ml) ml ml + makeB (2 * ml) +
        mlG (wL4 ℓ0 ml) ml ml + makeB (ml + 1) := rfl

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc ret : Nat}
    {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the body**: from `EPre` at the entry to `RET` with the post `FQ` -/
theorem body {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ K) (haN : aboveN ≤ 88)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ K) (haL : aboveL ≤ 88)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (hkR : stkR ≤ K) (haR : aboveR ≤ 88)
    {KN : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    (hE : EvenHyp.ExpNNHypNE1 impl R KN costF needR costR needS needP costS costP)
    (hKN : 4304 ≤ KN) (hKN1 : KN + 1312 ≤ K) (hKN2 : KN + 288 ≤ 2 ^ 20)
    (hmv : MemmoveLive (LibNE.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive (LibNE.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract (LibNE.program.link impl) mkE 4096 R)
    (hSE : SubMod2N.EnsG impl R) (hK4 : 4608 ≤ K)
    {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} (hMi : MiEns impl R kc sqC mlC)
    (hKc : 240 + kc ≤ K) (hkc : 4608 ≤ kc)
    {stkM aboveM : Nat} {mlG : Nat → Nat → Nat → Nat} (hmu : MulHypG impl R ns stkM aboveM mlG)
    (hkM : stkM ≤ K) (haM : aboveM ≤ 88)
    (htr : TrHyp0 impl R ns 4208 64) (hadd : AddHypR0 impl R)
    (hRm : ∀ x a a', a ≤ a' → needR x a ≤ needR x a')
    (hSm : ∀ x y a a', a ≤ a' → needS x y a ≤ needS x y a')
    (hPm : ∀ x y a a', a ≤ a' → needP x y a ≤ needP x y a')
    {bU cU : Nat → Nat → Nat → Nat → Nat → Nat}
    (hNB : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      NBudE costF costR costS costP x y a l k ≤ bU x y a' l' k')
    (hNC : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      ExpN.NCost costF costR costS costP x y a l k ≤ cU x y a' l' k')
    (hsm : ∀ ℓ ℓ' a a', ℓ ≤ ℓ' → a ≤ a' → sqC ℓ a ≤ sqC ℓ' a')
    (hmm : ∀ ℓ ℓ' a a' c c', ℓ ≤ ℓ' → a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ' a' c')
    (hgm : ∀ ℓ ℓ' a a' c c', ℓ ≤ ℓ' → a ≤ a' → c ≤ c' → mlG ℓ a c ≤ mlG ℓ' a' c')
    (zl : Nat) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) (hzw : Outside zp (8 * zc) [(sp - K, sp + 448)])
    (hneed : stLen s.mem st + needE needR needS needP xl yl ml ≤ 2 ^ 16)
    (hcost : costE costF costR costS costP bU cU sqC mlC mlG (stLen s.mem st) xl yl ml ≤ b)
    (hr4 : ret % 4 = 0) (hr48 : ret < 2 ^ 48) (hzl : zl < 2 ^ 64)
    (hpc : s.pc = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc)
    (h3 : s.regs 3 = BitVec.ofNat 64 st) (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 xl)
    (h6 : s.regs 6 = BitVec.ofNat 64 xc) (h7 : s.regs 7 = BitVec.ofNat 64 yp) (h8 : s.regs 8 = BitVec.ofNat 64 yl)
    (h9 : s.regs 9 = BitVec.ofNat 64 yc) (h10 : s.regs 10 = BitVec.ofNat 64 mp)
    (h11 : s.regs 11 = BitVec.ofNat 64 ml) (h12 : s.regs 12 = BitVec.ofNat 64 mc)
    (h30 : s.regs 30 = BitVec.ofNat 64 ret) :
    ReachesRet (LibNE.program.link impl) (BitVec.ofNat 64 ret) s
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp ml)
        (costE costF costR costS costP bU cU sqC mlC mlG (stLen s.mem st) xl yl ml) s) := by
  obtain ⟨hn0, hn⟩ := nE_bd hP hM hev
  have ha1 : a1 (nE s mp ml) ≤ ml := by simp only [a1]; omega
  have ha2 : a2 ml (nE s mp ml) ≤ ml := by simp only [a2]; omega
  have hnw : nE s mp ml ≤ 64 * ml := Nat.le_of_lt hn
  have hNW : ModInv.NW (nE s mp ml) ≤ ml := by simp only [ModInv.NW]; omega
  have ha11 : a1 (nE s mp ml) + 1 ≤ ml + 1 := Nat.succ_le_succ ha1
  have hml40 : ml < 2 ^ 40 := by have := hP.2.2.2.2.2.2.1; omega
  have hC := costE_eq costF costR costS costP bU cU sqC mlC mlG (stLen s.mem st) xl yl ml
  generalize costE costF costR costS costP bU cU sqC mlC mlG (stLen s.mem st) xl yl ml = cE at hC hcost ⊢
  obtain ⟨r15, e15⟩ : ∃ r, r = b - cE := ⟨_, rfl⟩
  obtain ⟨r14, e14⟩ : ∃ r, r = makeB (ml + 1) + r15 := ⟨_, rfl⟩
  obtain ⟨r13, e13⟩ : ∃ r, r = mlG (wL4 (stLen s.mem st) ml) ml ml + r14 := ⟨_, rfl⟩
  obtain ⟨r12, e12⟩ : ∃ r, r = makeB (2 * ml) + r13 := ⟨_, rfl⟩
  obtain ⟨r11, e11⟩ : ∃ r, r = mlG (wL4 (stLen s.mem st) ml) ml ml + r12 := ⟨_, rfl⟩
  obtain ⟨r10, e10⟩ : ∃ r, r = ModInv.cost (sqC (wL4 (stLen s.mem st) ml)) (mlC (wL4 (stLen s.mem st) ml))
    (64 * ml) + r11 := ⟨_, rfl⟩
  obtain ⟨r9, e9⟩ : ∃ r, r = SubMod2N.costG (64 * ml) + r10 := ⟨_, rfl⟩
  obtain ⟨r8, e8⟩ : ∃ r, r = allocCost (8 * (ml + 4)) + r9 := ⟨_, rfl⟩
  obtain ⟨r7, e7⟩ : ∃ r, r = eC costF costR costS costP bU cU xl yl ml (wL4 (stLen s.mem st) ml) + r8 := ⟨_, rfl⟩
  obtain ⟨r6, e6⟩ : ∃ r, r = stackNatCost (wL3 (stLen s.mem st) ml) (2 * ml) + r7 := ⟨_, rfl⟩
  obtain ⟨r5, e5⟩ : ∃ r, r = eC costF costR costS costP bU cU xl yl ml (wL3 (stLen s.mem st) ml) + r6 := ⟨_, rfl⟩
  obtain ⟨r4, e4⟩ : ∃ r, r = stackNatCost (wL2 (stLen s.mem st) ml) (2 * ml) + r5 := ⟨_, rfl⟩
  obtain ⟨r3, e3⟩ : ∃ r, r = makeB ml + r4 := ⟨_, rfl⟩
  obtain ⟨r2, e2⟩ : ∃ r, r = stackNatCost (stLen s.mem st + rnd ml) ml + r3 := ⟨_, rfl⟩
  obtain ⟨r1, e1⟩ : ∃ r, r = makeB (ml + 1) + r2 := ⟨_, rfl⟩
  have hc1 : stackNatCost (stLen s.mem st) (a1 (nE s mp ml)) ≤ stackNatCost (stLen s.mem st) ml :=
    stackNatCost_mono (Nat.le_refl _) ha1
  refine seg1 hap hns hnf hsn haN (BitVec.ofNat 64 ret) _ b L K g sp st zp zl zc xp xl xc yp yl yc mp ml mc ret s hP
    hkN hM (Nat.le_trans hc1 (c1_le_b (Nat.le_refl _) hC hcost)) (need1 hneed ha1) hr48 hzl hpc h0 h1 h2 h3 h4 h5 h6
    h7 h8 h9 h10 h11 h12 h30 ?_
  intro S L1 b1 p f0 f1 f2 f3 f4 g0 g1 g2 hw hsl h224 hscr hp hb1
  have hJ1 : J1 R L K g sp st zp zc xp xl xc yp yl yc mp ml mc ret s r1 S L1 b1 p :=
    ⟨⟨f1, f2, f3, f4, hw, hsl, bud_chain hc1 hC hcost hb1 e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1⟩, f0,
      g0, g1, g2, h224, DL.of_scr hw hscr hp (Nat.add_le_add_left (rnd_ge (a1 (nE s mp ml))) _)
      (Nat.lt_of_le_of_lt ha1 hml40)⟩
  refine segL hap hns hnf hlh hkL haL hP hM hev (rk' := r2) (rk_le (makeCost_le ha11) e1) ?_ hJ1
  intros; rename_i h
  refine segN2 hap hns hnf hsn hkN haN hP hM hev (need2 hneed ha1 ha2) (rk' := r3)
    (rk_le (stackNatCost_mono (Nat.add_le_add_left (rnd_mono ha1) _) ha2) e2) ?_ h
  intros; rename_i h
  refine segR hap hns hnf hrh hkR haR hP hM hev (rk' := r4) (rk_le (makeCost_le ha2) e3) ?_ h
  intros; rename_i h
  refine segN3 hap hns hnf hsn hkN haN hP hM hev (need3 hneed (Nat.le_trans (ℓ2_le hn) (wL2_le _ _)))
    (rk' := r5) (fun l1 l2 q1 q2 => rk_le (stackNatCost_mono (ℓ2_le hn) (max2_le q1 q2)) e4) ?_ h
  intros; rename_i h
  refine segE1 hap hE hKN hKN1 hKN2 hP hM hev
    (fun l1 l2 q1 q2 => nstkE_of hRm hSm hPm hneed (Nat.le_trans (ℓ3_le hn q1 q2) (wL3_le _ _)) q1 hnw)
    (rk' := r6) (fun l1 l2 q1 q2 => rk_le2 (hNB xl yl l1 ml _ _ _ _ q1 (ℓ3_le hn q1 q2) hnw)
      (hNC xl yl l1 ml _ _ _ _ q1 (ℓ3_le hn q1 q2) hnw) e5) ?_ h
  intros; rename_i h
  refine segN4 hap hns hnf hsn hkN haN hP hM hev
    (fun l1 l2 q1 q2 => need3 hneed (Nat.le_trans (ℓ3_le hn q1 q2) (wL3_le _ _))) (rk' := r7)
    (fun l1 l2 q1 q2 => rk_le (stackNatCost_mono (ℓ3_le hn q1 q2) (max2_le q1 q2)) e6) ?_ h
  intros; rename_i h
  refine segE2 hap hE hKN hKN1 hKN2 hP hM hev
    (fun l1 l2 q1 q2 => nstkE_of hRm hSm hPm hneed (ℓ4_le hn q1 q2) q2 (lg2_le s mp ml))
    (rk' := r8) (fun l1 l2 q1 q2 => rk_le2 (hNB xl yl l2 ml _ _ _ _ q2 (ℓ4_le hn q1 q2) (lg2_le s mp ml))
      (hNC xl yl l2 ml _ _ _ _ q2 (ℓ4_le hn q1 q2) (lg2_le s mp ml)) e7) ?_ h
  intros; rename_i h
  refine segSet hmv hmz hmk hP hM hev (rk' := r9) (fun c hc => rk_le (alloc_le hc) e8) ?_ h
  intros; rename_i h
  refine segSm hap hSE hK4 hP hM hev (rk' := r10) (rk_le (costG_mono hnw) e9) ?_ h
  intros; rename_i h
  refine segMi hap hMi hKc hkc hP hM hev
    (fun l1 l2 q1 q2 => needMi hneed (ℓ4_le hn q1 q2) hNW) (rk' := r11)
    (fun l1 l2 q1 q2 => rk_le (miCost_mono (fun a a' ha => hsm _ _ a a' (ℓ4_le hn q1 q2) ha)
      (fun a a' c c' ha hc => hmm _ _ a a' c c' (ℓ4_le hn q1 q2) ha hc) hn0 hnw) e10) ?_ h
  intros; rename_i h
  refine segM1 hap hns hnf hmu hkM haM hP hM hev (fun l1 l2 q1 q2 => needM hneed (ℓ4_le hn q1 q2)) (rk' := r12)
    (fun l1 l2 a c q1 q2 qa qc => rk_le (hgm _ _ a ml c ml (ℓ4_le hn q1 q2) qa qc) e11) ?_ h
  intros; rename_i h
  refine segTr hap hns hnf htr hP hM hev (rk' := r13) (fun k hk => rk_le (makeCost_le hk) e12) ?_ h
  intros; rename_i h
  refine segM2 hap hns hnf hmu hkM haM hP hM hev (fun l1 l2 q1 q2 => needM hneed (ℓ4_le hn q1 q2)) (rk' := r14)
    (fun l1 l2 a c q1 q2 qa qc => rk_le (hgm _ _ a ml c ml (ℓ4_le hn q1 q2) qa qc) e13) ?_ h
  intros; rename_i h
  refine segAdd hap hadd (by omega) hP hM hzw (rk' := r15) (fun k hk => rk_le (makeCost_le hk) e14) ?_ h
  intros; rename_i h
  exact segFin hap hP hM hev hr4 hr48 (by rw [e15]; exact Nat.le_refl _) h

end

end FvModexp.Arm64.ExpEven
