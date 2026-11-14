import FvModexp.Proofs.Amd64.Exp.EvCost
import FvModexp.Proofs.Amd64.Exp.EvN1
import FvModexp.Proofs.Amd64.Exp.EvLsh
import FvModexp.Proofs.Amd64.Exp.EvN2
import FvModexp.Proofs.Amd64.Exp.EvRsh
import FvModexp.Proofs.Amd64.Exp.EvN3
import FvModexp.Proofs.Amd64.Exp.EvE1
import FvModexp.Proofs.Amd64.Exp.EvN4
import FvModexp.Proofs.Amd64.Exp.EvE2
import FvModexp.Proofs.Amd64.Exp.EvSet
import FvModexp.Proofs.Amd64.Exp.EvSmS
import FvModexp.Proofs.Amd64.Exp.EvMi
import FvModexp.Proofs.Amd64.Exp.EvM1
import FvModexp.Proofs.Amd64.Exp.EvTr
import FvModexp.Proofs.Amd64.Exp.EvM2
import FvModexp.Proofs.Amd64.Exp.EvAdd
import FvModexp.Proofs.Amd64.Exp.EvFin

set_option autoImplicit false

/-!
# **`nat.expNNEven`** (go-bigmodexpfix nat.go:801-847), amd64 — the body (asm s65; port of infra's arm64 `EvFull`)

`body`: from `EPre` at the entry to `RET` with the post `FQ`: the 16 segments `seg1 → J1 → segL → … → segAdd → J15 →
segFin` with the budget chain `r1 … r15` (each segment consumes its worst-case cost; `costE` = their sum) and the
stack bounds from `needE`. The two `nat.expNN` calls (`segE1`, `segE2`) need, unlike arm64, the window budget
`ExpOdd.OBud` separately: `hNB` bounds `NBudO` (= `NBudE` max the window demand, `EvOB`) by `bU`, `obud_rk` +
`needO_of` (the `needE` part for the window levels) + `hFD` (`costF ≤ cDf xl lm lv` on the window divisions at
levels `≤ lv + needO xl lm`; asm s73: the division bound depends on the call's level `lv`, amd64 `EvCD.cD`) give it.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-! ### small arithmetic facts (kept out of the big contexts) -/

theorem bud1 {c1' c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 b C : Nat}
    {r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Nat} (h1' : c1' ≤ c1)
    (hC : C = c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 + c15) (hcost : C ≤ b)
    (e15 : r15 = b - C) (e14 : r14 = c15 + r15) (e13 : r13 = c14 + r14) (e12 : r12 = c13 + r13)
    (e11 : r11 = c12 + r12) (e10 : r10 = c11 + r11) (e9 : r9 = c10 + r10) (e8 : r8 = c9 + r9) (e7 : r7 = c8 + r8)
    (e6 : r6 = c7 + r7) (e5 : r5 = c6 + r6) (e4 : r4 = c5 + r5) (e3 : r3 = c4 + r4) (e2 : r2 = c3 + r3)
    (e1 : r1 = c2 + r2) : c1' + r1 ≤ b := by omega

theorem max2_le {l1 l2 ml : Nat} (h1 : l1 ≤ ml) (h2 : l2 ≤ ml) : 2 * max l1 l2 ≤ 2 * ml := by omega

theorem alloc_le {c C : Nat} (h : c ≤ C) : allocCost (8 * c) ≤ allocCost (8 * C) := by unfold allocCost; omega

theorem wL3_le (l0 ml : Nat) : wL3 l0 ml ≤ wL4 l0 ml := by simp only [wL4]; omega
theorem wL2_le (l0 ml : Nat) : wL2 l0 ml ≤ wL4 l0 ml := by simp only [wL4, wL3]; omega

theorem costE_eq (bU cU : Nat → Nat → Nat → Nat → Nat → Nat) (sqQ : Nat → Nat) (mlQ : Nat → Nat → Nat)
    (l0 xl yl ml : Nat) :
    costE bU cU sqQ mlQ l0 xl yl ml =
      stackNatCost l0 ml + makeB (ml + 1) + stackNatCost (l0 + StackNat.rnd ml) ml + makeB ml +
        stackNatCost (wL2 l0 ml) (2 * ml) + eC1 cU xl yl ml (wL3 l0 ml) +
        stackNatCost (wL3 l0 ml) (2 * ml) + eC2 bU cU xl yl ml (wL4 l0 ml) +
        allocCost (8 * (ml + 4)) + SubMod2N.costG (64 * ml) +
        (ModInv.cost sqQ mlQ ml (64 * ml) + stkRes (wL4 l0 ml + ModInv.D (64 * ml))) + mulE l0 ml +
        makeB (2 * ml) + mulE l0 ml + makeB (ml + 1) := rfl

theorem needMi {needR : Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {l0 xl yl ml l w : Nat}
    (hneed : l0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) (hl : l ≤ wL4 l0 ml) (hw : w ≤ ml) :
    l + 8 * w + 72 ≤ 2 ^ 16 := by
  have := need_lo hneed hl (k := 8 * ml + 72) (Nat.le_refl _); omega

theorem needM {needR : Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {l0 xl yl ml l : Nat}
    (hneed : l0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) (hl : l ≤ wL4 l0 ml) : l + 8 * ml + 64 ≤ 2 ^ 16 := by
  have := need_lo hneed hl (k := 8 * ml + 72) (Nat.le_refl _); omega

/-- the first `expNN` call's budget conjuncts (`segE1`'s `hrk`) -/
theorem e1_rk {costF : Nat → Nat → Nat → Nat} {costD : Nat} {costR : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat} {bU cU : Nat → Nat → Nat → Nat → Nat → Nat}
    {xl yl ml l1 lv n W3 W4 r5 r6 r7 r8 : Nat}
    (hB : NBudO costD costR costS costP xl yl l1 lv n ≤ bU xl yl ml W4 (64 * ml))
    (hC : ExpN.NCost costD costR costS costP xl yl l1 lv n ≤ cU xl yl ml W3 (64 * ml))
    (e5 : r5 = eC1 cU xl yl ml W3 + r6) {x : Nat} (e6 : r6 = x + r7) (e7 : r7 = eC2 bU cU xl yl ml W4 + r8)
    (hl : lv + needO xl l1 ≤ 2 ^ 16)
    (hF : ∀ l' a, l' ≤ lv + needO xl l1 → (a ≤ 2 * l1 + 1 ∨ a ≤ xl) → costF l' a l1 ≤ costD) :
    NBudE costR costS costP xl yl l1 lv n ≤ r5 ∧ ExpOdd.OBud costF l1 costD xl yl lv (r5 - makeCost l1) ∧
      ExpN.NCost costD costR costS costP xl yl l1 lv n + r6 ≤ r5 := by
  have h : NBudO costD costR costS costP xl yl l1 lv n ≤ r5 := by simp only [eC1, eC2] at e5 e7; omega
  exact ⟨(obud_rk h hl hF).1, (obud_rk h hl hF).2, by simp only [eC1] at e5; omega⟩

/-- the second `expNN` call's budget conjuncts (`segE2`'s `hrk`) -/
theorem e2_rk {costF : Nat → Nat → Nat → Nat} {costD : Nat} {costR : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat} {bU cU : Nat → Nat → Nat → Nat → Nat → Nat}
    {xl yl ml l2 lv n W4 r7 r8 : Nat}
    (hB : NBudO costD costR costS costP xl yl l2 lv n ≤ bU xl yl ml W4 (64 * ml))
    (hC : ExpN.NCost costD costR costS costP xl yl l2 lv n ≤ cU xl yl ml W4 (64 * ml))
    (e7 : r7 = eC2 bU cU xl yl ml W4 + r8) (hl : lv + needO xl l2 ≤ 2 ^ 16)
    (hF : ∀ l' a, l' ≤ lv + needO xl l2 → (a ≤ 2 * l2 + 1 ∨ a ≤ xl) → costF l' a l2 ≤ costD) :
    NBudE costR costS costP xl yl l2 lv n ≤ r7 ∧ ExpOdd.OBud costF l2 costD xl yl lv (r7 - makeCost l2) ∧
      ExpN.NCost costD costR costS costP xl yl l2 lv n + r8 ≤ r7 := by
  have h : NBudO costD costR costS costP xl yl l2 lv n ≤ r7 := by simp only [eC2] at e7; omega
  exact ⟨(obud_rk h hl hF).1, (obud_rk h hl hF).2, by simp only [eC2] at e7; omega⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the body**: from `EPre` at the entry to `RET` with the post `FQ` -/
theorem body {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ K) (haN : aboveN ≤ 0x7f)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (hkL : stkL ≤ K) (haL : aboveL ≤ 0x7f)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (hkR : stkR ≤ K) (haR : aboveR ≤ 0x7f)
    {KN : Nat} {costF : Nat → Nat → Nat → Nat} {cDf : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    (hE : ∀ costD, EvenHyp.ExpNNHypNE1 impl R KN costF costD needR costR needS needP costS costP)
    (hKN : 41640 ≤ KN) (hKN1 : KN + 0x498 ≤ K) (hKN2 : KN + 0x98 ≤ 2 ^ 20)
    (hmv : MemmoveLive64 (LibNE.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive64 (LibNE.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibNE.program.link impl) mkE 4096 R)
    (hSE : SubMod2N.EnsG impl R)
    {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} (hMi : MiEns impl R kc sqrC mulC) (hKc : 232 + kc ≤ K)
    {W : Nat} (hmu : Q.DivRec.MulHypQE impl R ns W) (hWX : mulWX64 ≤ W) (hWK : W ≤ K)
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
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmm : ∀ a a' c c', a ≤ a' → c ≤ c' → mulC a c ≤ mulC a' c')
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    (hev : natVal s.mem mp ml % 2 = 0) (hX : NHyp.XFacts R L xp xl xc) (hXC : XC R L sp K st s.mem xp xc)
    (hXG : ExpN.XG s.mem st xp xl xc) (hzw : Outside zp (8 * zc) [(sp - 8 - K, sp + 0x1b8)])
    (hneed : stLen s.mem st + needE needR needS needP xl yl ml ≤ 2 ^ 16)
    (hcost : costE bU cU sqrC mulC (stLen s.mem st) xl yl ml ≤ b)
    (hpc : s.rip = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zc) (h7 : s.regs 7 = BitVec.ofNat 64 st)
    (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 xl) (h9 : s.regs 9 = BitVec.ofNat 64 xc) :
    ReachesRet (LibNE.program.link impl) (BitVec.ofNat 64 r) s
      (FQ R b L K zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp ml)
        (costE bU cU sqrC mulC (stLen s.mem st) xl yl ml) s) := by
  obtain ⟨hn0, hn⟩ := nE_bd hP hM hev
  have ha1 : a1 (nE s mp ml) ≤ ml := by simp only [a1]; omega
  have ha2 : a2 ml (nE s mp ml) ≤ ml := by simp only [a2]; omega
  have hnw : nE s mp ml ≤ 64 * ml := Nat.le_of_lt hn
  have hNW : ModInv.NW (nE s mp ml) ≤ ml := by simp only [ModInv.NW]; omega
  have ha11 : a1 (nE s mp ml) + 1 ≤ ml + 1 := Nat.succ_le_succ ha1
  have hml : ml ≤ 128 := hP.2.2.2.2.2.1
  have hxl : xl ≤ 128 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hF : ∀ lm lv, lm ≤ ml → ∀ l' a, l' ≤ lv + needO xl lm → (a ≤ 2 * lm + 1 ∨ a ≤ xl) →
      costF l' a lm ≤ cDf xl lm lv :=
    fun lm lv hlm l' a hl ha => hFD xl lm lv l' a hxl (by omega) hl ha
  have hopA := hXG.2.1
  have hC := costE_eq bU cU sqrC mulC (stLen s.mem st) xl yl ml
  generalize costE bU cU sqrC mulC (stLen s.mem st) xl yl ml = cE at hC hcost ⊢
  obtain ⟨r15, e15⟩ : ∃ r, r = b - cE := ⟨_, rfl⟩
  obtain ⟨r14, e14⟩ : ∃ r, r = makeB (ml + 1) + r15 := ⟨_, rfl⟩
  obtain ⟨r13, e13⟩ : ∃ r, r = mulE (stLen s.mem st) ml + r14 := ⟨_, rfl⟩
  obtain ⟨r12, e12⟩ : ∃ r, r = makeB (2 * ml) + r13 := ⟨_, rfl⟩
  obtain ⟨r11, e11⟩ : ∃ r, r = mulE (stLen s.mem st) ml + r12 := ⟨_, rfl⟩
  obtain ⟨r10, e10⟩ : ∃ r, r = (ModInv.cost sqrC mulC ml (64 * ml) +
    stkRes (wL4 (stLen s.mem st) ml + ModInv.D (64 * ml))) + r11 := ⟨_, rfl⟩
  obtain ⟨r9, e9⟩ : ∃ r, r = SubMod2N.costG (64 * ml) + r10 := ⟨_, rfl⟩
  obtain ⟨r8, e8⟩ : ∃ r, r = allocCost (8 * (ml + 4)) + r9 := ⟨_, rfl⟩
  obtain ⟨r7, e7⟩ : ∃ r, r = eC2 bU cU xl yl ml (wL4 (stLen s.mem st) ml) + r8 := ⟨_, rfl⟩
  obtain ⟨r6, e6⟩ : ∃ r, r = stackNatCost (wL3 (stLen s.mem st) ml) (2 * ml) + r7 := ⟨_, rfl⟩
  obtain ⟨r5, e5⟩ : ∃ r, r = eC1 cU xl yl ml (wL3 (stLen s.mem st) ml) + r6 := ⟨_, rfl⟩
  obtain ⟨r4, e4⟩ : ∃ r, r = stackNatCost (wL2 (stLen s.mem st) ml) (2 * ml) + r5 := ⟨_, rfl⟩
  obtain ⟨r3, e3⟩ : ∃ r, r = makeB ml + r4 := ⟨_, rfl⟩
  obtain ⟨r2, e2⟩ : ∃ r, r = stackNatCost (stLen s.mem st + StackNat.rnd ml) ml + r3 := ⟨_, rfl⟩
  obtain ⟨r1, e1⟩ : ∃ r, r = makeB (ml + 1) + r2 := ⟨_, rfl⟩
  have hc1 : stackNatCost (stLen s.mem st) (a1 (nE s mp ml)) ≤ stackNatCost (stLen s.mem st) ml :=
    stackNatCost_mono (Nat.le_refl _) ha1
  refine seg1 hap hns hnf hsn haN (BitVec.ofNat 64 r) _ b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s hP
    hkN hM r1 (bud1 hc1 hC hcost e15 e14 e13 e12 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1) (need1 hneed ha1) hpc h0 h1 h7
    h6 h8 h9 ?_
  intro S L1 b1 p hJ1 _ _
  refine segL hap hns hnf hlh hkL haL hP hM hev (rk' := r2) (rk_le (makeCost_le ha11) e1) ?_ hJ1
  intros; rename_i h
  refine segN2 hap hns hnf hsn hkN haN hP hM hev (need2 hneed ha1 ha2) (rk' := r3)
    (rk_le (stackNatCost_mono (Nat.add_le_add_left (rnd_mono ha1) _) ha2) e2) ?_ h
  intros; rename_i h
  refine segR hap hns hnf hrh hkR haR hP hM hev (rk' := r4) (rk_le (makeCost_le ha2) e3) ?_ h
  intros; rename_i h
  refine segN3 hap hns hnf hsn hkN haN hP hM hev (need3 hneed (Nat.le_trans (l2_le hn) (wL2_le _ _)))
    (rk' := r5) (fun l1 l2 q1 q2 => rk_le (stackNatCost_mono (l2_le hn) (max2_le q1 q2)) e4) ?_ h
  intros; rename_i h
  refine segE1 hap hE (cDl := cDf xl) hKN hKN1 hKN2 hP hM hev hX hXC hXG
    (fun l1 l2 q1 q2 => nstkE_of hRm hSm hPm hneed (Nat.le_trans (l3_le hn q1 q2) (wL3_le _ _)) q1 hnw)
    (rk' := r6) (fun l1 l2 q1 q2 => e1_rk
      (hNB xl yl l1 ml _ _ _ _ q1 (Nat.le_trans (l3_le hn q1 q2) (wL3_le _ _)) hnw)
      (hNC xl yl l1 ml _ _ _ _ q1 (l3_le hn q1 q2) hnw) e5 e6 e7
      (needO_of hneed (Nat.le_trans (l3_le hn q1 q2) (wL3_le _ _)) q1) (hF l1 _ q1)) ?_ h
  intros; rename_i h
  refine segN4 hap hns hnf hsn hkN haN hP hM hev
    (fun l1 l2 q1 q2 => need3 hneed (Nat.le_trans (l3_le hn q1 q2) (wL3_le _ _))) (rk' := r7)
    (fun l1 l2 q1 q2 => rk_le (stackNatCost_mono (l3_le hn q1 q2) (max2_le q1 q2)) e6) ?_ h
  intros; rename_i h
  refine segE2 hap hE (cDl := cDf xl) hKN hKN1 hKN2 hP hM hev hX hXC hXG
    (fun l1 l2 q1 q2 => nstkE_of hRm hSm hPm hneed (l4_le hn q1 q2) q2 (lg2_le s mp ml))
    (rk' := r8) (fun l1 l2 q1 q2 => e2_rk (hNB xl yl l2 ml _ _ _ _ q2 (l4_le hn q1 q2) (lg2_le s mp ml))
      (hNC xl yl l2 ml _ _ _ _ q2 (l4_le hn q1 q2) (lg2_le s mp ml)) e7
      (needO_of hneed (l4_le hn q1 q2) q2) (hF l2 _ q2)) ?_ h
  intros; rename_i h
  refine segSet hmv hmz hmk hP hM hev (rk' := r9) (fun c hc => rk_le (alloc_le hc) e8) ?_ h
  intros; rename_i h
  refine segSm hap hSE hP hM hev (rk' := r10) (rk_le (costG_mono hnw) e9) ?_ h
  intros; rename_i h
  refine segMi hap hMi hKc hP hopA hM hev
    (fun l1 l2 q1 q2 => needMi hneed (l4_le hn q1 q2) hNW) (rk' := r11)
    (fun l1 l2 q1 q2 => rk_le (miB_mono hsm hmm q2 hn0 hnw (l4_le hn q1 q2)) e10) ?_ h
  intros; rename_i h
  refine segM1 hap hns hnf hmu hWX hWK hP hM hev (fun l1 l2 q1 q2 => needM hneed (l4_le hn q1 q2))
    (rk' := r12) (fun l1 l2 a c q1 q2 qa qc => rk_le (mul_le_mulE qa qc hml (l4_le hn q1 q2)) e11) ?_ h
  intros; rename_i h
  refine segTr hap hns hnf htr hP hM hev (rk' := r13) (fun k hk => rk_le (makeCost_le hk) e12) ?_ h
  intros; rename_i h
  refine segM2 hap hns hnf hmu hWX hWK hP hM hev (fun l1 l2 q1 q2 => needM hneed (l4_le hn q1 q2))
    (rk' := r14) (fun l1 l2 a c q1 q2 qa qc => rk_le (mul_le_mulE qa qc hml (l4_le hn q1 q2)) e13) ?_ h
  intros; rename_i h
  refine segAdd hap hadd hP hM hzw (rk' := r15) (fun k hk => rk_le (makeCost_le hk) e14) ?_ h
  intros; rename_i h
  exact segFin hap hP hM hev (by rw [e15]; exact Nat.le_refl _) h

end

end FvModexp.Amd64.ExpEven
