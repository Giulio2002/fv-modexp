import FvModexp.Proofs.Amd64.Exp.EvE2
import FvModexp.Proofs.Amd64.Exp.EvJ11
import FvModexp.Proofs.Amd64.Exp.SubMod2NG
import FvModexp.Proofs.Common.SqrCost
import FvModexp.Proofs.Common.MulCostQB

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the closed-form stack need `needE` and budget `costE` (asm s64; port of infra's arm64
`EvCost`)

Worst-case lengths `≤ ml` (as arm64), `n = tz M < 64 ml`, `log2 (M / 2^n) ≤ 64 ml`, monotonicity premises on the callee
needs / costs. `wL2/wL3/wL4` = the worst stack levels after `m1, m2` / `z1` / `z2`. amd64 differences: `NStkE` is
`l + 23 lm + 3`, `l + needR/needS/needP` (no rounding terms); the two `nat.mul` calls are charged in divmc's Q-form
(`mulCQ a c + stkRes (level + 8 ml + 64)`), `mulCQ` bounded by the box `mulB ml = 538 ml + 4912` (`mulCQ_le_box`,
`ml ≤ 128 < 157`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

@[reducible] def wL2 (l0 ml : Nat) : Nat := l0 + StackNat.rnd ml + StackNat.rnd ml
@[reducible] def wL3 (l0 ml : Nat) : Nat := wL2 l0 ml + StackNat.rnd (2 * ml)
@[reducible] def wL4 (l0 ml : Nat) : Nat := wL3 l0 ml + StackNat.rnd (2 * ml)

/-- the stack need (words above the entry level) -/
def needE (needR : Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat) (xl yl ml : Nat) : Nat :=
  2 * StackNat.rnd ml + 2 * StackNat.rnd (2 * ml) +
    (23 * ml + 3 + needR xl ml + needS xl yl ml + needP xl yl (64 * ml) + 8 * ml + 72 + 2 * ml + 3)

/-- the first `nat.expNN` call (`z1`, level `l`): its worst COST only (its budget is covered by the second call's) -/
@[reducible] def eC1 (cU : Nat → Nat → Nat → Nat → Nat → Nat) (xl yl ml l : Nat) : Nat := cU xl yl ml l (64 * ml)

/-- the second `nat.expNN` call (`z2`, level `l`): its worst budget and worst cost, whichever is larger -/
@[reducible] def eC2 (bU cU : Nat → Nat → Nat → Nat → Nat → Nat) (xl yl ml l : Nat) : Nat :=
  max (bU xl yl ml l (64 * ml)) (cU xl yl ml l (64 * ml))

/-- the box bound of a `nat.mul` Q-cost with operands `≤ ml` -/
@[reducible] def mulB (ml : Nat) : Nat := 538 * ml + 4912

/-- a `nat.mul` call at level `≤ wL4` (Q-form: cost + one reserve) -/
@[reducible] def mulE (l0 ml : Nat) : Nat := mulB ml + stkRes (wL4 l0 ml + 8 * ml + 64)

/-- the budget (entry stack level `l0`) -/
def costE (bU cU : Nat → Nat → Nat → Nat → Nat → Nat) (sqQ : Nat → Nat) (mlQ : Nat → Nat → Nat)
    (l0 xl yl ml : Nat) : Nat :=
  stackNatCost l0 ml + makeB (ml + 1) + stackNatCost (l0 + StackNat.rnd ml) ml + makeB ml +
    stackNatCost (wL2 l0 ml) (2 * ml) + eC1 cU xl yl ml (wL3 l0 ml) +
    stackNatCost (wL3 l0 ml) (2 * ml) + eC2 bU cU xl yl ml (wL4 l0 ml) +
    allocCost (8 * (ml + 4)) + SubMod2N.costG (64 * ml) +
    (ModInv.cost sqQ mlQ ml (64 * ml) + stkRes (wL4 l0 ml + ModInv.D (64 * ml))) + mulE l0 ml +
    makeB (2 * ml) + mulE l0 ml + makeB (ml + 1)

theorem zB_monoE {n n' : Nat} (h : n ≤ n') (j : Nat) : ModInv.zB n j ≤ ModInv.zB n' j := by
  unfold ModInv.zB; split
  · simp only [ModInv.NW]; omega
  · exact Nat.le_refl _

theorem makeCost_monoE {a b : Nat} (h : a ≤ b) (hb : 2 ≤ b) : makeCost a ≤ makeCost b := by
  unfold makeCost makeCap allocCost
  split <;> split <;> omega

theorem rnd_mono {a b : Nat} (h : a ≤ b) : StackNat.rnd a ≤ StackNat.rnd b := by unfold StackNat.rnd; omega

theorem makeB_mono {a b : Nat} (h : a ≤ b) : makeB a ≤ makeB b := by unfold makeB allocCost; omega

theorem makeCost_le {a b : Nat} (h : a ≤ b) : makeCost a ≤ makeB b :=
  Nat.le_trans (makeCost_le_makeB a) (makeB_mono h)

theorem costG_mono {n n' : Nat} (h : n ≤ n') : SubMod2N.costG n ≤ SubMod2N.costG n' := by
  have hW : SubMod2N.W n ≤ SubMod2N.W n' := by unfold SubMod2N.W; omega
  unfold SubMod2N.costG SubMod2N.gA SubMod2N.cost SubMod2N.wCost allocCost
  have := Nat.mul_le_mul hW (show 2 * (8 * (2 * SubMod2N.W n + 2)) + 24 ≤ 2 * (8 * (2 * SubMod2N.W n' + 2)) + 24 by
    omega)
  omega

theorem roundCost_mono {s1 : Nat → Nat} {m1 : Nat → Nat → Nat} (hs : ∀ a a', a ≤ a' → s1 a ≤ s1 a')
    (hm : ∀ a a' c c', a ≤ a' → c ≤ c' → m1 a c ≤ m1 a' c') {xl xl' n n' : Nat} (hx : xl ≤ xl') (h : n ≤ n')
    (j k : Nat) : ModInv.roundCost s1 m1 xl n j k ≤ ModInv.roundCost s1 m1 xl' n' j k := by
  have c6 := hs _ _ (zB_monoE h j)
  have hW : ModInv.NW n ≤ ModInv.NW n' := by unfold ModInv.NW; omega
  have c3 := makeCost_monoE (a := 2 * ModInv.NW n + 2) (b := 2 * ModInv.NW n' + 2) (by omega) (by omega)
  have c4 := makeCost_monoE (a := ModInv.NW n + 2) (b := ModInv.NW n' + 2) (by omega) (by omega)
  have c5 : SubMod2N.cost n ≤ SubMod2N.cost n' := by
    unfold SubMod2N.cost SubMod2N.wCost SubMod2N.W allocCost; omega
  have c7 := hm k k (min k xl) (min k xl') (Nat.le_refl _) (by omega)
  unfold ModInv.roundCost; omega

theorem sumR_le {s1 : Nat → Nat} {m1 : Nat → Nat → Nat} (hs : ∀ a a', a ≤ a' → s1 a ≤ s1 a')
    (hm : ∀ a a' c c', a ≤ a' → c ≤ c' → m1 a c ≤ m1 a' c') {xl xl' n n' : Nat} (hx : xl ≤ xl') (h : n ≤ n') :
    ∀ r, ModInv.sumR s1 m1 xl n r ≤ ModInv.sumR s1 m1 xl' n' r
  | 0 => Nat.le_refl _
  | r + 1 => by
    rw [ModInv.sumR_succ, ModInv.sumR_succ]
    have := sumR_le hs hm hx h r
    have := roundCost_mono hs hm hx h (r + 1) (2 ^ (r + 1))
    omega

/-- `ModInv.cost` is monotone in `len x` and `n` (TIGHT COSTS s45: per-round sizes, `xl`-dependent) -/
theorem miCost_mono {s1 : Nat → Nat} {m1 : Nat → Nat → Nat} (hs : ∀ a a', a ≤ a' → s1 a ≤ s1 a')
    (hm : ∀ a a' c c', a ≤ a' → c ≤ c' → m1 a c ≤ m1 a' c') {xl xl' n n' : Nat} (hx : xl ≤ xl') (h1 : 1 ≤ n)
    (h : n ≤ n') : ModInv.cost s1 m1 xl n ≤ ModInv.cost s1 m1 xl' n' := by
  have hW : ModInv.NW n ≤ ModInv.NW n' := by unfold ModInv.NW; omega
  have hW1 : 1 ≤ ModInv.NW n := by unfold ModInv.NW; omega
  have c1 := makeCost_monoE (a := ModInv.NW n + 1) (b := ModInv.NW n' + 1) (by omega) (by omega)
  have c2 := makeCost_monoE (a := 2 * ModInv.NW n) (b := 2 * ModInv.NW n') (by omega) (by omega)
  have c3 := makeCost_monoE (a := 2 * ModInv.NW n + 2) (b := 2 * ModInv.NW n' + 2) (by omega) (by omega)
  have c4 := makeCost_monoE (a := ModInv.NW n + 2) (b := ModInv.NW n' + 2) (by omega) (by omega)
  have c5 : SubMod2N.cost n ≤ SubMod2N.cost n' := by
    unfold SubMod2N.cost SubMod2N.wCost SubMod2N.W allocCost; omega
  have c6 := hs (ModInv.NW n + 1) (ModInv.NW n' + 1) (by omega)
  have c7 := hm (ModInv.NW n) (ModInv.NW n') (min (ModInv.NW n) xl) (min (ModInv.NW n') xl') hW (by omega)
  have hW0 : ModInv.NW n' ≠ 0 := by omega
  have hlg : Nat.log2 (ModInv.NW n) ≤ Nat.log2 (ModInv.NW n') :=
    (Nat.le_log2 hW0).2 (Nat.le_trans (Nat.log2_self_le (by omega)) hW)
  have c8 := sumR_le hs hm hx h (Nat.log2 (ModInv.NW n))
  have c9 := ModInv.sumR_mono s1 m1 xl' n' hlg
  unfold ModInv.cost; omega

/-- the bridged `ModInv.ens` charge (cost + one reserve) is monotone -/
theorem miB_mono {s1 : Nat → Nat} {m1 : Nat → Nat → Nat} (hs : ∀ a a', a ≤ a' → s1 a ≤ s1 a')
    (hm : ∀ a a' c c', a ≤ a' → c ≤ c' → m1 a c ≤ m1 a' c') {xl xl' n n' l l' : Nat} (hx : xl ≤ xl') (h1 : 1 ≤ n)
    (h : n ≤ n') (hl : l ≤ l') :
    ModInv.cost s1 m1 xl n + stkRes (l + ModInv.D n) ≤ ModInv.cost s1 m1 xl' n' + stkRes (l' + ModInv.D n') := by
  have := miCost_mono hs hm hx h1 h
  have hD : l + ModInv.D n ≤ l' + ModInv.D n' := by unfold ModInv.D ModInv.NW; omega
  have : stkRes (l + ModInv.D n) ≤ stkRes (l' + ModInv.D n') := by
    simp only [stkRes_eq]; omega
  omega

theorem mul_le_mulE {a c ml l0 l : Nat} (ha : a ≤ ml) (hc : c ≤ ml) (hml : ml ≤ 128) (hl : l ≤ wL4 l0 ml) :
    mulCQ a c + stkRes (l + 8 * ml + 64) ≤ mulE l0 ml := by
  have := mulCQ_le_box ha hc (by omega)
  simp only [mulE, mulB, stkRes_eq]; omega

/-! ### the arithmetic side conditions of the composition (small contexts) -/

theorem rk_le {x X r r' : Nat} (hx : x ≤ X) (h : r = X + r') : x + r' ≤ r := by omega

theorem rk_le2 {a A c C r r' : Nat} (h1 : a ≤ A) (h2 : c ≤ C) (h : r = A + C + r') : a ≤ r ∧ c + r' ≤ r := by
  omega

theorem rk_le3 {a B c C D r r6 r7 r8 x : Nat} (h1 : a ≤ B) (h2 : c ≤ C) (e5 : r = C + r6) (e6 : r6 = x + r7)
    (e7 : r7 = max B D + r8) : a ≤ r ∧ c + r6 ≤ r := by
  omega

theorem rk_le4 {a B c D r r' : Nat} (h1 : a ≤ B) (h2 : c ≤ D) (h : r = max B D + r') : a ≤ r ∧ c + r' ≤ r := by
  omega

theorem lg2_le (s : State) (mp ml : Nat) : lg2 s mp ml ≤ 64 * ml := by
  have hM : natVal s.mem mp ml < 2 ^ (64 * ml) := by
    have := Janus.Arm64.Memory.readLE_lt s.mem mp (8 * ml)
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * ml) = 64 * ml by omega] at this
    exact this
  have hq : natVal s.mem mp ml / 2 ^ nE s mp ml < 2 ^ (64 * ml) :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hM
  simp only [lg2]
  rcases Nat.eq_zero_or_pos (natVal s.mem mp ml / 2 ^ nE s mp ml) with e | e
  · rw [e]; simp
  · exact Nat.le_of_lt ((Nat.log2_lt (Nat.pos_iff_ne_zero.1 e)).2 hq)

section
variable {s : State} {st mp ml : Nat}

theorem l2_le (hn : nE s mp ml < 64 * ml) : lvl2 s st mp ml ≤ wL2 (stLen s.mem st) ml := by
  have h1 := rnd_mono (a := a1 (nE s mp ml)) (b := ml) (by simp only [a1]; omega)
  have h2 := rnd_mono (a := a2 ml (nE s mp ml)) (b := ml) (by simp only [a2]; omega)
  simp only [lvl2, wL2]; omega

theorem l3_le (hn : nE s mp ml < 64 * ml) {l1 l2 : Nat} (h1 : l1 ≤ ml) (h2 : l2 ≤ ml) :
    lvl3 s st mp ml l1 l2 ≤ wL3 (stLen s.mem st) ml := by
  have := l2_le (st := st) hn
  have h3 := rnd_mono (a := 2 * max l1 l2) (b := 2 * ml) (by omega)
  simp only [lvl3, wL3]; omega

theorem l4_le (hn : nE s mp ml < 64 * ml) {l1 l2 : Nat} (h1 : l1 ≤ ml) (h2 : l2 ≤ ml) :
    lvl4 s st mp ml l1 l2 ≤ wL4 (stLen s.mem st) ml := by
  have := l3_le (st := st) hn h1 h2
  have h3 := rnd_mono (a := 2 * max l1 l2) (b := 2 * ml) (by omega)
  simp only [lvl4, wL4]; omega

end

section
variable {needR : Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {l0 xl yl ml : Nat}

theorem need_lo (hneed : l0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) {l k : Nat} (hl : l ≤ wL4 l0 ml)
    (hk : k ≤ 8 * ml + 72) : l + k ≤ 2 ^ 16 := by
  unfold needE at hneed; simp only [wL4, wL3, wL2] at hl; omega

theorem need1 (hneed : l0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) {a : Nat} (ha : a ≤ ml) :
    l0 + a + 3 ≤ 2 ^ 16 := by unfold needE at hneed; omega

theorem need2 (hneed : l0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) {a c : Nat} (ha : a ≤ ml) (hc : c ≤ ml) :
    l0 + StackNat.rnd a + c + 3 ≤ 2 ^ 16 := by
  have := rnd_mono ha; unfold needE at hneed; omega

theorem need3 (hneed : l0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) {l : Nat} (hl : l ≤ wL4 l0 ml) :
    l + 2 * ml + 3 ≤ 2 ^ 16 := by unfold needE at hneed; simp only [wL4, wL3, wL2] at hl; omega

theorem nstkE_of (hRm : ∀ x a a', a ≤ a' → needR x a ≤ needR x a')
    (hSm : ∀ x y a a', a ≤ a' → needS x y a ≤ needS x y a')
    (hPm : ∀ x y a a', a ≤ a' → needP x y a ≤ needP x y a')
    (hneed : l0 + needE needR needS needP xl yl ml ≤ 2 ^ 16) {l lm k : Nat} (hl : l ≤ wL4 l0 ml) (hlm : lm ≤ ml)
    (hk : k ≤ 64 * ml) : NStkE needR needS needP xl yl lm l k := by
  have n1 := hRm xl lm ml hlm
  have n2 := hSm xl yl lm ml hlm
  have n3 := hPm xl yl k (64 * ml) hk
  unfold needE at hneed; simp only [wL4, wL3, wL2] at hl
  unfold NStkE; omega

end

end FvModexp.Amd64.ExpEven
