import FvModexp.Proofs.Arm64.Exp.P2DSumO
import FvModexp.Proofs.Arm64.Exp.P2DZero
import FvModexp.Proofs.Arm64.Exp.P2DLsh

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): the full summary `sumF` (agent infra)

`sumF`: a `Summary` on `LibW` at `fnE` for any positive base, budget `cP` (= `costP` with the window costs).
Odd base: `sumO` (budget `cO … lm ≤ cP`). Even base: `entP`, then `logM = 1` → `oneP`; `len y > 1` → `zeroP`
(`Y ≥ 2^64 ≥ logM`); `len y = 1`: the `tz` loop (`tzLoopP`), `tzE`: overflow / `tz·y ≥ logM` → `zeroP`; else
`rshCall` → `recCall` (the odd-base summary one frame down, window `(stk - 112) / 96`) → `lshPath`, value
`X^Y mod 2^lm = ((X / 2^tz)^Y mod 2^(lm − tz·Y)) · 2^(tz·Y)` (`val_rec`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp FvModexp.Arm64.EvenHyp

/-- the budget on any positive base -/
@[reducible] def cP (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (ℓ xl yl lm : Nat) : Nat :=
  costP (P2W2.cost sqC mlC) (P2W4.cost sqC mlC) ℓ xl yl lm

theorem cO_le_cP (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (ℓ xl yl lm lm1 : Nat) (h : lm1 ≤ lm) :
    cO sqC mlC ℓ lm1 ≤ cP sqC mlC ℓ xl yl lm :=
  Nat.le_trans (le_supTo (costO (P2W2.cost sqC mlC) (P2W4.cost sqC mlC) ℓ) lm lm1 h)
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

theorem postD_mono {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zc st v c c' : Nat} {s s' : State}
    (h : c ≤ c') (hq : PostD R b L stk A c zp zc st v s s') : PostD R b L stk A c' zp zc st v s s' := by
  obtain ⟨h1, h2, h3, h4, p, l, cc, q0, q1, q2, L', b', hr, ⟨hx, hb, hinv⟩, rest⟩ := hq
  exact ⟨h1, h2, h3, h4, p, l, cc, q0, q1, q2, L', b', hr, ⟨hx, by omega, hinv⟩, rest⟩

/-- the value identity of the recursive path -/
theorem val_rec {X Y lm : Nat} (hX : 0 < X) (hlo : Exp.tz X * Y < lm) :
    X ^ Y % 2 ^ lm = (X / 2 ^ Exp.tz X) ^ Y % 2 ^ (lm - Exp.tz X * Y) * 2 ^ (Exp.tz X * Y) := by
  have hs := (Exp.tz_spec hX).1
  have e1 : X ^ Y = 2 ^ (Exp.tz X * Y) * (X / 2 ^ Exp.tz X) ^ Y := by
    conv_lhs => rw [hs]
    rw [Nat.mul_pow, ← Nat.pow_mul]
  have e2 : 2 ^ lm = 2 ^ (Exp.tz X * Y) * 2 ^ (lm - Exp.tz X * Y) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e1, e2, Nat.mul_mod_mul_left, Nat.mul_comm]

/-- the zero value when `tz·Y ≥ logM` -/
theorem val_zero {X Y lm : Nat} (hX : 0 < X) (h : lm ≤ Exp.tz X * Y) : X ^ Y % 2 ^ lm = 0 := by
  have hs := (Exp.tz_spec hX).1
  have e1 : X ^ Y = 2 ^ (Exp.tz X * Y) * (X / 2 ^ Exp.tz X) ^ Y := by
    conv_lhs => rw [hs]
    rw [Nat.mul_pow, ← Nat.pow_mul]
  rw [e1]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 h) _)

theorem odd_pos {o Y k : Nat} (ho : o % 2 = 1) (hk : 1 ≤ k) : 0 < o ^ Y % 2 ^ k := by
  have h1 : o ^ Y % 2 ^ k % 2 = o ^ Y % 2 :=
    Nat.mod_mod_of_dvd _ (by
      have := Nat.pow_dvd_pow 2 hk; rwa [Nat.pow_one] at this)
  have h2 : o ^ Y % 2 = 1 := by rw [Nat.pow_mod, ho, Nat.one_pow]
  omega

theorem tz_pos {X : Nat} (hX : 0 < X) (he : X % 2 = 0) : 0 < Exp.tz X := by
  rcases Nat.eq_zero_or_pos (Exp.tz X) with h | h
  · have := (Exp.tz_spec hX).2; rw [h, Nat.pow_zero, Nat.div_one] at this; omega
  · exact h

theorem tz_lt64 {X ml : Nat} (hX : 0 < X) (hXl : X < 2 ^ (64 * ml)) : Exp.tz X < 64 * ml := by
  obtain ⟨hts, -⟩ := Exp.tz_spec hX
  have h2 : 2 ^ Exp.tz X ≤ X := Nat.le_of_dvd hX ⟨_, hts⟩
  exact (Nat.pow_lt_pow_iff_right (by omega)).1 (Nat.lt_of_le_of_lt h2 hXl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`expNNPowerOfTwo`, any positive base** (Summary on `LibW`) -/
theorem sumF {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf2 : ns.contains P2W2.fn = false)
    (hnf4 : ns.contains P2W4.fn = false) (hnfP : ns.contains P2Pre.fn = false)
    (hnf : ns.contains NHyp.fnP2 = false)
    (hgr : GrowsliceLiveContract (LibW.program.link impl) P2W2.grE 4096 R)
    (hmc : MemclrNoHeapPointersLive (LibW.program.link impl) P2W2.mcE 4096 R)
    (hmv : MemmoveLive (LibW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (LibW.program.link impl) P2W2.mkE 4096 R)
    (hno : NewobjectLiveContract (LibW.program.link impl) P2W2.noE 4096 R)
    (hwb : WbLiveContract (LibW.program.link impl) P2W2.wbE 4096 R 2)
    {kcP : Nat} (hkc : 4608 ≤ kcP)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ kcP) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kcP) (haS : aboveS ≤ 88) (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kcP) (haM : aboveM ≤ 88) (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kcP) (haT : aboveT ≤ 88)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (haR : aboveR ≤ 88)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (haL : aboveL ≤ 88)
    (b : Nat) (L : List (Nat × Nat)) (stk A : Nat) (hk1 : 1184 + kcP ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 576)
    (hkR : stkR + 112 ≤ stk) (hkL : stkL + 112 ≤ stk) (hA : 96 ≤ A)
    (zp zl zc st xp xl xc yp yl yc lm : Nat)
    (hB : zp < 2 ^ 64 ∧ zl < 2 ^ 64 ∧ zc < 2 ^ 64 ∧ st < 2 ^ 64 ∧ yp < 2 ^ 64 ∧ yl < 2 ^ 64 ∧ yc < 2 ^ 64 ∧
      lm < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxc : xc < 2 ^ 64) :
    Summary (LibW.program.link impl) fnE
      (fun s => Regs s zp zl zc st xp xl xc yp yl yc lm ∧
        PreD R b L stk A (cP sqC mlC (stLen s.mem st) xl yl lm) zp zl zc st xp xl yp yl lm s ∧
        xl ≤ xc ∧ xc < 2 ^ 40 ∧ (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48)
      (fun s s' => PostD R b L stk A (cP sqC mlC (stLen s.mem st) xl yl lm) zp zc st
        (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s s') := by
  have hSO := fun (b1 : Nat) (L1 : List (Nat × Nat)) (k A1 : Nat) (h1 : 1072 + kcP ≤ k) (h2 : k ≤ 2 ^ 20 + 576)
      (h3 : 72 ≤ A1) (p1 l1 c1 lm1 : Nat) (hp1 : p1 < 2 ^ 64) (hc1 : c1 < 2 ^ 64) =>
    sumO hap hns hnf2 hnf4 hnfP hgr hmc hmv hmk hno hwb hkc hsn hkN haN hsq hkS haS hsm hmu hkM haM hmm htr hkT haT
      b1 L1 k A1 h1 h2 h3 zp zl zc st p1 l1 c1 yp yl yc lm1 hB.1 hp1 hc1
  intro s hpc ⟨hR, hP, hxc1, hxc2, hr4, hr48⟩
  have hP' := hP
  obtain ⟨hC, hX, hY, hlm1, hlm, -, -⟩ := hP'
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  have hcO := cO_le_cP sqC mlC (stLen s.mem st) xl yl lm
  -- odd base
  by_cases hXo : natVal s.mem xp xl % 2 = 1
  · obtain ⟨k, s', hst, hr, hq⟩ := hSO b L stk A (by omega) hk2 (by omega) xp xl xc lm hxp hxc s hpc
      ⟨hR, ⟨cpre_cst hP.1 (hcO lm (Nat.le_refl _)), hP.2⟩, hXo, hr4, hr48⟩
    exact ⟨k, s', hst, hr, postD_mono (hcO lm (Nat.le_refl _)) hq⟩
  -- even base
  have hXe : natVal s.mem xp xl % 2 = 0 := by omega
  have hx0 : s.mem.readLE xp 8 % 2 = 0 := by
    have := val_mod2 s.mem xp xl 1 hxl0 (by omega); rw [Nat.pow_one] at this; omega
  have hC' := hC
  obtain ⟨⟨-, ⟨hal, hle, h48, hacc⟩, -, -, -, -, -, -⟩, -, -, -, -, -, -, hins, -⟩ := hC'
  obtain ⟨⟨-, hxa, hx48, -, hxw⟩, hxn, -⟩ := hins xp xl (by simp)
  obtain ⟨⟨-, hya, hy48, -, hyw⟩, hyn, hyN, -⟩ := hins yp yl (by simp)
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := hB
  refine entP impl _ s hP (by omega) (by omega) hpc hR
    (fun hl S hS hRE hm => oneP hmk hP (by omega) (by omega)
      (Nat.le_trans (Nat.le_add_left _ _) (hcO lm (Nat.le_refl _))) hl hB.1 hxp hr4 hr48 S hS hRE hm)
    (fun _ h => absurd h (by omega)) (fun hl _ hy1 S hS hRE hm => ?_) (fun hl _ hy1 S hS hRE h11 hm => ?_)
  · -- `len y > 1`: `Y ≥ 2^64 ≥ logM`
    obtain ⟨esp, e0, -, e2, -, -, -, -, -, -, -, -, e18, e28, -⟩ := hRE
    have hYb : 2 ^ 64 ≤ natVal s.mem yp yl := by
      refine Nat.not_lt.1 fun hlt => ?_
      have := lenLe (n := 1) hyN (by simpa using hlt); omega
    exact zeroP hP (by omega) (by omega) (Exp.pow_even_mod_zero _ _ _ hXe (by omega)) hr4 hr48 (Or.inl rfl) S hS esp
      e0 e2 e18 e28 hm
  · -- `len y = 1`: the `tz` loop
    subst hy1
    obtain ⟨esp, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e18, e28, e29⟩ := hRE
    generalize hXd : natVal s.mem xp xl = X at hX hXe
    generalize hYd : natVal s.mem yp 1 = Y at hY
    have hX0 : 0 < X := hX
    have hW0 : ∀ a k, a + k ≤ s.sp.toNat - stk ∨ s.sp.toNat + A ≤ a →
        (W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp).readLE a k = s.mem.readLE a k :=
      fun a k h => w0_rd (by omega) (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hy0 : (W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp).readLE yp 8 = Y := by
      rw [hW0 _ _ (by omega), ← hYd]; simp [natVal]
    have hXl : X < Exp.B ^ xl := by
      have := Memory.readLE_lt s.mem xp (8 * xl)
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
      rw [← hXd, Exp.B_def, ← Nat.pow_mul, show 64 * xl = 8 * (8 * xl) by omega]; exact this
    have hXl' : X < 2 ^ (64 * xl) := by rw [Exp.B_def, ← Nat.pow_mul] at hXl; exact hXl
    have htz64 : Exp.tz X < 2 ^ 64 := by have := tz_lt64 hX0 hXl'; omega
    have hY64 : Y < 2 ^ 64 := by rw [← hYd]; exact Memory.readLE_lt _ _ _
    have hY0 : 0 < Y := hY
    have hmr : ∀ j, j < xl →
        (W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp).readLE (xp + 8 * j) 8 =
          Exp.wd X j := by
      intro j hj
      rw [hW0 _ _ (by omega), ← hXd]
      exact Expmc.readLE_wd _ _ _ _ hj
    refine tzLoopP (s.regs 30) _ xp xl X _ S.regs S.sp hmr
      (by simp only [W0, Memory.accessible_writeLE]; exact hxa) hx48 hX0 hXl (by omega)
      (by simp only [W0, Memory.accessible_writeLE]; exact Memory.accessible_mono _ hya (by omega) (by omega)) (by omega)
      e4 e5 e7 ?_ (xl - 0) 0 S rfl (Nat.zero_le _) (fun j hj => absurd hj (by omega)) hS rfl (fun _ _ _ _ => rfl) h11 hm
    intro S2 d1 d2 d3 d4 d5 d6
    rw [hy0] at d5
    have hacc2 : (W0 s.mem (s.sp.toNat - 112) (s.regs 29).toNat (s.regs 30).toNat zp xp yp).accessible
        (s.sp.toNat - 112 + 96) 112 true = true := by
      simp only [W0, Memory.accessible_writeLE]; exact Memory.accessible_mono _ hacc (by omega) (by omega)
    have r : ∀ i, i ≠ 11 → i ≠ 12 → i ≠ 13 → S2.regs i = S.regs i := d3
    refine tzE impl (s.regs 30) _ (s.sp.toNat - 112) zp zl zc st xp xl xc yp 1 yc lm (Exp.tz X) Y _ (by omega)
      (by omega) hacc2 ⟨z1, z2, z3, z4, z5, z6, z7, z8, htz64, hY64⟩ S2 d1 (d2.trans esp)
      ((r 0 (by omega) (by omega) (by omega)).trans e0) ((r 1 (by omega) (by omega) (by omega)).trans e1)
      ((r 2 (by omega) (by omega) (by omega)).trans e2) ((r 3 (by omega) (by omega) (by omega)).trans e3)
      ((r 4 (by omega) (by omega) (by omega)).trans e4) ((r 5 (by omega) (by omega) (by omega)).trans e5)
      ((r 6 (by omega) (by omega) (by omega)).trans e6) ((r 7 (by omega) (by omega) (by omega)).trans e7)
      ((r 8 (by omega) (by omega) (by omega)).trans e8) ((r 9 (by omega) (by omega) (by omega)).trans e9)
      ((r 10 (by omega) (by omega) (by omega)).trans e10) d4 d5 d6 ?_ ?_
    · -- overflow / `tz·y ≥ logM`
      intro hz S3 g1 g2 g3 g4 g5 g6 g7
      have hle' : lm ≤ Exp.tz X * Y := by
        generalize Exp.tz X * Y = P at hz; omega
      have hv := val_zero hX0 hle'
      exact zeroP hP (by omega) (by omega) (by rw [hXd, hYd]; exact hv) hr4 hr48 (Or.inr rfl) S3 g1
        (g2.trans (d2.trans esp)) (g3.trans ((r 0 (by omega) (by omega) (by omega)).trans e0))
        (g4.trans ((r 2 (by omega) (by omega) (by omega)).trans e2))
        (g5.trans ((r 18 (by omega) (by omega) (by omega)).trans e18))
        (g6.trans ((r 28 (by omega) (by omega) (by omega)).trans e28)) g7
    · -- the recursive path
      intro hP64 hlt S4 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14
      have hlo0 : 0 < Exp.tz X * Y := Nat.mul_pos (tz_pos hX0 hXe) hY0
      have hneed : makeCost (Rsh.need xl (Exp.tz X)) ≤ makeCost (xl + 2) :=
        mk_mono (by simp only [Rsh.need]; omega) (by omega)
      have hcO' := hcO (lm - Exp.tz X * Y) (by omega)
      have hcst : cP sqC mlC (stLen s.mem st) xl 1 lm = supTo (costO (P2W2.cost sqC mlC) (P2W4.cost sqC mlC)
          (stLen s.mem st)) lm + makeCost (xl + 2) + makeCost (lm / 64 + 2) := rfl
      have hb1 : makeCost (Rsh.need xl (Exp.tz X)) ≤ cP sqC mlC (stLen s.mem st) xl 1 lm := by omega
      have hb2 : makeCost (Rsh.need xl (Exp.tz X)) + cO sqC mlC (stLen s.mem st) (lm - Exp.tz X * Y) ≤
          cP sqC mlC (stLen s.mem st) xl 1 lm := by
        have := le_supTo (costO (P2W2.cost sqC mlC) (P2W4.cost sqC mlC) (stLen s.mem st)) lm
          (lm - Exp.tz X * Y) (by omega)
        omega
      have hb3 : makeCost (Rsh.need xl (Exp.tz X)) + cO sqC mlC (stLen s.mem st) (lm - Exp.tz X * Y) +
          makeCost (lm / 64 + 2) ≤ cP sqC mlC (stLen s.mem st) xl 1 lm := by
        have := le_supTo (costO (P2W2.cost sqC mlC) (P2W4.cost sqC mlC) (stLen s.mem st)) lm
          (lm - Exp.tz X * Y) (by omega)
        omega
      have hodd := (Exp.tz_spec hX0).2
      have hv0 : 0 < (X / 2 ^ Exp.tz X) ^ Y % 2 ^ (lm - Exp.tz X * Y) := odd_pos hodd (by omega)
      have hvb : (X / 2 ^ Exp.tz X) ^ Y % 2 ^ (lm - Exp.tz X * Y) < 2 ^ (lm - Exp.tz X * Y) :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have hw := (val_rec hX0 hlt).symm
      have e29' : S4.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 120) := by
        rw [k13, r 29 (by omega) (by omega) (by omega), e29, show s.sp.toNat - 112 - 8 = s.sp.toNat - 120 by omega]
      have r28' : S4.regs 28 = BitVec.ofNat 64 (s.regs 28).toNat :=
        k12.trans ((r 28 (by omega) (by omega) (by omega)).trans e28)
      have r18' : S4.regs 18 = s.regs 18 := k11.trans ((r 18 (by omega) (by omega) (by omega)).trans e18)
      have hsp4 : S4.sp = BitVec.ofNat 64 (s.sp.toNat - 112) := k2.trans (d2.trans esp)
      have hv0' : 0 < (natVal s.mem xp xl / 2 ^ Exp.tz X) ^ natVal s.mem yp 1 % 2 ^ (lm - Exp.tz X * Y) := by
        rw [hXd, hYd]; exact hv0
      have hvb' : (natVal s.mem xp xl / 2 ^ Exp.tz X) ^ natVal s.mem yp 1 % 2 ^ (lm - Exp.tz X * Y) <
          2 ^ (lm - Exp.tz X * Y) := by
        rw [hXd, hYd]; exact hvb
      have hw' : (natVal s.mem xp xl / 2 ^ Exp.tz X) ^ natVal s.mem yp 1 % 2 ^ (lm - Exp.tz X * Y) *
          2 ^ (Exp.tz X * Y) = natVal s.mem xp xl ^ natVal s.mem yp 1 % 2 ^ lm := by
        rw [hXd, hYd]; exact hw
      have htz : Exp.tz X = Exp.tz (natVal s.mem xp xl) := by rw [hXd]
      refine rshCall hap hns hnf hrh hkR haR hP (by omega) hA hxc1 hxc2 (tz := Exp.tz X) (lo := Exp.tz X * Y) htz64
        hb1 S4 k1 hsp4 k3 k4 k5 k6 k7 k8 k9 k10 r28' k14 fun S5 j1 j2 j3 j4 j5 j6 hq => ?_
      refine recCall (cf := cO sqC mlC) (lm' := lm - Exp.tz X * Y)
        (fun b1 L1 p1 l1 c1 hp1 hc1 => hSO b1 L1 (stk - 112) 96 (by omega) (by omega) (by omega) p1 l1 c1
          (lm - Exp.tz X * Y) hp1 hc1)
        hP (by omega) hA hlt rfl htz hb2 ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ hkR haR S4 hsp4 r28' r18' e29' k14
        S5 j1 j2 j3 j4 j5 j6 hq fun S3 a1 a2 a3 a4 a5 a6 a7 a8 a9 hcp => ?_
      exact lshPath hap hns hnf hlh hkL haL hP (by omega) hA hr4 hr48 hlo0 (by omega) hv0' hvb' hw' hb3 S3 a1 a2 a3
        a4 a6 a7 a8 a9 hcp

end FvModexp.Arm64.P2D
