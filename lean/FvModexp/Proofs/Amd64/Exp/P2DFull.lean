import FvModexp.Proofs.Amd64.Exp.P2DSumO
import FvModexp.Proofs.Amd64.Exp.P2DTz
import FvModexp.Proofs.Amd64.Exp.P2DRec
import FvModexp.Proofs.Amd64.Exp.P2DLsh

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): the full summary `sumF` (agent asm s71; twin of infra's arm64 `P2DFull`)

`sumF`: a `Summary` on `LibW` at `fnE` for any positive base, budget `costP` (with the window costs).
Odd base: `sumO`. Even base: `entP`, then `logM = 1` → `oneP`; `len y > 1` → `zeroP` (`Y ≥ 2^64 ≥ logM`);
`len y = 1`: the `tz` loop (`tzLoop`), `tzE`: overflow / `tz·y ≥ logM` → `zero2P`; else `rshCall` → `recCall` (the
odd-base summary one frame down, window `(stk - 0x78) / 72`) → `lshPath`, value
`X^Y mod 2^lm = ((X / 2^tz)^Y mod 2^(lm − tz·Y)) · 2^(tz·Y)` (`val_rec`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp FvModexp.Amd64.EvenHyp

/-- the extra entry facts of the full summary (`OX` without the parity) -/
@[reducible] def FX (s : State) (zp xp xl xc : Nat) : Prop :=
  (s.xmm 15 = 0 ∧ s.df = false ∧ zp < 2 ^ 64) ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧
    ((0 < xl → Apart xp (8 * xl) RunIface.gA 32) ∧ Apart (s.mem.readLE EvenHyp.natOneA 8) 8 RunIface.gA 32 ∧
      s.mem.accessible Callees.adxAddr 1 false = true) ∧
    s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47

theorem cO_le_cP (c2 c4 : Nat → Nat → Nat → Nat) (l xl yl lm lm1 : Nat) (h : lm1 ≤ lm) :
    costO c2 c4 l yl lm1 ≤ costP c2 c4 l xl yl lm :=
  Nat.le_trans (le_supTo (costO c2 c4 l yl) lm lm1 h) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

theorem postD_mono {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zc st v c c' : Nat} {s s' : State}
    (h : c ≤ c') (hq : PostD R b L stk A c zp zc st v s s') : PostD R b L stk A c' zp zc st v s s' := by
  obtain ⟨h1, hfs, hdf, p, l, cc, q0, q1, q2, L', b', hr, ⟨hx, hb, hinv⟩, rest⟩ := hq
  exact ⟨h1, hfs, hdf, p, l, cc, q0, q1, q2, L', b', hr, ⟨hx, by omega, hinv⟩, rest⟩

/-- the value identity of the recursive path -/
theorem val_rec {X Y lm : Nat} (hX : 0 < X) (hlo : Exp.tz X * Y < lm) :
    X ^ Y % 2 ^ lm = (X / 2 ^ Exp.tz X) ^ Y % 2 ^ (lm - Exp.tz X * Y) * 2 ^ (Exp.tz X * Y) := by
  have hs := (Exp.tz_spec hX).1
  have e1 : X ^ Y = 2 ^ (Exp.tz X * Y) * (X / 2 ^ Exp.tz X) ^ Y := by
    rw [show X ^ Y = (2 ^ Exp.tz X * (X / 2 ^ Exp.tz X)) ^ Y from congrArg (· ^ Y) hs, Nat.mul_pow, ← Nat.pow_mul]
  have e2 : 2 ^ lm = 2 ^ (Exp.tz X * Y) * 2 ^ (lm - Exp.tz X * Y) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e1, e2, Nat.mul_mod_mul_left, Nat.mul_comm]

/-- the zero value when `tz·Y ≥ logM` -/
theorem val_zero {X Y lm : Nat} (hX : 0 < X) (h : lm ≤ Exp.tz X * Y) : X ^ Y % 2 ^ lm = 0 := by
  have hs := (Exp.tz_spec hX).1
  have e1 : X ^ Y = 2 ^ (Exp.tz X * Y) * (X / 2 ^ Exp.tz X) ^ Y := by
    rw [show X ^ Y = (2 ^ Exp.tz X * (X / 2 ^ Exp.tz X)) ^ Y from congrArg (· ^ Y) hs, Nat.mul_pow, ← Nat.pow_mul]
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

/-- the three budget facts of the recursive path (kept out of the big context: `omega` there is slow) -/
theorem bud3 {m a o S d C : Nat} (h1 : m ≤ a) (h2 : o ≤ S) (hc : C = S + a + d) :
    m ≤ C ∧ m + o ≤ C ∧ m + o + d ≤ C := by
  subst hc; omega

theorem hle_z {tz Y lm : Nat} (h : tz * Y / 2 ^ 64 ≠ 0 ∨ lm ≤ tz * Y % 2 ^ 64) (hlm : lm ≤ 2 ^ 13) : lm ≤ tz * Y := by
  generalize tz * Y = P at h ⊢; omega

theorem need_le (xl tz : Nat) : makeCost (Rsh.need xl tz) ≤ makeCost (xl + 2) :=
  mk_mono (by simp only [Rsh.need]; omega) (by omega)

theorem nKF {stk A kW2 kW4 : Nat} (hk1 : 4320 + 0x78 ≤ stk) (hkW2 : kW2 + 0xf0 ≤ stk) (hkW4 : kW4 + 0xf0 ≤ stk)
    (hk2 : stk ≤ 2 ^ 20 + 0x78) (hA : 96 ≤ A) :
    4320 ≤ stk ∧ 72 ≤ A ∧ kW2 + 0x78 ≤ stk ∧ kW4 + 0x78 ≤ stk ∧ 4320 ≤ stk - 0x78 ∧ kW2 + 0x78 ≤ stk - 0x78 ∧
      kW4 + 0x78 ≤ stk - 0x78 ∧ stk - 0x78 ≤ 2 ^ 20 + 0x78 := by
  omega

theorem nE {SP stk A xp xl yp : Nat} (hbel : stk ≤ SP) (h48 : SP + A ≤ 2 ^ 48) (hk : 4320 ≤ stk) (hA : 96 ≤ A)
    (hxw : xp + 8 * xl ≤ SP - stk ∨ SP + A ≤ xp) (hyw : yp + 8 * 1 ≤ SP - stk ∨ SP + A ≤ yp)
    (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hy48 : yp + 8 * 1 ≤ 2 ^ 48) :
    (∀ j, j < xl → xp + 8 * j + 8 ≤ SP - 0x70 + 0x68 ∨ SP - 0x70 + 0xb8 ≤ xp + 8 * j) ∧
      (yp + 8 ≤ SP - 0x70 + 0x68 ∨ SP - 0x70 + 0xb8 ≤ yp) ∧ xp < 2 ^ 64 ∧ yp < 2 ^ 64 ∧ yp + 8 ≤ 2 ^ 48 ∧
      8 ≤ SP - 0x70 ∧ SP - 0x70 + 0xd0 ≤ 2 ^ 48 ∧ SP - stk ≤ SP - 0x70 - 8 ∧
      SP - 0x70 - 8 + 0xd8 ≤ SP - stk + (stk + A) := by
  refine ⟨fun j hj => by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem nZ {zl zc st lm : Nat} (hzl : zl ≤ zc) (hzc : zc < 2 ^ 40) (hst : st + 24 ≤ 2 ^ 48) (hlm : lm ≤ 2 ^ 13) :
    zl < 2 ^ 64 ∧ zc < 2 ^ 64 ∧ st < 2 ^ 64 ∧ lm < 2 ^ 64 := by
  omega

theorem tz64 {t xl : Nat} (h : t < 64 * xl) (hx : xl ≤ 2 ^ 9) : t < 2 ^ 64 := by omega

theorem m64 (xl : Nat) : 64 * xl = 8 * (8 * xl) := by omega

theorem lm_ab {a lm : Nat} (h : a < lm) : lm - a + a ≤ lm := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`expNNPowerOfTwo`, any positive base** (Summary on `LibW`) -/
theorem sumF {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    {kW2 kW4 : Nat} {c2 c4 : Nat → Nat → Nat → Nat} (hW2 : WSum impl R w2E kW2 c2) (hW4 : WSum impl R w4E kW4 c4)
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains NHyp.fnP2 = false)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (haR : aboveR ≤ 0x60)
    {stkL aboveL : Nat} (hlh : Lsh.Hyp2 impl R ns stkL aboveL) (haL : aboveL ≤ 0x60)
    (b : Nat) (L : List (Nat × Nat)) (stk A : Nat) (hk1 : 4320 + 0x78 ≤ stk) (hkW2 : kW2 + 0xf0 ≤ stk)
    (hkW4 : kW4 + 0xf0 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x78) (hkR : stkR + 0x78 ≤ stk) (hkL : stkL + 0x78 ≤ stk)
    (hA : 96 ≤ A) (zp zl zc st xp xl xc yp yl yc lm : Nat) :
    Summary (LibW.program.link impl) fnE
      (fun s => Regs s zp zl zc st xp xl xc yp yl yc lm ∧
        PreD R b L stk A (costP c2 c4 (stLen s.mem st) xl yl lm) zp zl zc st xp xl yp yl lm s ∧ FX s zp xp xl xc)
      (fun s s' => PostD R b L stk A (costP c2 c4 (stLen s.mem st) xl yl lm) zp zc st
        (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm) s s') := by
  have hSO := fun (b1 : Nat) (L1 : List (Nat × Nat)) (k A1 : Nat) (h1 : 4320 ≤ k) (h2 : kW2 + 0x78 ≤ k)
      (h3 : kW4 + 0x78 ≤ k) (h4 : k ≤ 2 ^ 20 + 0x78) (h5 : 72 ≤ A1) (p1 l1 c1 lm1 : Nat) =>
    sumO hmk hW2 hW4 b1 L1 k A1 h1 h2 h3 h4 h5 zp zl zc st p1 l1 c1 yp yl yc lm1
  intro s hpc ⟨hR, hP, ⟨hx15, hdf, hzp⟩, hxl, hxc, hEX, hra⟩
  have hP' := hP
  obtain ⟨hC, hX, hY, hlm1, hlm, -, -⟩ := hP'
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  have hcO := cO_le_cP c2 c4 (stLen s.mem st) xl yl lm
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := nKF hk1 hkW2 hkW4 hk2 hA
  -- odd base
  by_cases hXo : natVal s.mem xp xl % 2 = 1
  · obtain ⟨k, s', hst, hr, hq⟩ := hSO b L stk A n1 n3 n4 hk2 n2 xp xl xc lm s hpc
      ⟨hR, ⟨cpre_cst hP.1 (hcO lm (Nat.le_refl _)), hP.2⟩, ⟨hx15, hdf, hzp⟩, hXo, hxl, hxc, hEX, hra⟩
    exact ⟨k, s', hst, hr, postD_mono (hcO lm (Nat.le_refl _)) hq⟩
  -- even base
  have hXe : natVal s.mem xp xl % 2 = 0 := Nat.mod_two_ne_one.mp hXo
  have hC' := hC
  obtain ⟨⟨-, ⟨hbel, h48, hacc⟩, -, -, -, -, -, -, -⟩, -, -, -, -, -, ⟨hzc40, -, -⟩, hins, hsok, -⟩ := hC'
  simp only [regSP] at hbel h48 hacc
  obtain ⟨⟨-, hxa, hx48, -, hxw⟩, hxn, -⟩ := hins xp xl (by simp)
  obtain ⟨⟨-, hya, hy48, -, hyw⟩, hyn, hyN, -⟩ := hins yp yl (by simp)
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  have hzl : zl ≤ zc := hC.2.2.2.2.2.1
  have hst48 : st + 24 ≤ 2 ^ 48 := hsok.2.2.2.1
  have epi := epi_of hP n1 n2 hra
  refine entP _ s hP n1 n2 hpc hR
    (fun hl S hS hRE hm => oneP hmk hP n1 n2
      (Nat.le_trans (Nat.le_add_left _ _) (hcO lm (Nat.le_refl _))) hl hra S hS hRE hm)
    (fun _ h => absurd h (by
      have := val_mod2 s.mem xp xl 1 hxl0 Nat.one_pos; rw [Nat.pow_one, hXe] at this; rw [← this]; decide))
    (fun hl _ hy1 S hS hRE hm => ?_) (fun hl _ hy1 S hS hRE h12 hm => ?_)
  · -- `len y > 1`: `Y ≥ 2^64 ≥ logM`
    obtain ⟨esp, -, e0, -, e1, -, -, -, -, -, -, -, e14, efs, ex, edf⟩ := hRE
    have hYb : 2 ^ 64 ≤ natVal s.mem yp yl := by
      refine Nat.not_lt.1 fun hlt => ?_
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hy1 (lenLe (n := 1) hyN (by simpa using hlt)))
    exact zeroP hP n1 n2 hra (Exp.pow_even_mod_zero _ _ _ hXe (Nat.le_trans hlm (Nat.le_trans (by decide) hYb)))
      S hS esp e0 e1
      (e14.trans (bv_tn _)) efs ex edf hm
  · -- `len y = 1`: the `tz` loop
    subst hy1
    have hy := hR.2.2.2.2.2.2.2.2
    obtain ⟨esp, e5, e0, e3, e1, e7, e6, e8, e9, e10, e11, e2, e14, efs, ex, edf⟩ := hRE
    generalize hXd : natVal s.mem xp xl = X at hX hXe
    generalize hYd : natVal s.mem yp 1 = Y at hY
    have hX0 : 0 < X := hX
    obtain ⟨wx, wy, hxp64, hyp64, hy8, s1, s2, s3, s4⟩ := nE hbel h48 n1 hA hxw hyw hx48 hy48
    have hy0 : S.mem.readLE yp 8 = Y := by
      rw [hm, w0_rd wy, ← hYd]
    have hXl : X < Exp.B ^ xl := by
      have := Janus.Arm64.Memory.readLE_lt s.mem xp (8 * xl)
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
      rw [← hXd, Exp.B_def, ← Nat.pow_mul, m64 xl]; exact this
    have hXl' : X < 2 ^ (64 * xl) := by rw [Exp.B_def, ← Nat.pow_mul] at hXl; exact hXl
    have htz64 : Exp.tz X < 2 ^ 64 := tz64 (tz_lt64 hX0 hXl') hxn
    have hY64 : Y < 2 ^ 64 := by rw [← hYd]; exact Janus.Arm64.Memory.readLE_lt _ _ _
    have hY0 : 0 < Y := hY
    have txp := LibCalls.tN hxp64
    have typ := LibCalls.tN hyp64
    refine tzLoop (retAddrOf s) _ S (BitVec.ofNat 64 xp) (BitVec.ofNat 64 yp) xl X
      (fun j hj => by rw [txp, hm, w0_rd (wx j hj), ← hXd]; exact Expmc.readLE_wd _ _ _ _ hj)
      (by rw [txp, hm]; simp only [W0, Janus.Arm64.Memory.accessible_writeLE]; exact hxa) (by rw [txp]; exact hx48)
      (by
        rw [typ, hm]; simp only [W0, Janus.Arm64.Memory.accessible_writeLE]
        exact Janus.Arm64.Memory.accessible_mono _ hya (Nat.le_refl _) (Nat.le_refl _)) (by rw [typ]; exact hy8)
      hX0 hXl e6 e8 e11 ?_ (xl - 0) 0 S rfl (Nat.zero_le _) (fun j hj => absurd hj (Nat.not_lt_zero _)) hS
      ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩ (by rw [h12])
    intro S2 d1 ⟨dr, dm, dfs, dx, ddf⟩ d4 d5
    rw [typ, hy0] at d5
    have hacc2 : (W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp).accessible
        ((s.regs 4).toNat - 0x70 - 8) 0xd8 true = true := by
      simp only [W0, Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_mono _ hacc s3 s4
    have r14' : S2.regs 14 = s.regs 14 := (dr 14 (by decide) (by decide) (by decide)).trans (e14.trans (bv_tn _))
    have hone2A := hEX.2.1
    obtain ⟨z2, z3, z4, z5⟩ := nZ hzl hzc40 hst48 hlm
    refine tzE (retAddrOf s) _ ((s.regs 4).toNat - 0x70) zp zl zc st xp xl xc lm (Exp.tz X) Y _ s1
      s2 hacc2 ⟨hzp, z2, z3, z4, z5, htz64, hY64⟩ S2 d1
      ((dr 4 (by decide) (by decide) (by decide)).trans esp) ((dr 0 (by decide) (by decide) (by decide)).trans e0)
      ((dr 3 (by decide) (by decide) (by decide)).trans e3) ((dr 1 (by decide) (by decide) (by decide)).trans e1)
      ((dr 7 (by decide) (by decide) (by decide)).trans e7) ((dr 6 (by decide) (by decide) (by decide)).trans e6)
      ((dr 8 (by decide) (by decide) (by decide)).trans e8) ((dr 9 (by decide) (by decide) (by decide)).trans e9)
      ((dr 10 (by decide) (by decide) (by decide)).trans e10) d4 d5 (dm.trans hm) ?_ ?_
    · -- overflow / `tz·y ≥ logM`
      intro hz S3 g1 g2 g3 g4 g5 g6 g7 g8 g9
      have hv := val_zero hX0 (hle_z hz hlm)
      exact zero2P hP n1 n2 hra (by rw [hXd, hYd]; exact hv) S3 g1 g2 g3 g4 (g5.trans r14')
        (g6.trans (dfs.trans efs)) (g7.trans (dx.trans ex)) (g8.trans (ddf.trans edf)) g9
    · -- the recursive path
      intro hP64 hlt S4 k1 k2 k3 k4 k5 k7 k6 k8 k9 _ k14 kfs kx kdf km
      have hlo0 : 0 < Exp.tz X * Y := Nat.mul_pos (tz_pos hX0 hXe) hY0
      have hsup := le_supTo (costO c2 c4 (stLen s.mem st) 1) lm (lm - Exp.tz X * Y) (Nat.sub_le _ _)
      have hcst : costP c2 c4 (stLen s.mem st) xl 1 lm = supTo (costO c2 c4 (stLen s.mem st) 1) lm +
          makeCost (xl + 2) + makeCost (lm / 64 + 2) := rfl
      obtain ⟨hb1, hb2, hb3⟩ := bud3 (need_le xl (Exp.tz X)) hsup hcst
      have hodd := (Exp.tz_spec hX0).2
      have hv0 : 0 < (X / 2 ^ Exp.tz X) ^ Y % 2 ^ (lm - Exp.tz X * Y) := odd_pos hodd (Nat.sub_pos_of_lt hlt)
      have hvb : (X / 2 ^ Exp.tz X) ^ Y % 2 ^ (lm - Exp.tz X * Y) < 2 ^ (lm - Exp.tz X * Y) :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have hw := (val_rec hX0 hlt).symm
      have hv0' : 0 < (natVal s.mem xp xl / 2 ^ Exp.tz X) ^ natVal s.mem yp 1 % 2 ^ (lm - Exp.tz X * Y) := by
        rw [hXd, hYd]; exact hv0
      have hvb' : (natVal s.mem xp xl / 2 ^ Exp.tz X) ^ natVal s.mem yp 1 % 2 ^ (lm - Exp.tz X * Y) <
          2 ^ (lm - Exp.tz X * Y) := by
        rw [hXd, hYd]; exact hvb
      have hw' : (natVal s.mem xp xl / 2 ^ Exp.tz X) ^ natVal s.mem yp 1 % 2 ^ (lm - Exp.tz X * Y) *
          2 ^ (Exp.tz X * Y) = natVal s.mem xp xl ^ natVal s.mem yp 1 % 2 ^ lm := by
        rw [hXd, hYd]; exact hw
      have htz : Exp.tz X = Exp.tz (natVal s.mem xp xl) := by rw [hXd]
      have hsp4 : S4.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x78) := by
        rw [k2]; congr 1
      refine rshCall hap hns hnf hrh hkR haR hP n1 hA hxl hxc (tz := Exp.tz X) (lo := Exp.tz X * Y) htz64
        hb1 hx15 hdf S4 k1 hsp4 k3 k4 k5 k7 k6 k8 k9 (k14.trans r14') (kfs.trans (dfs.trans efs))
        (kx.trans (dx.trans ex)) (kdf.trans (ddf.trans edf)) km fun S5 j1 j2 j3 j4 j5 hq => ?_
      refine recCall (cf := fun l lm => costO c2 c4 l 1 lm) (lm' := lm - Exp.tz X * Y)
        (fun b1 L1 p1 l1 c1 => hSO b1 L1 (stk - 0x78) 72 n5 n6 n7 n8 (Nat.le_refl _)
          p1 l1 c1 (lm - Exp.tz X * Y))
        hP n1 hA hy hzp hx15 hdf hone2A hlt rfl htz hb2 hkR haR S4 hsp4 (k14.trans r14')
        (kfs.trans (dfs.trans efs)) (kx.trans (dx.trans ex)) (kdf.trans (ddf.trans edf)) km
        S5 j1 j2 j3 j4 j5 hq fun S3 a1 a2 a3 a4 a5 a6 a7 a8 hcp => ?_
      exact lshPath hap hns hnf hlh hkL haL hP n1 hA hx15 hdf epi.2.2.2.2 hlo0 (lm_ab hlt) hv0' hvb' hw' hb3
        S3 a1 a2 a3 a4 a5 a6 a7 a8 hcp

end FvModexp.Amd64.P2D
