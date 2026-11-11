import FvModexp.Proofs.Amd64.Nat.BasicSqrEnd
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

/-!
# `basicSqr` (amd64): `addVV(z, z, t)` (natmul.go:133) and the defer bit, up to the closure call `CALL AX`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.BasicSqr

abbrev callVV : Nat := segAddr Extracted.program fn + 0x3a3

/-- `(Σ x_j² B^(2j) + 2 Σ x_j x[0:j] B^j) mod B^(2n) = x²` -/
theorem sq_val (m : Memory) (xp n : Nat) :
    (SqrMath.sqS (SqrMath.lim m xp) n + 2 * SqrMath.sqT (SqrMath.lim m xp) n) % 2 ^ (64 * (2 * n)) =
      natVal m xp n * natVal m xp n := by
  rw [SqrMath.sq_id, ← SqrMath.natVal_eq_pre]
  apply Nat.mod_eq_of_lt
  have h := natVal_lt m xp n
  calc natVal m xp n * natVal m xp n < 2 ^ (64 * n) * 2 ^ (64 * n) := Nat.mul_lt_mul_of_lt_of_lt h h
    _ = 2 ^ (64 * (2 * n)) := by rw [← Nat.pow_add]; congr 1; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- from the `CALL addVV.abi0` (state `D`; memory = the loop's final `M` with `t` doubled and the frame stores) to the
closure call -/
theorem fin3 (impl : List Amd64.Segment) (R : RtInv)
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1)
    (M : Memory) (hI : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 xl.toNat M)
    (D : State) (hpc : D.rip = BitVec.ofNat 64 callVV) (hsp : D.regs 4 = s.regs 4 - 192#64)
    (h5 : D.regs 5 = s.regs 4 - 8#64) (h14 : D.regs 14 = s.regs 14) (hfs : D.fsBase = s.fsBase)
    (hdf : D.df = false)
    (hF : MemFrame M D.mem [(t, t + 16 * xl.toNat), ((s.regs 4).toNat - 200, (s.regs 4).toNat - 120),
      ((s.regs 4).toNat - 56, (s.regs 4).toNat - 48)])
    (d1 : D.mem.readLE ((s.regs 4).toNat - 200 + 8) 8 = zp.toNat)
    (d2 : D.mem.readLE ((s.regs 4).toNat - 200 + 16) 8 = zl.toNat)
    (d4 : D.mem.readLE ((s.regs 4).toNat - 200 + 32) 8 = zp.toNat)
    (d7 : D.mem.readLE ((s.regs 4).toNat - 200 + 56) 8 = t)
    (hvt : natVal D.mem t (2 * xl.toNat) = 2 * SqrMath.sqT (SqrMath.lim s.mem xp.toNat) xl.toNat)
    (hinvD : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 D.mem)) :
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) D fun s' =>
      RegsOK s s' ∧ Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hz48 := hl.z48
  have hpre := hE.pre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, ⟨htb, htr, htg⟩, htrt, htw⟩ := hpre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  have hzlv := hpre.zlive; have hzg := hpre.zg; have hzt := hpre.zt
  obtain ⟨hzal, hzh, hzacc, -⟩ := hzlv (by omega)
  have hzh1 := hE.ext.held hzh
  have hscr := hE.scr
  have hI' := hI
  obtain ⟨hM, hvz, -, -⟩ := hI'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf,
    minv⟩ := hM
  have htw' := hl.tw; have hzw := hl.zw; have htz := hl.tz; have hra := hE.ra
  have hft := hl.ft; have hfz := hl.fz; have hfw := hl.fw
  have hvz' : natVal D.mem zp.toNat zl.toNat = SqrMath.sqS (SqrMath.lim s.mem xp.toNat) xl.toNat := by
    rw [show natVal D.mem zp.toNat zl.toNat = D.mem.readLE zp.toNat (8 * zl.toNat) from rfl,
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), ← hvz, hzl]
  rw [← hzl] at hvt
  have hDacc : ∀ a n w, D.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hF.accessible, mfr.accessible]
  have hzaccD : D.mem.accessible zp.toNat (8 * zl.toNat) true = true := by rw [hDacc]; exact hzacc
  have hzaccD' := Janus.Arm64.Memory.accessible_weaken _ hzaccD
  have htaccD : D.mem.accessible t (8 * zl.toNat) false = true := by
    rw [hDacc]; exact Janus.Arm64.Memory.accessible_weaken _
      (Janus.Arm64.Memory.accessible_mono _ hscr.acc (by omega) (by omega))
  have hwaccD : D.mem.accessible ((s.regs 4).toNat - 200) 200 true = true := by
    rw [hDacc]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hzt' : Apart zp.toNat (8 * zl.toNat) t (8 * zl.toNat) := by unfold Apart; omega
  have hzt2 : zp.toNat = t ∨ Apart zp.toNat (8 * zl.toNat) t (8 * zl.toNat) := Or.inr hzt'
  have hzr : Apart zp.toNat (8 * zl.toNat) ((s.regs 4).toNat - 200) 88 := by unfold Apart; omega
  have hro : Outside ((s.regs 4).toNat - 200 + 80) 8 R.rt := hout.of_sub (by omega) (by omega)
  have hrg : Apart ((s.regs 4).toNat - 200 + 80) 8 ((s.regs 14).toNat + 16) 8 := by unfold Apart at hga ⊢; omega
  have hrt : Apart ((s.regs 4).toNat - 200 + 80) 8 (s.fsBase.toNat - 8) 8 := by unfold Apart at htw ⊢; omega
  have hDtl : D.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact m19
  have hDtacc : D.mem.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hDacc]; exact htr
  have hfs8 : (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 := by omega
  clear hpre hscr hzlv
  janus64_run [d1, d2, d4, d7, hfs] until [callVV + 5] calls [hVV b1 L1]
  rename_i w _ _ hv _ hFw hinvw hgd htl
  have e80 : (s.regs 4).toNat - 200 + 80 = (s.regs 4).toNat - 120 := by omega
  have e88 : (s.regs 4).toNat - 200 + 88 = (s.regs 4).toNat - 112 := by omega
  simp only [e80, e88] at hFw
  have hFw' : MemFrame D.mem w [(zp.toNat, zp.toNat + 8 * zl.toNat), ((s.regs 4).toNat - 200, (s.regs 4).toNat - 192),
      ((s.regs 4).toNat - 120, (s.regs 4).toNat - 112)] :=
    MemFrame.trans (MemFrame.of_writeLE (rs := [((s.regs 4).toNat - 200, (s.regs 4).toNat - 192)]) D.mem 6232136
      (List.mem_singleton.2 rfl) (Nat.le_refl _) (by omega)) hFw fun a n h => by
        simp only [outside_cons, outside_nil, and_true] at h ⊢; exact ⟨h.2.1, h.1, h.2.2⟩
  have rdw : ∀ a, (s.regs 4).toNat - 48 ≤ a → a + 8 ≤ (s.regs 4).toNat - 8 → w.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    rw [hFw'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have w16 := (rdw _ (by omega) (by omega)).trans m9
  have w40 := (rdw _ (by omega) (by omega)).trans m6
  have eD : segAddr LibBasicSqr.program (fn ++ ".deferwrap1") = 6232320 := by decide
  rw [eD] at w40
  have wtl : w.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [hFw'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hDtl
  have wtacc : w.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hFw'.accessible]; exact hDtacc
  have hval : natVal w zp.toNat zl.toNat = natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat := by
    rw [hv, show M.readLE zp.toNat (8 * zl.toNat) = natVal M zp.toNat (2 * xl.toNat) by rw [hzl],
      show D.mem.readLE t (8 * zl.toNat) = natVal D.mem t zl.toNat from rfl, hvz, hvt, hzl, sq_val]
  have hwacc : w.accessible ((s.regs 4).toNat - 89) 1 true = true := by
    rw [hFw'.accessible, hDacc]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  janus64_run [w16, w40, wtl, hfs8, hfs] until [callD]
  refine fin4 impl R b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE M hI _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?qF ?qZ ?qI
  case qF => simp only [wsE]; janus_frame
  case qZ =>
    show Janus.Arm64.Memory.readLE _ _ _ = _
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hval
  case qI =>
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 89, (s.regs 4).toNat - 88)]) (by janus_frame) (fun r hr => ?_) hinvw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; left; exact hout.of_sub (by omega) (by omega)
  all_goals try janus64_simp
  all_goals first | exact hfs | exact hdf | skip

end FvModexp.Amd64.BasicSqr
