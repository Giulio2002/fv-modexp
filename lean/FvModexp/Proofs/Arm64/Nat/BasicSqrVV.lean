import FvModexp.Proofs.Arm64.Nat.BasicSqrEnd
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

/-!
# `basicSqr` (arm64): `addVV(z, z, t)` (natmul.go:133) and the defer bit, up to the closure call `CALL (R0)`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.BasicSqr

abbrev callVV : Nat := segAddr Extracted.program fn + 0x25c

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
theorem fin3 (impl : List Segment) (R : RtInv)
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1)
    (M : Memory) (hI : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 xl.toNat M)
    (D : State) (hpc : D.pc = BitVec.ofNat 64 callVV) (hsp : D.sp = s.sp - 208#64) (h28 : D.regs 28 = s.regs 28)
    (h29 : D.regs 29 = s.sp - 216#64) (h18 : D.regs 18 = s.regs 18)
    (hF : MemFrame M D.mem [(t, t + 16 * xl.toNat), (s.sp.toNat - 200, s.sp.toNat - 128),
      (s.sp.toNat - 56, s.sp.toNat - 48)])
    (d1 : D.mem.readLE (s.sp.toNat - 208 + 8) 8 = zp.toNat)
    (d2 : D.mem.readLE (s.sp.toNat - 208 + 16) 8 = zl.toNat)
    (d4 : D.mem.readLE (s.sp.toNat - 208 + 32) 8 = zp.toNat)
    (d7 : D.mem.readLE (s.sp.toNat - 208 + 56) 8 = t)
    (hvt : natVal D.mem t (2 * xl.toNat) = 2 * SqrMath.sqT (SqrMath.lim s.mem xp.toNat) xl.toNat)
    (hinvD : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 D.mem))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) D fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hz48 := hl.z48
  have hpre := hE.pre
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
  have hzlv := hpre.zlive; have hzg := hpre.zg
  obtain ⟨hzal, hzh, hzacc, -⟩ := hzlv (by omega)
  have hzh1 := hE.ext.held hzh
  have hscr := hE.scr
  have hI' := hI
  obtain ⟨hM, hvz, -, -⟩ := hI'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf, minv⟩ := hM
  have htw := hl.tw; have hzw := hl.zw; have htz := hl.tz
  have hvz' : natVal D.mem zp.toNat zl.toNat = SqrMath.sqS (SqrMath.lim s.mem xp.toNat) xl.toNat := by
    rw [show natVal D.mem zp.toNat zl.toNat = D.mem.readLE zp.toNat (8 * zl.toNat) from rfl,
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), ← hvz, hzl]
  rw [← hzl] at hvt
  have hDacc : ∀ a n w, D.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hF.accessible, mfr.accessible]
  have hzaccD : D.mem.accessible zp.toNat (8 * zl.toNat) true = true := by rw [hDacc]; exact hzacc
  have hzaccD' := Memory.accessible_weaken _ hzaccD
  have htaccD : D.mem.accessible t (8 * zl.toNat) false = true := by
    rw [hDacc]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ hscr.acc (by omega) (by omega))
  have hwaccD : D.mem.accessible (s.sp.toNat - 208 + 8) 80 true = true := by
    rw [hDacc]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hzt : Apart zp.toNat (8 * zl.toNat) t (8 * zl.toNat) := by unfold Apart; omega
  have hzt' : zp.toNat = t ∨ Apart zp.toNat (8 * zl.toNat) t (8 * zl.toNat) := Or.inr hzt
  have hzr : Apart zp.toNat (8 * zl.toNat) (s.sp.toNat - 208 + 80) 8 := by unfold Apart; omega
  have hro : Outside (s.sp.toNat - 208 + 80) 8 R.rt := hout.of_sub (by omega) (by omega)
  have hzgA : Apart zp.toNat (8 * zl.toNat) ((s.regs 28).toNat + 16) 8 := hzg
  have hrg : Apart (s.sp.toNat - 208 + 80) 8 ((s.regs 28).toNat + 16) 8 := by unfold Apart at hga ⊢; omega
  clear hpre hscr hzlv
  janus_run [d1, d2, d4, d7] until [callVV + 4] calls [hVV b1 L1]
  rename_i w hv _ hFw hinvw _
  have rdw : ∀ a, s.sp.toNat - 48 ≤ a → a + 8 ≤ s.sp.toNat - 8 → w.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    rw [hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have w16 := (rdw _ (by omega) (by omega)).trans m10
  have w40 := (rdw _ (by omega) (by omega)).trans m7
  have eD : segAddr LibBasicSqr.program (fn ++ ".deferwrap1") = 1817392 := by decide
  rw [eD] at w40
  have hval : natVal w zp.toNat zl.toNat = natVal s.mem xp.toNat xl.toNat * natVal s.mem xp.toNat xl.toNat := by
    rw [hv, hvt, ← sq_val, hzl]
    congr 2
  have hwacc : w.accessible (s.sp.toNat - 89) 1 true = true := by
    rw [hFw.accessible, hDacc]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  janus_run [w16, w40] until [callD]
  refine fin4 impl R b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE M hI _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?qF ?qZ ?qI hl4 hl48
  case qF => simp only [wsE]; janus_frame
  case qZ =>
    show Memory.readLE _ _ _ = _
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hval
  case qI =>
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 89, s.sp.toNat - 88)]) (by janus_frame) (fun r hr => ?_) hinvw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; left; exact hout.of_sub (by omega) (by omega)
  all_goals janus_simp

end FvModexp.Arm64.BasicSqr
