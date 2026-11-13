import FvModexp.Proofs.Arm64.NatQ.BasicSqrFin
import FvModexp.Proofs.Arm64.NatQ.BasicSqrLoop
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

/-!
# [Q-form copy of Arm64/Nat/BasicSqrClr.lean — TIGHT COSTS, divmc s34] `basicSqr` (arm64): `clear(t)` (`memclrNoHeapPointers`), `z[1], z[0] = mulWW(x[0], x[0])`, into the loop (natmul.go:121-124)
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.Q.BasicSqr

variable {H : Nat}

/-- the `CALL runtime.memclrNoHeapPointers` -/
abbrev callClr : Nat := segAddr Extracted.program fn + 0x98

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem clr (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibBasicSqr.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b H L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (Q : State) (hpc : Q.pc = BitVec.ofNat 64 callClr) (hsp : Q.sp = s.sp - 208#64) (h28 : Q.regs 28 = s.regs 28)
    (h29 : Q.regs 29 = s.sp - 216#64) (h18 : Q.regs 18 = s.regs 18) (r0 : Q.regs 0 = BitVec.ofNat 64 t)
    (r1 : Q.regs 1 = BitVec.ofNat 64 (16 * xl.toNat))
    (hM : Mem R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 (2 * xl.toNat)
      (stLen s.mem st.toNat + (2 * xl.toNat + 3) / 4 * 4) Q.mem) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) Q fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b H L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hz48 := hl.z48; have hbig := hE.big
  have hpre := hE.pre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hpre.ce
  have hsv := hpre.sv
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [t, 16 * xl.toNat] := hsv.2.2.1 _ _ (by
    have := hpre.stlen; omega)
  have hxacc := hpre.xacc; have hx48 := hpre.x48
  have hzlv := hpre.zlive
  obtain ⟨hzal, hzh, hzacc, -⟩ := hzlv (by omega)
  have hscr := hE.scr
  have hM' := hM
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf, minv⟩ := hM'
  have htacc : Q.mem.accessible t (16 * xl.toNat) true = true := by
    rw [mfr.accessible]; have := hscr.acc; rw [show 8 * (2 * xl.toNat) = 16 * xl.toNat by omega] at this; exact this
  have htH : Held R L1 t (16 * xl.toNat) := hl.theld
  have htg : Apart t (16 * xl.toNat) ((s.regs 28).toNat + 16) 8 := by
    rcases hscr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
    · have ha := (hpre.starr h0).2; have := hpre.stok.2.2.2.2.2.1; unfold Apart at ha ⊢; omega
    · have := (hin.apart hgr).symm; unfold Apart at this ⊢; omega
  have htH' : InRanges t (16 * xl.toNat) L1 ∨ Outside t (16 * xl.toNat) R.rt := htH
  have hgQ : Q.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    mfr.readLE _ _ (by have := hE.gOut; rw [show 8 * zl.toNat = 8 * zl.toNat from rfl] at this; exact this)
  have hL1 := hE.lsep1
  clear hpre hscr hzlv hsv
  have htw := hl.tw
  janus_run [m15, m12, m14, m11, hgQ] until [head] calls [hmc L1 b1]
  clear htw
  rename_i w _ _ hFc hLFc hinvw hz _
  have hxh := hE.ext.held hE.pre.xh
  have hzh1 := hE.ext.held hzh
  have hsth := hE.ext.held hE.pre.stok.2.1
  -- reads through memclr's frame
  have kw : ∀ a n, Held R L1 a n → (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat - 216 ≤ a) →
      (a + n ≤ s.sp.toNat - 200 ∨ s.sp.toNat - 184 ≤ a) → (a + n ≤ t ∨ t + 16 * xl.toNat ≤ a) →
      w.readLE a n = Q.mem.readLE a n := by
    intro a n hh h1 h2 h3
    refine Held.readLE2 hh hFc hLFc ?_ ?_
    · simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]; omega
  have kx : ∀ a n, xp.toNat ≤ a → a + n ≤ xp.toNat + 8 * xl.toNat → w.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have h3 := hl.xw; have h4 := hl.tx
    rw [kw a n (hxh.sub h1 h2) (by omega) (by omega) (by omega)]; exact mxs a n h1 h2
  have hx0v : w.readLE xp.toNat 8 = s.mem.readLE xp.toNat 8 := kx _ _ (Nat.le_refl _) (by omega)
  -- the new memory
  generalize hMn : (w.writeLE zp.toNat 8
      (BitVec.ofNat 64 (w.readLE xp.toNat 8) * BitVec.ofNat 64 (w.readLE xp.toNat 8)).toNat).writeLE
      (zp.toNat + 8) 8 (w.readLE xp.toNat 8 * w.readLE xp.toNat 8 / 18446744073709551616) = Mn
  have kn : ∀ a n, (a + n ≤ zp.toNat ∨ zp.toNat + 16 ≤ a) → Mn.readLE a n = w.readLE a n := by
    intro a n h; rw [← hMn, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have ks : ∀ a, (s.sp.toNat - 216 ≤ a ∧ a + 8 ≤ s.sp.toNat - 200) ∨ (s.sp.toNat - 184 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) →
      Mn.readLE a 8 = Q.mem.readLE a 8 := by
    intro a ha
    have h3 := hl.zw; have h4 := hl.tw
    rw [kn a 8 (by omega), kw a 8 (Or.inr (hout.of_sub (by omega) (by omega))) (by omega) (by omega) (by omega)]
  have kst : ∀ k, k + 8 ≤ 24 → Mn.readLE (st.toNat + k) 8 = Q.mem.readLE (st.toNat + k) 8 := by
    intro k hk
    have h3 := hl.sz; have h4 := hl.sw; have h5 := hl.ts
    rw [kn _ 8 (by omega), kw _ 8 (hsth.sub (by omega) (by omega)) (by omega) (by omega) (by omega)]
  have hMnF : MemFrame Q.mem Mn (R.rt ++ [(s.sp.toNat - 4304, s.sp.toNat - 216), (s.sp.toNat - 200, s.sp.toNat - 184)] ++
      [(t, t + 16 * xl.toNat)] ++ [(zp.toNat, zp.toNat + 16)]) := by
    have e1 : s.sp.toNat - 208 - 4096 = s.sp.toNat - 4304 := by omega
    have e2 : s.sp.toNat - 208 - 8 = s.sp.toNat - 216 := by omega
    have e3 : s.sp.toNat - 208 + 8 = s.sp.toNat - 200 := by omega
    have e4 : s.sp.toNat - 208 + 8 + 16 = s.sp.toNat - 184 := by omega
    rw [e1, e2, e4, e3] at hFc
    refine mfTrans hFc ⟨fun a n h => ?_, fun a n v => ?_⟩
    · simp only [outside_cons, outside_nil, and_true] at h; exact kn a n h
    · rw [← hMn]; simp only [Memory.accessible_writeLE]
  have hI1 : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 1 Mn := by
    refine ⟨⟨(ks _ (by omega)).trans m1, (ks _ (by omega)).trans m2, (ks _ (by omega)).trans m3,
      (ks _ (by omega)).trans m4, (ks _ (by omega)).trans m5, (ks _ (by omega)).trans m6, (ks _ (by omega)).trans m7,
      (ks _ (by omega)).trans m8, (ks _ (by omega)).trans m9, (ks _ (by omega)).trans m10,
      (ks _ (by omega)).trans m11, (ks _ (by omega)).trans m12, (ks _ (by omega)).trans m13,
      (ks _ (by omega)).trans m14, (ks _ (by omega)).trans m15, (ks _ (by omega)).trans m16,
      (kst 0 (by omega)).trans m17, (kst 8 (by omega)).trans m18, (kst 16 (by omega)).trans m19,
      ?xs, ?fr, ?lf, ?inv⟩, ?vz, ?vt, ?zr⟩
    case xs =>
      intro a n h1 h2
      have h3 := hl.zx
      rw [kn a n (by omega)]; exact kx a n h1 h2
    case fr =>
      refine (mfTrans mfr hMnF).mono fun a n ho => ?_
      simp only [winA, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨⟨⟨h1, h2, h3⟩, h4, h5⟩, h6, h7⟩ := ho
      have hz2 : a + n ≤ zp.toNat ∨ zp.toNat + 16 ≤ a := by clear h3 h5 h6 h7; omega
      have hw1 : a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat - 216 ≤ a := by clear h3 h4 h5 h6 h7; omega
      have hw2 : a + n ≤ s.sp.toNat - 200 ∨ s.sp.toNat - 184 ≤ a := by clear h3 h4 h5 h6 h7; omega
      exact ⟨⟨⟨⟨h1, h2, h3⟩, h4, h5⟩, h6, h7⟩, ⟨⟨h1, hw1, hw2⟩, h5⟩, hz2⟩
    case lf =>
      refine ⟨fun a n hin hws => ?_⟩
      simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at hws
      obtain ⟨⟨h4, h5⟩, h6, h7⟩ := hws
      have hin1 : InRanges a n L1 := hE.ext.inRanges_old hin
      have hw0 : a + n ≤ s.sp.toNat - 4432 ∨ s.sp.toNat + 64 ≤ a := by
        obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r hr; clear h4 h5 h6 h7; omega
      rw [kn a n (by clear h5 h6 h7 hw0; omega), kw a n (Or.inl hin1) (by clear h4 h5 h6 h7; omega)
        (by clear h4 h5 h6 h7; omega) h5]
      exact mlf.readLE a n hin
        (by simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨h4, h5⟩, h6, h7⟩)
    case inv =>
      rw [← hMn]
      exact inv_store_held (inv_store_held hinvw (hzh1.sub (by omega) (by omega))) (hzh1.sub (by omega) (by omega))
    case vz =>
      show Mn.readLE zp.toNat (8 * (2 * 1)) = SqrMath.sqS (SqrMath.lim s.mem xp.toNat) 1
      rw [← hMn, show 8 * (2 * 1) = 8 + 8 by rfl, Memory.readLE_add, Memory.readLE_writeLE_self,
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, hx0v]
      simp only [SqrMath.sqS, SqrMath.lim, Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add,
        BitVec.toNat_mul, BitVec.toNat_ofNat]
      have := Memory.readLE_lt s.mem xp.toNat 8
      generalize s.mem.readLE xp.toNat 8 = x0 at this ⊢
      simp only [Nat.reducePow] at this ⊢
      have h2 : x0 * x0 / 18446744073709551616 < 18446744073709551616 := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        exact Nat.mul_lt_mul_of_lt_of_lt this this
      rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt this, Nat.mod_mod]
      omega
    case vt =>
      show Mn.readLE t (8 * (2 * 1)) = SqrMath.sqT (SqrMath.lim s.mem xp.toNat) 1
      have := hl.tz
      rw [kn _ _ (by omega)]
      simp only [SqrMath.sqT, SqrMath.pre, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      exact readLE_of_zeroed hz _ _ (Nat.le_refl _) (by omega)
    case zr =>
      intro a n h1 h2
      have := hl.tz
      rw [kn _ _ (by omega)]
      exact readLE_of_zeroed hz _ _ (by omega) h2
  refine loop impl R hMV' b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE _
    (fin1 impl R hLsh b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hVV hE hl4 hl48) (xl.toNat - 1) _ 1 (by omega)
    (Nat.le_refl _) ?_ ?_ ?_ ?_ ?_ ?r0 ?r2 ?_ ?_ ?_ ?_ ?_ hI1
  case r0 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, m6]
  case r2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, m4]
  all_goals janus_simp

end FvModexp.Arm64.Q.BasicSqr
