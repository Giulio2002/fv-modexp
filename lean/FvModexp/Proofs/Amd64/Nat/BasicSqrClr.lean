import FvModexp.Proofs.Amd64.Nat.BasicSqrFin
import FvModexp.Proofs.Amd64.Nat.BasicSqrLoop
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

/-!
# `basicSqr` (amd64): `clear(t)` (`memclrNoHeapPointers`), `z[1], z[0] = mulWW(x[0], x[0])`, into the loop
(natmul.go:121-124; the amd64 twin of `Arm64/Nat/BasicSqrClr.lean`)

The `CALL runtime.memclrNoHeapPointers` at `+0xe0` (return `+0xe5`, entry `RSP - 200`), then `AX, CX, BX = t, cap, len`
reloaded, `x[0]²` stored into `z[0:2]` (`MULQ`), `AX = 1`, `JMP head`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.BasicSqr

/-- the `CALL runtime.memclrNoHeapPointers` -/
abbrev callClr : Nat := segAddr Extracted.program fn + 0xe0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the loop invariant at `i = 1` after `clear(t)` (memory `w`) and the stores of `x[0]²` into `z[0:2]` (pure) -/
theorem inv1 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl xc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1) {M w : Memory}
    (hM : Mem R L st zp zl zc xp xl xc s t L1 b1 w1 c1 (stLen s.mem st + (2 * xl + 3) / 4 * 4) M)
    (hFc : MemFrame (M.writeLE ((s.regs 4).toNat - 200) 8 6231429) w
      (R.rt ++ [((s.regs 4).toNat - 200 - 4096, (s.regs 4).toNat - 200),
        ((s.regs 4).toNat - 200 + 8, (s.regs 4).toNat - 200 + 8 + 16)] ++ [(t, t + 16 * xl)]))
    (hLFc : LiveFrame (M.writeLE ((s.regs 4).toNat - 200) 8 6231429) w L1 [(t, t + 16 * xl)])
    (hinvw : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 w)) (hz : Mem.Zeroed w t (16 * xl)) :
    Inv R L st zp zl zc xp xl xc s t L1 b1 w1 c1 1
      ((w.writeLE (zp + 8) 8 (w.readLE xp 8 * w.readLE xp 8 / 18446744073709551616)).writeLE zp 8
        (w.readLE xp 8 * w.readLE xp 8)) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hbig := hE.big
  have hpre := hE.pre
  obtain ⟨-, -, -, -, hout, -, -, -, -, ⟨htb, -, -⟩, htrt, -⟩ := hpre.ce
  have hzlv := hpre.zlive
  obtain ⟨-, hzh, -, -⟩ := hzlv (by omega)
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf,
    minv⟩ := hM
  have hxh := hE.ext.held hpre.xh
  have hzh1 := hE.ext.held hzh
  have hsth := hE.ext.held hpre.stok.2.1
  -- reads through the push and memclr's frame
  have kw : ∀ a n, Held R L1 a n → (a + n ≤ (s.regs 4).toNat - 4296 ∨ (s.regs 4).toNat - 176 ≤ a) →
      (a + n ≤ t ∨ t + 16 * xl ≤ a) → w.readLE a n = M.readLE a n := by
    intro a n hh h1 h3
    rw [Held.readLE2 hh hFc hLFc (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have kx : ∀ a n, xp ≤ a → a + n ≤ xp + 8 * xl → w.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have h3 := hl.xw; have h4 := hl.tx
    rw [kw a n (hxh.sub h1 h2) (by omega) (by omega)]; exact mxs a n h1 h2
  have hx0v : w.readLE xp 8 = s.mem.readLE xp 8 := kx _ _ (Nat.le_refl _) (by omega)
  generalize hMn : (w.writeLE (zp + 8) 8 (w.readLE xp 8 * w.readLE xp 8 / 18446744073709551616)).writeLE zp 8
      (w.readLE xp 8 * w.readLE xp 8) = Mn
  have kn : ∀ a n, (a + n ≤ zp ∨ zp + 16 ≤ a) → Mn.readLE a n = w.readLE a n := by
    intro a n h; rw [← hMn, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have ks : ∀ a, (s.regs 4).toNat - 176 ≤ a → a + 8 ≤ (s.regs 4).toNat + 64 → Mn.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    have h3 := hl.zw; have h4 := hl.tw
    rw [kn a 8 (by omega), kw a 8 (Or.inr (hout.of_sub (by omega) (by omega))) (by omega) (by omega)]
  have kst : ∀ k, k + 8 ≤ 24 → Mn.readLE (st + k) 8 = M.readLE (st + k) 8 := by
    intro k hk
    have h3 := hl.sz; have h4 := hl.sw; have h5 := hl.ts
    rw [kn _ 8 (by omega), kw _ 8 (hsth.sub (by omega) (by omega)) (by omega) (by omega)]
  have ktl : Mn.readLE (s.fsBase.toNat - 8) 8 = M.readLE (s.fsBase.toNat - 8) 8 := by
    have h1 := hl.fw; have h2 := hl.fz; have h3 := hl.ft; have h4 := hl.fs
    rw [kn _ 8 (by omega), kw _ 8 (Or.inr htrt) (by omega) (by omega)]
  have hQw : MemFrame M w (R.rt ++ [((s.regs 4).toNat - 4424, (s.regs 4).toNat + 64)] ++ [(t, t + 16 * xl)]) := by
    refine (mfTrans (rs := [((s.regs 4).toNat - 200, (s.regs 4).toNat - 192)]) (by janus_frame) hFc).mono
      fun a n ho => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := ho
    exact ⟨by omega, ⟨h1, by omega, by omega⟩, h3⟩
  have hwMn : MemFrame w Mn [(zp, zp + 16)] :=
    ⟨fun a n h => by simp only [outside_cons, outside_nil, and_true] at h; exact kn a n h,
     fun a n v => by rw [← hMn]; simp only [Janus.Arm64.Memory.accessible_writeLE]⟩
  refine ⟨⟨(ks _ (by omega) (by omega)).trans m1, (ks _ (by omega) (by omega)).trans m2,
      (ks _ (by omega) (by omega)).trans m3, (ks _ (by omega) (by omega)).trans m4,
      (ks _ (by omega) (by omega)).trans m5, (ks _ (by omega) (by omega)).trans m6,
      (ks _ (by omega) (by omega)).trans m7, (ks _ (by omega) (by omega)).trans m8,
      (ks _ (by omega) (by omega)).trans m9, (ks _ (by omega) (by omega)).trans m10,
      (ks _ (by omega) (by omega)).trans m11, (ks _ (by omega) (by omega)).trans m12,
      (ks _ (by omega) (by omega)).trans m13, (ks _ (by omega) (by omega)).trans m14,
      (ks _ (by omega) (by omega)).trans m15,
      (kst 0 (by omega)).trans m16, (kst 8 (by omega)).trans m17, (kst 16 (by omega)).trans m18,
      ktl.trans m19, ?xs, ?fr, ?lf, ?inv⟩, ?vz, ?vt, ?zr⟩
  case xs =>
    intro a n h1 h2
    have h3 := hl.zx
    rw [kn a n (by omega)]; exact kx a n h1 h2
  case fr =>
    refine (mfTrans mfr (mfTrans hQw hwMn)).mono fun a n ho => ?_
    simp only [win, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := ho
    exact ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩, ⟨⟨h1, h2⟩, h4⟩, by omega⟩
  case lf =>
    refine ⟨fun a n hin hws => ?_⟩
    simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at hws
    obtain ⟨⟨h4, h5⟩, h6, h7⟩ := hws
    have hin1 : InRanges a n L1 := hE.ext.inRanges_old hin
    have hw0 : a + n ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 64 ≤ a := by
      obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r hr; clear h4 h5 h6 h7; omega
    rw [kn a n (by clear h5 h6 h7 hw0; omega), kw a n (Or.inl hin1) (by clear h4 h5 h6 h7; omega) h5]
    exact mlf.readLE a n hin
      (by simp only [stkWs, outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨h4, h5⟩, h6, h7⟩)
  case inv =>
    rw [← hMn]
    exact inv_store_held (inv_store_held hinvw (hzh1.sub (by omega) (by omega))) (hzh1.sub (by omega) (by omega))
  case vz =>
    show Mn.readLE zp (8 * (2 * 1)) = SqrMath.sqS (SqrMath.lim s.mem xp) 1
    rw [← hMn, show 8 * (2 * 1) = 8 + 8 by rfl, Janus.Arm64.Memory.readLE_add, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self, hx0v]
    simp only [SqrMath.sqS, SqrMath.lim, Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
    have := Janus.Arm64.Memory.readLE_lt s.mem xp 8
    generalize s.mem.readLE xp 8 = x0 at this ⊢
    simp only [Nat.reducePow] at this ⊢
    have h2 : x0 * x0 / 18446744073709551616 < 18446744073709551616 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      exact Nat.mul_lt_mul_of_lt_of_lt this this
    rw [Nat.mod_eq_of_lt h2]
    omega
  case vt =>
    show Mn.readLE t (8 * (2 * 1)) = SqrMath.sqT (SqrMath.lim s.mem xp) 1
    have := hl.tz
    rw [kn _ _ (by omega)]
    simp only [SqrMath.sqT, SqrMath.pre, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    exact readLE_of_zeroed hz _ _ (Nat.le_refl _) (by omega)
  case zr =>
    intro a n h1 h2
    have := hl.tz
    rw [kn _ _ (by omega)]
    exact readLE_of_zeroed hz _ _ (by omega) h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem clr (impl : List Amd64.Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (LibBasicSqr.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1)
    (Q : State) (hpc : Q.rip = BitVec.ofNat 64 callClr) (hsp : Q.regs 4 = s.regs 4 - 192#64)
    (h5 : Q.regs 5 = s.regs 4 - 8#64) (h14 : Q.regs 14 = s.regs 14) (hfs : Q.fsBase = s.fsBase)
    (hx15 : Q.xmm 15 = 0#128) (hdf : Q.df = false)
    (r0 : Q.regs 0 = BitVec.ofNat 64 t) (r3 : Q.regs 3 = BitVec.ofNat 64 (16 * xl.toNat))
    (hM : Mem R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1
      (stLen s.mem st.toNat + (2 * xl.toNat + 3) / 4 * 4) Q.mem) :
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) Q fun s' =>
      RegsOK s s' ∧ Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hz48 := hl.z48; have hbig := hE.big
  have hpre := hE.pre
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, ⟨htb, htr, htg⟩, htrt, htw⟩ := hpre.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  have hsv := hpre.sv
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [t, 16 * xl.toNat] := hsv.2.2.1 _ _ (by
    have := hpre.stlen; omega)
  have hxacc := hpre.xacc; have hx48 := hpre.x48
  have hzlv := hpre.zlive
  obtain ⟨hzal, hzh, hzacc, -⟩ := hzlv (by omega)
  have hscr := hE.scr
  have hM' := hM
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf,
    minv⟩ := hM'
  have htacc : Q.mem.accessible t (16 * xl.toNat) true = true := by
    rw [mfr.accessible]; have := hscr.acc; rw [show 8 * (2 * xl.toNat) = 16 * xl.toNat by omega] at this; exact this
  have htH : Held R L1 t (16 * xl.toNat) := hl.theld
  have htH' : InRanges t (16 * xl.toNat) L1 ∨ Outside t (16 * xl.toNat) R.rt := htH
  have hgQ : Q.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    mfr.readLE _ _ hE.gOut
  have hL1 := hE.lsep1
  have htw' := hl.tw
  have hx00 : xl ≠ 0#64 := by intro h; rw [h] at hx0; simp at hx0
  have hzl1 : (1#64) < zl := by rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega
  clear hpre hscr hzlv hsv
  janus64_run [m5, m4, m3, m14, m13, m11, m10, hgQ, hfs, BitVec.msb_eq_decide] until [head] calls [hmc L1 b1]
  rename_i _ _ _ _ w _ _ hFc hLFc hinvw hz _
  refine loop impl R hMV' b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE _
    (fin1 impl R hLsh hVV b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE) (xl.toNat - 1) 1 (by omega)
    (Nat.le_refl _) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (inv1 hE hM hFc hLFc hinvw hz)
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | omega | skip

end FvModexp.Amd64.BasicSqr
