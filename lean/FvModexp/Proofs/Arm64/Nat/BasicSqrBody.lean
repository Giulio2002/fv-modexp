import FvModexp.Proofs.Arm64.Nat.BasicSqrStep
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

/-!
# `basicSqr` (arm64): the second half of a loop iteration — the `addMulVVWW.abi0` call, `t[2i] = c`, back to the head
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.BasicSqr

/-- the `CALL addMulVVWW.abi0` of the loop body -/
abbrev callMV : Nat := segAddr Extracted.program fn + 0x1b8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- the rest of an iteration, from the call (state `S1`, memory = the head's `M` with the two `z` words and the
frame stores): the call, `t[2i] = c`, back to the head. -/
theorem body2 (impl : List Segment) (R : RtInv)
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1) (Q : State → Prop)
    (i : Nat) (hi1 : 1 ≤ i) (hiy : i < xl.toNat) (M : Memory)
    (hI : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 i M)
    (hk : ∀ S : State, S.pc = BitVec.ofNat 64 head →
      S.sp = s.sp - 208#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 216#64 → S.regs 18 = s.regs 18 →
      S.regs 0 = BitVec.ofNat 64 t → S.regs 2 = BitVec.ofNat 64 (2 * xl.toNat) → S.regs 3 = xl → S.regs 4 = zl →
      S.regs 5 = xp → S.regs 6 = BitVec.ofNat 64 (i + 1) → S.regs 8 = zp →
      Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 (i + 1) S.mem →
      ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) S Q)
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 callMV) (hsp : S1.sp = s.sp - 208#64) (h28 : S1.regs 28 = s.regs 28)
    (h29 : S1.regs 29 = s.sp - 216#64) (h18 : S1.regs 18 = s.regs 18)
    (hF : MemFrame M S1.mem [(zp.toNat + 16 * i, zp.toNat + 16 * i + 16), (s.sp.toNat - 200, s.sp.toNat - 112),
      (s.sp.toNat - 72, s.sp.toNat - 56)])
    (hz0 : S1.mem.readLE (zp.toNat + 16 * i) 8 = (s.mem.readLE (xp.toNat + 8 * i) 8 * s.mem.readLE (xp.toNat + 8 * i) 8) % 2 ^ 64)
    (hz1 : S1.mem.readLE (zp.toNat + 16 * i + 8) 8 = s.mem.readLE (xp.toNat + 8 * i) 8 * s.mem.readLE (xp.toNat + 8 * i) 8 / 2 ^ 64)
    (f1 : S1.mem.readLE (s.sp.toNat - 200) 8 = t + 8 * i) (f2 : S1.mem.readLE (s.sp.toNat - 192) 8 = i)
    (f3 : S1.mem.readLE (s.sp.toNat - 176) 8 = t + 8 * i) (f4 : S1.mem.readLE (s.sp.toNat - 152) 8 = xp.toNat)
    (f5 : S1.mem.readLE (s.sp.toNat - 128) 8 = s.mem.readLE (xp.toNat + 8 * i) 8)
    (f6 : S1.mem.readLE (s.sp.toNat - 120) 8 = 0) (f7 : S1.mem.readLE (s.sp.toNat - 72) 8 = i)
    (hinv1 : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S1.mem)) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) S1 Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hpre := hE.pre
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
  have hxacc := hpre.xacc; have hx48 := hpre.x48
  have hscr := hE.scr
  have hI' := hI
  obtain ⟨hM, -, -, -⟩ := hI'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf, minv⟩ := hM
  have htacc : S1.mem.accessible (t + 8 * i) (8 * i) true = true := by
    rw [hF.accessible, mfr.accessible]; exact Memory.accessible_mono _ hscr.acc (by omega) (by omega)
  have htacc' := Memory.accessible_weaken _ htacc
  have hxacc' : S1.mem.accessible xp.toNat (8 * i) false = true := by
    rw [hF.accessible, mfr.accessible]; exact Memory.accessible_mono _ hxacc (by omega) (by omega)
  have hwacc : S1.mem.accessible (s.sp.toNat - 200) 96 true = true := by
    rw [hF.accessible, mfr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hty : t + 8 * i = xp.toNat ∨ Apart (t + 8 * i) (8 * i) xp.toNat (8 * i) := by
    right; unfold Apart; have := hl.tx; omega
  have htr : Apart (t + 8 * i) (8 * i) (s.sp.toNat - 208 + 96) 8 := by unfold Apart; have := hl.tw; omega
  have htH : Held R L1 (t + 8 * i) (8 * i) := hscr.held.sub (by omega) (by omega)
  have hro : Outside (s.sp.toNat - 208 + 96) 8 R.rt := hout.of_sub (by omega) (by omega)
  have htg : Apart (t + 8 * i) (8 * i) ((s.regs 28).toNat + 16) 8 := by
    rcases hscr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
    · have := (hpre.starr h0).2; unfold Apart at this ⊢; have := hpre.stok.2.2.2.2.2.1; omega
    · have := (hin.apart hgr).symm; unfold Apart at this ⊢; omega
  have hrg : Apart (s.sp.toNat - 208 + 96) 8 ((s.regs 28).toNat + 16) 8 := by unfold Apart at hga ⊢; omega
  have htaccs : s.mem.accessible (t + 8 * i) (8 * i) true = true := by rw [← mfr.accessible, ← hF.accessible]; exact htacc
  have htaccs' := Memory.accessible_weaken _ htaccs
  have hxaccs : s.mem.accessible xp.toNat (8 * i) false = true := by rw [← mfr.accessible, ← hF.accessible]; exact hxacc'
  have e8 : s.sp.toNat - 208 + 8 = s.sp.toNat - 200 := by omega
  have e16 : s.sp.toNat - 208 + 16 = s.sp.toNat - 192 := by omega
  have e32 : s.sp.toNat - 208 + 32 = s.sp.toNat - 176 := by omega
  have e56 : s.sp.toNat - 208 + 56 = s.sp.toNat - 152 := by omega
  have e80 : s.sp.toNat - 208 + 80 = s.sp.toNat - 128 := by omega
  have e88 : s.sp.toNat - 208 + 88 = s.sp.toNat - 120 := by omega
  rw [← e8] at f1; rw [← e16] at f2; rw [← e32] at f3; rw [← e56] at f4; rw [← e80] at f5; rw [← e88] at f6
  clear hpre hscr hl
  janus_run [m3, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, f1, f2, f3, f4, f5, f6, f7] until [callMV + 4]
    calls [hMV' b1 L1]
  rename_i w hval hFw hinvw hgd
  have e96 : s.sp.toNat - 208 + 96 = s.sp.toNat - 112 := by omega
  have e104 : s.sp.toNat - 208 + 104 = s.sp.toNat - 104 := by omega
  rw [e96] at hval; rw [e96, e104] at hFw
  have rdw : ∀ a, (s.sp.toNat - 104 ≤ a ∧ a + 8 ≤ s.sp.toNat - 72) ∨ (s.sp.toNat - 56 ≤ a ∧ a + 8 ≤ s.sp.toNat - 8) ∨
      (s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) → w.readLE a 8 = M.readLE a 8 := by
    intro a ha
    have := hE.lay.tw; have := hE.lay.zw
    rw [hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have w72 : w.readLE (s.sp.toNat - 72) 8 = i := by
    rw [hFw.readLE _ _ (by have := hE.lay.tw; simp only [outside_cons, outside_nil, and_true]; omega)]; exact f7
  have w88 := (rdw _ (by omega)).trans m3
  have w80 := (rdw _ (by omega)).trans m4
  have w48 := (rdw _ (by omega)).trans m6
  have w16 := (rdw _ (by omega)).trans m11
  have w24 := (rdw _ (by omega)).trans m12
  have w40 := (rdw _ (by omega)).trans m14
  have w48' := (rdw _ (by omega)).trans m15
  have hwacc2 : w.accessible (t + 16 * i) 8 true = true := by
    rw [hFw.accessible, hF.accessible, mfr.accessible]
    exact Memory.accessible_mono _ hE.scr.acc (by omega) (by omega)
  janus_run [w72, w88, w80, w48, w16, w24, w40, w48', mod64_of_lt (t + 16 * i) (by omega)] until [head]
  have htw := hE.lay.tw
  have wr : ∀ a, (s.sp.toNat - 104 ≤ a ∧ a + 8 ≤ s.sp.toNat - 72) ∨ (s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) →
      (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)).readLE a 8 = w.readLE a 8 :=
    fun a ha => Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have W80 := (wr _ (by omega)).trans w80
  have W48 := (wr _ (by omega)).trans w48'
  have W24 := (wr _ (by omega)).trans w24
  have W40 := (wr _ (by omega)).trans w40
  have W16 := (wr _ (by omega)).trans w16
  refine hk _ ?pc ?sp ?r28 ?r29 ?r18 ?r0 ?r2 ?r3 ?r4 ?r5 ?r6 ?r8
    (inv_step hE hi1 hiy hI hF hz0 hz1 hFw hval hinvw)
  case r0 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, W80]
  case r3 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, W48, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  case r4 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, W24, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  case r5 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, W40, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  case r8 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, W16, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  case r6 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact (BitVec.ofNat_add i 1).symm
  all_goals janus_simp

end FvModexp.Arm64.BasicSqr
