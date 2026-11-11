import FvModexp.Proofs.Arm64.Nat.BasicSqrBody
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

/-!
# `basicSqr` (arm64): the loop `for i := 1; i < n; i++` (natmul.go:124-130)

One iteration from the head `+0x140`: `z[2i+1], z[2i] = mulWW(x[i], x[i])`, the slice expressions `t[i:2i]`, `x[0:i]`,
`addMulVVWW.abi0` (frame at `SP' + 8 …`, carry at `SP' + 96`), `t[2i] = c`. The loop exits to the continuation `hfin`
at `i = n`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.BasicSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
theorem loop (impl : List Segment) (R : RtInv)
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1) (Q : State → Prop)
    (hfin : ∀ S : State, S.pc = BitVec.ofNat 64 head → S.sp = s.sp - 208#64 → S.regs 28 = s.regs 28 →
      S.regs 29 = s.sp - 216#64 → S.regs 18 = s.regs 18 → S.regs 0 = BitVec.ofNat 64 t →
      S.regs 2 = BitVec.ofNat 64 (2 * xl.toNat) → S.regs 3 = xl → S.regs 6 = xl →
      Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 xl.toNat S.mem →
      ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) S Q) :
    ∀ k (S : State) (i : Nat), i + k = xl.toNat → 1 ≤ i → S.pc = BitVec.ofNat 64 head →
      S.sp = s.sp - 208#64 → S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 216#64 → S.regs 18 = s.regs 18 →
      S.regs 0 = BitVec.ofNat 64 t → S.regs 2 = BitVec.ofNat 64 (2 * xl.toNat) → S.regs 3 = xl → S.regs 4 = zl →
      S.regs 5 = xp → S.regs 6 = BitVec.ofNat 64 i → S.regs 8 = zp →
      Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 i S.mem →
      ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) S Q := by
  intro k
  induction k with
  | zero =>
    intro S i hi h1 hpc hsp h28 h29 h18 r0 r2 r3 r4 r5 r6 r8 hI
    obtain rfl : i = xl.toNat := by omega
    exact hfin S hpc hsp h28 h29 h18 r0 r2 r3 (by rw [r6]; simp) hI
  | succ k ih =>
    intro S i hi h1 hpc hsp h28 h29 h18 r0 r2 r3 r4 r5 r6 r8 hI
    have hI' := hI
    obtain ⟨hM, hz, ht, h0⟩ := hI'
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf, minv⟩ := hM
    have hiy : i < xl.toNat := by omega
    have hl := hE.lay
    have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have hz48 := hl.z48
    have ht48 := hl.t48
    have hzwA : Apart zp.toNat (16 * xl.toNat) (s.sp.toNat - 4432) 4496 := by unfold Apart; have := hl.zw; omega
    have hxwA : Apart xp.toNat (8 * xl.toNat) (s.sp.toNat - 4432) 4496 := by unfold Apart; have := hl.xw; omega
    have htwA : Apart t (16 * xl.toNat) (s.sp.toNat - 4432) 4496 := by unfold Apart; have := hl.tw; omega
    have htxA : Apart t (16 * xl.toNat) xp.toNat (8 * xl.toNat) := by unfold Apart; have := hl.tx; omega
    have htzA : Apart t (16 * xl.toNat) zp.toNat (16 * xl.toNat) := by unfold Apart; have := hl.tz; omega
    have hzxA : Apart zp.toNat (16 * xl.toNat) xp.toNat (8 * xl.toNat) := by unfold Apart; have := hl.zx; omega
    have hpre := hE.pre
    have hce := hpre.ce
    obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
    have hzlv := hpre.zlive; have hzg := hpre.zg; have hxacc := hpre.xacc; have hx48 := hpre.x48
    obtain ⟨hzal, hzh, hzacc, -⟩ := hzlv (by omega)
    have hscr := hE.scr
    rw [← mfr.accessible] at hxacc hzacc
    have htacc : S.mem.accessible t (8 * (2 * xl.toNat)) true = true := by rw [mfr.accessible]; exact hscr.acc
    have hmask : ((BitVec.ofNat 64 i - BitVec.ofNat 64 (2 * xl.toNat)).sshiftRight 63).toNat =
        18446744073709551615 := sshr63_of_lt _ _ (by simp; omega) (by simp; omega)
    have hta1 : s.mem.accessible (t + 8 * i) (8 * i) true = true :=
      Memory.accessible_mono _ hscr.acc (by omega) (by omega)
    have hta2 := Memory.accessible_weaken _ hta1
    have htx1 : t + 8 * i = xp.toNat ∨ Apart (t + 8 * i) (8 * i) xp.toNat (8 * i) := by
      right; unfold Apart at htxA ⊢; omega
    have hzh1 := hE.ext.held hzh
    rw [hzl] at hzh1
    have htH : InRanges (t + 8 * i) (8 * i) L1 ∨ Outside (t + 8 * i) (8 * i) R.rt := hscr.held.sub (by omega) (by omega)
    have htg : Apart t (8 * (2 * xl.toNat)) ((s.regs 28).toNat + 16) 8 := by
      rcases hscr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
      · have := (hpre.starr h0).2; unfold Apart at this ⊢; have := hpre.stok.2.2.2.2.2.1; omega
      · exact (hin.apart hgr).symm
    have htgA : Apart (t + 8 * i) (8 * i) ((s.regs 28).toNat + 16) 8 := by unfold Apart at htg ⊢; omega
    clear hpre hscr hzlv htg hg1 hg2
    janus_run [toInt_small xl (by omega), toInt_small (BitVec.ofNat 64 i) (by simp; omega), hmask,
      and_ones64 i (by omega), mod64_of_lt (t + 8 * i) (by omega),
      (by omega : (18446744073709551616 - i + (i + i)) % 18446744073709551616 = i),
      m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16] until [callMV]
    refine body2 impl R hMV' b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE Q i h1 hiy S.mem hI
      (fun S hpc hsp h28 h29 h18 r0 r2 r3 r4 r5 r6 r8 hI => ih S (i + 1) (by omega) (by omega) hpc hsp h28 h29 h18
        r0 r2 r3 r4 r5 r6 r8 hI) _ ?_ ?_ ?_ ?_ ?_ ?F ?z0 ?z1 ?_ ?_ ?_ ?_ ?f5 ?_ ?_ ?inv
    case F => janus_frame
    case z0 => janus_simp; simp only [Nat.mul_comm i 8]
    case z1 => janus_simp; simp only [Nat.mul_comm i 8]
    case f5 => janus_simp; simp only [Nat.mul_comm i 8]
    case inv =>
      refine RtInv.inv_frame' (ws := [(zp.toNat + 16 * i, zp.toNat + 16 * i + 16), (s.sp.toNat - 200, s.sp.toNat - 112),
        (s.sp.toNat - 72, s.sp.toNat - 56)]) (by janus_frame) (fun r hr => ?_) minv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simp only [Nat.add_sub_cancel_left]; exact (hzh1.sub (by omega) (by omega)).symm
      · left; exact hout.of_sub (by omega) (by omega)
      · left; exact hout.of_sub (by omega) (by omega)
    all_goals janus_simp

end FvModexp.Arm64.BasicSqr
