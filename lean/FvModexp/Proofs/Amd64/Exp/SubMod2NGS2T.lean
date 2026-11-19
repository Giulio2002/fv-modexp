import FvModexp.Proofs.Amd64.Exp.SubMod2NGS2J
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.GenReg

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64): `J1` → `J2` when `y.bitLen() > n`: `y = nat(nil).trunc(y, n)` (agent infra)

`alias(z, y)` is false (`y`'s array is apart from `z`'s): a fresh array (`TruncHyp`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem s2Gtr (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) (hy0 : yl ≠ 0)
    (hc0 : ¬ 64 * (yl - 1) + Aux.bitLen (s.mem.readLE (yp + 8 * (yl - 1)) 8) ≤ n)
    (k2 : J2G impl R b L op zp zl zc yp yl yc n s) : J1G impl R b L op zp zl zc yp yl yc n s := by
  intro S l1 L1 b1 hpre hpc hsp hab h0 h3 h1 h7 h6 h8 h9 h10 h11 h12 hfw hrt hv hnorm hlc
  have hpre' := hpre
  obtain ⟨⟨⟨hgN, hgR, hgB, _⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, hzl',
    hyl, hyc, hyl', hzlive, hzw, hzg, -, hya, hy48, hyh, hyw, hyn, hzy, -⟩ := hpre'
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  have hent := hpre.ent
  have hy0' : 0 < yl := Nat.pos_of_ne_zero hy0
  replace hya := hya hy0'
  replace hy48 := hy48 hy0'
  replace hyh := hyh hy0'
  replace hyw := hyw hy0'
  simp only [win, outside_cons, outside_nil, and_true] at hzw hout hyw
  simp only [K, A, regG, regSP, stackguard0Offset, stackguard0] at hw hout hzw hgB hb' ha hga hyw hgN hgR
  have hacc : S.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by rw [hrt.2.1.accessible]; exact hw
  have hya' : S.mem.accessible yp (8 * yl) false = true := by rw [hrt.2.1.accessible]; exact hya
  have hywA : Outside yp (8 * yl) (win s K A) := by
    simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
  have hzyl : 0 < zc → Apart yp (8 * yl) zp (8 * zc) := fun hz => by
    have := hzy hz hy0'; unfold Apart at this ⊢; omega
  have hyv : natVal S.mem yp yl = natVal s.mem yp yl := rd_heldG hrt hyh hywA hzyl
  unfold GoalG
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw
  have hyt : S.mem.readLE (yp + 8 * (yl - 1)) 8 = s.mem.readLE (yp + 8 * (yl - 1)) 8 :=
    rd_heldG hrt (hyh.sub (by omega) (by omega)) (hywA.of_sub (by omega) (by omega))
      (fun hz => by have := hzyl hz; unfold Apart at this ⊢; omega)
  have e0 : (BitVec.ofNat 64 yl + 18446744073709551615#64).toNat = yl - 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have e0' : (BitVec.ofNat 64 yl - 1#64).toNat = yl - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hm0 : (BitVec.ofNat 64 yl + 18446744073709551615#64).msb = false := by
    rw [BitVec.msb_eq_decide, e0]; simp; omega
  have hm1 : (BitVec.ofNat 64 yl - 1#64).msb = false := by
    rw [BitVec.msb_eq_decide, e0']; simp; omega
  have e1 : (yp % 18446744073709551616 + (yl - 1) * 8) % 18446744073709551616 = yp + 8 * (yl - 1) := by omega
  janus64_run [hm0, hm1] until [6216197]
  janus64_run [e1] until [6216202]
  generalize hxd : BitVec.ofNat 64 (S.mem.readLE (yp + yl * 8 - 8) 8) = x
  janus64_run until [6216265]
  gen_reg 15 as t with hT
  have hts : t = BitLenA64.smearBV x := by rw [← hT, BitVec.or_comm]; rfl
  have hx0 : x.toNat ≠ 0 := by
    rcases hyn with h | h
    · omega
    · rw [← hxd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Util.readLE8_lt _ _),
        show yp + yl * 8 - 8 = yp + 8 * (yl - 1) by omega, hyt]; exact h
  have ht0 : t.toNat ≠ 0 := by rw [hts]; exact (BitLenA64.smearBV_log2 x hx0).1
  have ht0' : (t.toNat = 0) = False := by simp [ht0]
  janus64_run [ht0, ht0'] until [6216288]
  gen_reg 2 as bl with hBl
  have hbl : bl.toNat = 64 * (yl - 1) + Aux.bitLen (s.mem.readLE (yp + 8 * (yl - 1)) 8) := by
    rw [← hBl]
    refine BitLenA64.bl_exact64 _ _ _ (Util.readLE8_lt _ _) ?_ ?_ (by omega) (by omega)
    · intro h; apply hx0; rw [← hxd, BitVec.toNat_ofNat, show yp + yl * 8 - 8 = yp + 8 * (yl - 1) by omega, hyt, h]
    · rw [hts, BitLenA64.clz_smear, ← hxd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Util.readLE8_lt _ _),
        show yp + yl * 8 - 8 = yp + 8 * (yl - 1) by omega, hyt]
  have hc : ¬ bl.toNat ≤ n := by rw [hbl]; exact hc0
  have b16 : (s.regs 4).toNat - 128 + 112 = (s.regs 4).toNat - 16 := by omega
  have b40 : (s.regs 4).toNat - 128 + 88 = (s.regs 4).toNat - 40 := by omega
  have b32 : (s.regs 4).toNat - 128 + 96 = (s.regs 4).toNat - 32 := by omega
  have b136 : (s.regs 4).toNat - 128 - 8 = (s.regs 4).toNat - 136 := by omega
  by_cases hz0 : zc = 0
  · have hcz : (zc = 0) = True := by simp [hz0]
    janus64_run [hc, hcz, b16, b40, b32, b136] until [6188320]
    have hwy : yp + 8 * yl ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ yp := by
      simp only [win, K, A, outside_cons, outside_nil, and_true] at hywA; omega
    refine truncCallW hap hns htr (zp := 0) (zl := 0) (zc := 0) (x := yp) (xl := yl) (xc := yc) (n := n)
      (ra := 6216398) (ra_of hap hnf 0x22e (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (truncPreG_nil hpre hpre.costB (rtG_stk hpre hrt ?_ ?_) (by omega) rfl ?_ ?_ ?_ hkT haT (by omega)
        ?_ hy48 (hrt.2.2.2.1.held hyh) hwy (by omega))
      (Or.inr (by have := bitLen_le64 (s.mem.readLE (yp + 8 * (yl - 1)) 8) (Util.readLE8_lt _ _); omega))
      (Or.inr (Or.inr ⟨by omega, by omega⟩))
      fun s' hpc' hsp' h14' hx' hreg' hpost => ?qK
    case qK =>
      have hzw' : Outside zp (8 * l1) (win s K A) := by
        simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
      refine s2Gt impl k2 hpre hkT haT _ (rtG_stk hpre hrt ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ hlc (by omega) ?_ _ rfl ?_ ?_ ?_ ?_ ?_
        s' hpc' hsp' h14' hx' hreg' hpost
      · simp only [win, K, A]; janus_frame
      · janus64_simp
      · simp only [Fw]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp
      · janus64_simp <;> omega
      · janus64_simp <;> omega
      · janus64_simp <;> omega
      · refine (natVal_frame (m := S.mem) (rs := win s K A) ?_ hzw').trans hv
        simp only [win, K, A]; janus_frame
      · refine natNorm_frame (m := S.mem) (rs := win s K A) ?_ hzw' hnorm
        simp only [win, K, A]; janus_frame
      · refine (natVal_frame (m := S.mem) (rs := win s K A) ?_ hywA).trans hyv
        simp only [win, K, A]; janus_frame
      · janus64_simp <;> omega
      · janus64_simp <;> exact h14
      · janus64_simp <;> exact hfs
      · janus64_simp <;> exact hx15
      · janus64_simp <;> exact hdf
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp <;> first | exact hent.2.2.2.1 | (rw [hx15]; exact hent.2.2.2.1)
    · janus64_simp <;> exact hdf
    · simp only [win, K, A]; janus_frame
    · janus64_simp
    · janus64_simp <;> omega
    · janus64_simp <;> exact h14
    · janus64_simp <;> exact hfs
    · janus64_simp <;> exact hya'
  · have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
    have hzy' := hzy (by omega) hy0'
    unfold Apart at hzy'
    have hcz : (zc = 0) = False := by simp; omega
    have hycz : (yc = 0) = False := by simp; omega
    janus64_run [hc, hcz, hycz, b16, b40, b32, b136] until [6188320]
    have hwy : yp + 8 * yl ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ yp := by
      simp only [win, K, A, outside_cons, outside_nil, and_true] at hywA; omega
    refine truncCallW hap hns htr (zp := 0) (zl := 0) (zc := 0) (x := yp) (xl := yl) (xc := yc) (n := n)
      (ra := 6216398) (ra_of hap hnf 0x22e (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (truncPreG_nil hpre hpre.costB (rtG_stk hpre hrt ?_ ?_) (by omega) rfl ?_ ?_ ?_ hkT haT (by omega)
        ?_ hy48 (hrt.2.2.2.1.held hyh) hwy (by omega))
      (Or.inr (by have := bitLen_le64 (s.mem.readLE (yp + 8 * (yl - 1)) 8) (Util.readLE8_lt _ _); omega))
      (Or.inr (Or.inr ⟨by omega, by omega⟩))
      fun s' hpc' hsp' h14' hx' hreg' hpost => ?qK
    case qK =>
      have hzw' : Outside zp (8 * l1) (win s K A) := by
        simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
      refine s2Gt impl k2 hpre hkT haT _ (rtG_stk hpre hrt ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ hlc (by omega) ?_ _ rfl ?_ ?_ ?_ ?_ ?_
        s' hpc' hsp' h14' hx' hreg' hpost
      · simp only [win, K, A]; janus_frame
      · janus64_simp
      · simp only [Fw]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp
      · janus64_simp <;> omega
      · janus64_simp <;> omega
      · janus64_simp <;> omega
      · refine (natVal_frame (m := S.mem) (rs := win s K A) ?_ hzw').trans hv
        simp only [win, K, A]; janus_frame
      · refine natNorm_frame (m := S.mem) (rs := win s K A) ?_ hzw' hnorm
        simp only [win, K, A]; janus_frame
      · refine (natVal_frame (m := S.mem) (rs := win s K A) ?_ hywA).trans hyv
        simp only [win, K, A]; janus_frame
      · janus64_simp <;> omega
      · janus64_simp <;> exact h14
      · janus64_simp <;> exact hfs
      · janus64_simp <;> exact hx15
      · janus64_simp <;> exact hdf
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp <;> first | exact hent.2.2.2.1 | (rw [hx15]; exact hent.2.2.2.1)
    · janus64_simp <;> exact hdf
    · simp only [win, K, A]; janus_frame
    · janus64_simp
    · janus64_simp <;> omega
    · janus64_simp <;> exact h14
    · janus64_simp <;> exact hfs
    · janus64_simp <;> exact hya'

end FvModexp.Amd64.SubMod2N
