import FvModexp.Proofs.Amd64.Exp.SubMod2NGS2J
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.GenReg

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64): `J1` → `J2` when `y.bitLen() ≤ n` (agent infra)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem s2Gn (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) (hy0 : yl ≠ 0)
    (hc0 : 64 * (yl - 1) + Aux.bitLen (s.mem.readLE (yp + 8 * (yl - 1)) 8) ≤ n)
    (k2 : J2G impl R b L op zp zl zc yp yl yc n s) : J1G impl R b L op zp zl zc yp yl yc n s := by
  intro S l1 L1 b1 hpre hpc hsp hab h0 h3 h1 h7 h6 h8 h9 h10 h11 h12 hfw hrt hv hnorm hlc
  have hpre' := hpre
  obtain ⟨⟨⟨hgN, hgR, hgB, -⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, hzl',
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
  have hc : bl.toNat ≤ n := by rw [hbl]; exact hc0
  janus64_run [hc] until [6216422]
  refine j2G_skip k2 hpre hrt hv hnorm hlc _ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [win, K, A]; janus_frame
  all_goals try janus64_simp
  all_goals first
    | exact h14 | exact hfs | exact hx15 | exact hdf
    | (refine fw_loc (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ ?_; janus_frame)
    | (refine Nat.lt_of_lt_of_le (BitLenA64.natVal_lt_bl _ _ _ (by omega)) (Nat.pow_le_pow_right (by omega) ?_)
       omega)
    | skip

end FvModexp.Amd64.SubMod2N
