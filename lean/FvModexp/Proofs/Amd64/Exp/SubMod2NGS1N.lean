import FvModexp.Proofs.Amd64.Exp.SubMod2NGS1J
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.GenReg

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64): entry → `J1` when `x.bitLen() ≤ n` (agent infra)

`x.bitLen()` inline: the OR-smear, `BSR`, `CMOVE` (`BitLenA64.bl_exact64`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem s1Gn (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 6215840)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h3 : s.regs 3 = BitVec.ofNat 64 zl) (h1 : s.regs 1 = BitVec.ofNat 64 zc)
    (h7 : s.regs 7 = BitVec.ofNat 64 zp) (h6 : s.regs 6 = BitVec.ofNat 64 zl) (h8 : s.regs 8 = BitVec.ofNat 64 zc)
    (h9 : s.regs 9 = BitVec.ofNat 64 yp) (h10 : s.regs 10 = BitVec.ofNat 64 yl) (h11 : s.regs 11 = BitVec.ofNat 64 yc)
    (hpre : PreG R b L op zp zl zc yp yl yc n s) (hz0 : zl ≠ 0)
    (hc0 : 64 * (zl - 1) + Aux.bitLen (s.mem.readLE (zp + 8 * (zl - 1)) 8) ≤ n) (k1 : J1G impl R b L op zp zl zc yp yl yc n s) :
    GoalG impl R b L zp zl zc yp yl n s s := by
  have hpre' := hpre
  obtain ⟨⟨⟨hgN, hgR, hgB, _⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, hzl',
    hyl, hyc, hyl', hzlive, hzw, -⟩ := hpre'
  obtain ⟨hzf, hra, hn8, hx15, hdf⟩ := hpre.ent
  simp only [win, outside_cons, outside_nil, and_true] at hzw hout
  simp only [K, A, regG, regSP, stackguard0Offset, stackguard0] at hw hout hzw hgB hb' ha hga hgN hgR
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hza : s.mem.accessible zp (8 * zl) false = true :=
    Janus.Arm64.Memory.accessible_sub _ (hzlive (by omega)).2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega)
  unfold GoalG
  have e0 : (BitVec.ofNat 64 zl + 18446744073709551615#64).toNat = zl - 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have e0' : (BitVec.ofNat 64 zl - 1#64).toNat = zl - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hm0 : (BitVec.ofNat 64 zl + 18446744073709551615#64).msb = false := by
    rw [BitVec.msb_eq_decide, e0]; simp; omega
  have hm1 : (BitVec.ofNat 64 zl - 1#64).msb = false := by
    rw [BitVec.msb_eq_decide, e0']; simp; omega
  have e1 : (zp % 18446744073709551616 + (zl - 1) * 8) % 18446744073709551616 = zp + 8 * (zl - 1) := by omega
  janus64_run [hm0, hm1] until [6215891]
  janus64_run [e1] until [6215896]
  generalize hxd : BitVec.ofNat 64 (s.mem.readLE (zp + zl * 8 - 8) 8) = x
  janus64_run until [6215959]
  gen_reg 13 as t with hT
  have hts : t = BitLenA64.smearBV x := by rw [← hT, BitVec.or_comm]; rfl
  have hx0 : x.toNat ≠ 0 := by
    have hn := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rcases hn with h | h
    · omega
    · rw [← hxd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Util.readLE8_lt _ _),
        show zp + zl * 8 - 8 = zp + 8 * (zl - 1) by omega]; exact h
  have ht0 : t.toNat ≠ 0 := by rw [hts]; exact (BitLenA64.smearBV_log2 x hx0).1
  have ht0' : (t.toNat = 0) = False := by simp [ht0]
  janus64_run [ht0, ht0'] until [6215982]
  gen_reg 2 as bl with hBl
  have hbl : bl.toNat = 64 * (zl - 1) + Aux.bitLen (s.mem.readLE (zp + 8 * (zl - 1)) 8) := by
    rw [← hBl]
    refine BitLenA64.bl_exact64 _ _ _ (Util.readLE8_lt _ _) ?_ ?_ (by omega) (by omega)
    · intro h; apply hx0; rw [← hxd, BitVec.toNat_ofNat, show zp + zl * 8 - 8 = zp + 8 * (zl - 1) by omega, h]
    · rw [hts, BitLenA64.clz_smear, ← hxd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Util.readLE8_lt _ _),
        show zp + zl * 8 - 8 = zp + 8 * (zl - 1) by omega]
  have hc : bl.toNat ≤ n := by rw [hbl]; exact hc0
  janus64_run [hc] until [6216183]
  refine j1G_stack k1 hpre _ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [win, K, A]; janus_frame
  all_goals try janus64_simp
  all_goals first
    | exact Expmc.sp_sub _ _ (by omega) (by omega)
    | (simp only [Fw]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp)
    | (refine Nat.lt_of_lt_of_le (BitLenA64.natVal_lt_bl _ _ _ (by omega)) (Nat.pow_le_pow_right (by omega) ?_)
       omega)
    | skip

end FvModexp.Amd64.SubMod2N
