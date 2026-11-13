import FvModexp.Proofs.Amd64.Exp.SubMod2NGS2J

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64): `J1` → `J2` when `len y = 0` (agent infra)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem s2Gz (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State) (hy0 : yl = 0)
    (k2 : J2G impl R b L op zp zl zc yp yl yc n s) : J1G impl R b L op zp zl zc yp yl yc n s := by
  intro S l1 L1 b1 hpre hpc hsp hab h0 h3 h1 h7 h6 h8 h9 h10 h11 h12 hfw hrt hv hnorm hlc
  have hpre' := hpre
  obtain ⟨⟨⟨hgN, hgR, hgB⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, hzl',
    hyl, hyc, hyl', hzlive, hzw, hzg, -, hya, hy48, hyh, hyw, hyn, hzy, -⟩ := hpre'
  obtain ⟨h14, hfs, hx15, hdf⟩ := hab
  have hent := hpre.ent
  simp only [win, outside_cons, outside_nil, and_true] at hzw hout
  simp only [K, A, regG, regSP, stackguard0Offset, stackguard0] at hw hout hzw hgB hb' ha hga hgN hgR
  have hacc : S.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by rw [hrt.2.1.accessible]; exact hw
  unfold GoalG
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw
  subst hy0
  have hmA : (BitVec.ofNat 64 0 + 18446744073709551615#64).msb = true := by decide
  have hmB : (BitVec.ofNat 64 0 - 1#64).msb = true := by decide
  have hmC : (18446744073709551615#64).msb = true := by decide
  have b16 : (s.regs 4).toNat - 128 + 112 = (s.regs 4).toNat - 16 := by omega
  have b40 : (s.regs 4).toNat - 128 + 88 = (s.regs 4).toNat - 40 := by omega
  have b32 : (s.regs 4).toNat - 128 + 96 = (s.regs 4).toNat - 32 := by omega
  janus64_run [hmA, hmB, hmC, b16, b40, b32] until [6216422]
  refine j2G_skip k2 hpre hrt hv hnorm hlc _ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [win, K, A]; janus_frame
  all_goals try janus64_simp
  all_goals first
    | exact h14 | exact hfs | exact hx15 | exact hdf
    | (refine fw_loc (by omega) ⟨f1, f2, f3, f4, f5, f6, f7⟩ ?_; janus_frame)
    | exact Nat.lt_of_lt_of_le (natVal_lt _ _ _) (Nat.one_le_two_pow)
    | skip

end FvModexp.Amd64.SubMod2N
