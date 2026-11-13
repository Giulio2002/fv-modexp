import FvModexp.Proofs.Amd64.Exp.SubMod2NGS1J

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64): entry → `J1` when `len x = 0` (agent infra)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem s1Gz (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 6215840)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h3 : s.regs 3 = BitVec.ofNat 64 zl) (h1 : s.regs 1 = BitVec.ofNat 64 zc)
    (h7 : s.regs 7 = BitVec.ofNat 64 zp) (h6 : s.regs 6 = BitVec.ofNat 64 zl) (h8 : s.regs 8 = BitVec.ofNat 64 zc)
    (h9 : s.regs 9 = BitVec.ofNat 64 yp) (h10 : s.regs 10 = BitVec.ofNat 64 yl) (h11 : s.regs 11 = BitVec.ofNat 64 yc)
    (hpre : PreG R b L op zp zl zc yp yl yc n s) (hz0 : zl = 0) (k1 : J1G impl R b L op zp zl zc yp yl yc n s) :
    GoalG impl R b L zp zl zc yp yl n s s := by
  have hpre' := hpre
  obtain ⟨⟨⟨hgN, hgR, hgB⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, hzl',
    hyl, hyc, hyl', hzlive, hzw, -⟩ := hpre'
  obtain ⟨hzf, hra, hn8, hx15, hdf⟩ := hpre.ent
  simp only [win, outside_cons, outside_nil, and_true] at hzw hout
  simp only [K, A, regG, regSP, stackguard0Offset, stackguard0] at hw hout hzw hgB hb' ha hga hgN hgR
  unfold GoalG
  subst hz0
  have hmA : (BitVec.ofNat 64 0 + 18446744073709551615#64).msb = true := by decide
  have hmB : (BitVec.ofNat 64 0 - 1#64).msb = true := by decide
  have hmC : (18446744073709551615#64).msb = true := by decide
  janus64_run [hmA, hmB, hmC] until [6216183]
  refine j1G_stack k1 hpre _ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [win, K, A]; janus_frame
  all_goals try janus64_simp
  all_goals first
    | exact Expmc.sp_sub _ _ (by omega) (by omega)
    | (simp only [Fw]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp)
    | exact Nat.lt_of_lt_of_le (natVal_lt _ _ _) (Nat.one_le_two_pow)
    | skip

end FvModexp.Amd64.SubMod2N
