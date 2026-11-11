import FvModexp.Proofs.Arm64.Nat.DivBasicAddB

/-!
# `divBasic` (arm64): the add-back, all cases (`c = 0`; `c ≠ 0` with `qhl = n` (`addA`) / `qhl = n + 1` (`addB`))
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem add0 (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qhat q : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S afterSub j)
    (hqh : S.mem.readLE (s.sp.toNat - 96) 8 = qhat) (hbw : S.mem.readLE (s.sp.toNat - 160) 8 = 0) (Q : State → Prop)
    (k : ∀ S', AddK R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S S' j qhat q 0 →
      ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S Q := by
  obtain ⟨hpc, hsp, h28, h29, h18, hM, hjj⟩ := hB
  have s8 := hM.s8; have s4 := hM.s4; have s5 := hM.s5
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hE.pre.ce
  have hwacc : S.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [hMacc]; exact hw
  have hsp0 := hE.lay.sp0; have hsp1 := hE.lay.sp1
  janus_run [hqh, hbw, s8, s4, s5] until [tailPt]
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, hM, hjj⟩, ?_, ?_, ?_, ?_, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩,
    fun _ _ _ => rfl, fun h => absurd rfl h⟩
  all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals janus_simp

theorem add1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qhat q bw : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S afterSub j)
    (hqh : S.mem.readLE (s.sp.toNat - 96) 8 = qhat) (hql : S.mem.readLE (s.sp.toNat - 120) 8 = q)
    (huj : S.mem.readLE (s.sp.toNat - 48) 8 = up + 8 * j) (hcj : S.mem.readLE (s.sp.toNat - 64) 8 = uc - j)
    (hbw : S.mem.readLE (s.sp.toNat - 160) 8 = bw) (hq : q = vl ∨ q = vl + 1) (hj : j + q ≤ ul) (Q : State → Prop)
    (k : ∀ S', AddK R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S S' j qhat q bw →
      ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S Q := by
  by_cases h0 : bw = 0
  · subst h0; exact add0 impl R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S j qhat q hB hqh hbw Q k
  · rcases hq with h | h <;> rw [h] at hql hj k
    · exact addA impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S j qhat bw hB hqh hql huj hcj hbw h0
        hj Q k
    · exact addB impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S j qhat bw hB hqh hql huj hcj hbw h0
        hj Q k

end FvModexp.Arm64.DivBasic
