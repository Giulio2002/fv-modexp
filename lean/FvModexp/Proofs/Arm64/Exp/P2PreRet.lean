import FvModexp.Proofs.Arm64.Exp.P2PreJ

/-!
# `buildPrecomputationWindowModPower2` (arm64): the loop head at `i = pl` → `RET` (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem headRet {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}
    (hkc : 4608 ≤ kc) (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) :
    HeadJ impl R kc sqC mlC b L st pw pl lm x xl s pl := by
  intro S bp L1 b1 hpc hsp h28 h29 h18 h0 h7 h9 hc hd ht he h2 hi hb
  have hsl := s.sp.isLt
  obtain ⟨hal, hb', ha, hw⟩ := hpre.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (208 + kc)) (208 + kc + 80) true = true := by
    rw [hc.fr.accessible]; exact hw
  obtain ⟨e0, e1, -, -, -, -, -, -, e8, -, -, -⟩ := hc.sl
  have f48 : S.mem.readLE (s.sp.toNat - 208 + 160) 8 = pl := by
    rw [show s.sp.toNat - 208 + 160 = s.sp.toNat - 48 by omega]; exact e8
  have f1 : S.mem.readLE (s.sp.toNat - 208) 8 = (s.regs 30).toNat := e0
  have f2 : S.mem.readLE (s.sp.toNat - 208 - 8) 8 = (s.regs 29).toNat := by
    rw [show s.sp.toNat - 208 - 8 = s.sp.toNat - 216 by omega]; exact e1
  have hpl : pl < 2 ^ 63 := by have := hpre.2.2.2.2.1; rcases hpre.2.2.2.1 with rfl | rfl <;> simp_all
  unfold Goal
  janus_run [f48, f1, f2]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, bp, fun j hj => hd j hj, L1, b1, hc.le, hb, hc.inv, hc.scr, hc.sap, hc.sa, hc.fr, hc.lf, hc.ain, hc.bu⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  all_goals janus_simp
  all_goals omega

end FvModexp.Arm64.P2Pre
