import FvModexp.Proofs.Arm64.Nat.DivBasic
import FvModexp.Proofs.Arm64.Nat.DivRel

/-!
# `nat.div` (arm64), `len v ≥ 2`: entry → `u.cmp(v)` (`CmpSum.cmp_summary`) → `AtC` (natdiv.go:518-532)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- entry → `nat.cmp`'s entry (`len v ≥ 2`) -/
theorem two1 (impl : List Segment) (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c up ul uc vp vl vc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = z2)
    (h5 : s.regs 5 = z2l) (h6 : s.regs 6 = z2c) (h7 : s.regs 7 = up) (h8 : s.regs 8 = ul) (h9 : s.regs 9 = uc)
    (h10 : s.regs 10 = vp) (h11 : s.regs 11 = vl) (h12 : s.regs 12 = vc) (hv2 : 2 ≤ vl.toNat)
    (hpre : Pre R b dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat up.toNat ul.toNat vp.toNat
      vl.toNat s)
    (Q : State → Prop)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 cmpE → X.sp = s.sp - 240#64 →
      X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 248#64 → X.regs 18 = s.regs 18 →
      X.regs 30 = BitVec.ofNat 64 retC → X.regs 0 = up → X.regs 1 = ul → X.regs 2 = uc → X.regs 3 = vp →
      X.regs 4 = vl → X.regs 5 = vc →
      MemFrame s.mem X.mem (proW s) → X.mem.regions = s.mem.regions →
      X.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat → X.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat →
      X.mem.readLE (s.sp.toNat + 8) 8 = zp.toNat → X.mem.readLE (s.sp.toNat + 16) 8 = zl.toNat →
      X.mem.readLE (s.sp.toNat + 24) 8 = zc.toNat → X.mem.readLE (s.sp.toNat + 32) 8 = st.toNat →
      X.mem.readLE (s.sp.toNat + 40) 8 = z2.toNat → X.mem.readLE (s.sp.toNat + 48) 8 = z2l.toNat →
      X.mem.readLE (s.sp.toNat + 56) 8 = z2c.toNat → X.mem.readLE (s.sp.toNat + 64) 8 = up.toNat →
      X.mem.readLE (s.sp.toNat + 72) 8 = ul.toNat → X.mem.readLE (s.sp.toNat + 80) 8 = uc.toNat →
      X.mem.readLE (s.sp.toNat + 88) 8 = vp.toNat → X.mem.readLE (s.sp.toNat + 96) 8 = vl.toNat →
      X.mem.readLE (s.sp.toNat + 104) 8 = vc.toNat →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) s Q := by
  have hp := hpre.f
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hp.ce
  have hv0 : (vl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at hv2; simp at hv2
  have hv1 : (vl = 1#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at hv2; simp at hv2
  clear hpre hp
  janus_run [hv0, hv1] until [cmpE]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?qF ?qR ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case qF => unfold proW; janus_frame
  case qR => simp only [Memory.regions_writeLE]
  all_goals try (janus_simp; done)
  all_goals (janus_simp; omega)

end FvModexp.Arm64.NatDiv
