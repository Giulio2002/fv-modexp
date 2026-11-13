import FvModexp.Proofs.Arm64.Nat.DivBasic
import FvModexp.Proofs.Arm64.Nat.DivRel

/-!
# `nat.div` (arm64), `len v = 1`: entry → `CALL nat.divW` → `AtW` (natdiv.go:518-527)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- entry → `divW`'s entry (`len v = 1`) -/
theorem one1 (impl : List Segment) (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c up ul uc vp vc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl) (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = z2)
    (h5 : s.regs 5 = z2l) (h6 : s.regs 6 = z2c) (h7 : s.regs 7 = up) (h8 : s.regs 8 = ul) (h9 : s.regs 9 = uc)
    (h10 : s.regs 10 = vp) (h11 : s.regs 11 = 1#64) (h12 : s.regs 12 = vc)
    (hpre : Pre R b dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat up.toNat ul.toNat vp.toNat 1 s)
    (Q : State → Prop)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 (segAddr Extracted.program DivW.fn) → X.sp = s.sp - 240#64 →
      X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 248#64 → X.regs 18 = s.regs 18 →
      X.regs 30 = BitVec.ofNat 64 retW → X.regs 0 = zp → X.regs 1 = zl → X.regs 2 = zc → X.regs 3 = up →
      X.regs 4 = ul → X.regs 5 = uc → X.regs 6 = BitVec.ofNat 64 (s.mem.readLE vp.toNat 8) →
      MemFrame s.mem X.mem (proW s) → X.mem.regions = s.mem.regions →
      X.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat → X.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat →
      X.mem.readLE (s.sp.toNat + 40) 8 = z2.toNat → X.mem.readLE (s.sp.toNat + 56) 8 = z2c.toNat →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) s Q := by
  have hp := hpre.f
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hp.ce
  obtain ⟨-, hvacc, hv48, -, hvw⟩ := hp.vo
  simp only [win, outside_cons, outside_nil, and_true] at hvw
  clear hpre hp
  janus_run until [segAddr Extracted.program DivW.fn]
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?qF ?qR ?_ ?_ ?_ ?_
  case qF => unfold proW; janus_frame
  case qR => simp only [Memory.regions_writeLE]
  all_goals try (janus_simp; done)
  all_goals (janus_simp; omega)

end FvModexp.Arm64.NatDiv
