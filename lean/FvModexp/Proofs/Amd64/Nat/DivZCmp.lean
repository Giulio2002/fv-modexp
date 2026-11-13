import FvModexp.Proofs.Amd64.Nat.DivCmp
import FvModexp.Proofs.Amd64.Nat.DivG

set_option autoImplicit false

/-!
# `nat.div` (amd64), `len v ≥ 2`, from `PreG` (possibly empty dividend with any pointer): entry → `nat.cmp` (`two1G` = `DivCmp.two1` on `PreG`; twin of arm64 `DivMLessA.two1G`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- entry → `nat.cmp`'s entry (`len v ≥ 2`), from `PreG` -/
theorem two1G (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vl vc : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn)) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = z2)
    (h8 : s.regs 8 = z2l) (h9 : s.regs 9 = z2c) (hv2 : 2 ≤ vl)
    (hpre : PreG R b dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s)
    (Q : State → Prop)
    (k : ∀ X : State, AtK zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v vl vc s X →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) s Q := by
  have hp := hpre.f
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -⟩ := hp.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have r1 := hp.ru; have r2 := hp.rul; have r3 := hp.ruc; have r4 := hp.rv; have r5 := hp.rvl; have r6 := hp.rvc
  have hvl : vl < 2 ^ 40 := hp.vo.1
  have hul : ul < 2 ^ 40 := hp.ui.1
  have hv0 : (BitVec.ofNat 64 vl = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
  have hv1 : (BitVec.ofNat 64 vl = 1#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  clear hpre hp
  janus64_run [r1, r2, r3, r4, r5, r6, hv0, hv1] until [cmpE]
  refine k _
    { pc := rfl, sp := ?_, r5 := ?_, r14 := ?_, fs := ?_, x15 := ?_, df := ?_, a0 := ?_, a3 := ?_, a1 := ?_,
      a7 := ?_, a6 := ?_, a8 := ?_, rc := ?_, mf := ?qF, reg := ?qR, bp := ?_, s1 := ?_, s2 := ?_, s3 := ?_,
      s4 := ?_, s5 := ?_, s6 := ?_, s7 := ?_, q0 := ?_ }
  case qF => unfold proW; janus_frame
  case qR => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals try (janus64_simp; done)
  all_goals first | exact hx15 | exact hdf | (janus64_simp; omega) | rfl

end FvModexp.Amd64.NatDiv
