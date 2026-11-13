import FvModexp.Proofs.Amd64.NatQ.SqrRel

set_option autoImplicit false

/-!
# [Q-form copy of Amd64/Nat/SqrZero.lean — TIGHT COSTS, divmc s38] `nat.sqr` (amd64), `n = 0`: `return z[:0]` (`TESTQ R8, R8; JE 0x5f126b`) — twin of the arm64 module
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zero (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 0x5f0fe0)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = zp) (h3 : s.regs 3 = zl) (h1 : s.regs 1 = zc) (h7 : s.regs 7 = st) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hpre : SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : xl.toNat = 0) :
    ReachesRet (LibSqr.program.link impl) (retAddrOf s) s fun s' =>
      Kept s s' ∧ SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨hce, hsw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk, -, -, -, -⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, -⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  obtain ⟨-, hstok, hstw, -, -, -, -, -, -⟩ := hstk
  have hW : 5056 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hxl0 : xl = 0#64 := BitVec.eq_of_toNat_eq (by simp [hx])
  subst hxl0
  janus64_run [BitVec.msb_eq_decide]
  have hJ := core_reuse (M := s.mem) hpre (by simp) (MemFrame.refl _ _)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, post_of hJ (MemFrame.refl _ _) (by simp) (LiveExt.refl R L) (k := 0) (Or.inr ⟨Nat.le_refl _, rfl⟩)
    (by unfold sqrCQ; simp) hJ.inv
    (stackBack_keep hstok (MemFrame.refl _ []) (by simp) (LiveExt.refl R L)) (MemFrame.refl _ _)
    (LiveFrame.refl _ _ _) (s' := _) (l' := 0) ?qF ?_ ?_ ?_ ?_ ?_ (by simp) rfl (Or.inl rfl)⟩
  case qF => simp only [win]; janus_frame
  all_goals janus64_simp

end FvModexp.Amd64.Q.NatSqr
