import FvModexp.Proofs.Arm64.NatQ.SqrRel

/-!
# [Q-form copy of Arm64/Nat/SqrZero.lean — TIGHT COSTS, divmc s34] `nat.sqr` (arm64), `n = 0`: `return z[:0]` (`CBZ R5` → `+0x230`)
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zero (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp zl zc st xp xl xc : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 0x1bb420)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = st) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : xl.toNat = 0) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) s fun s' =>
      Kept s s' ∧ SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s s' := by
  have hpre' := hpre
  obtain ⟨hce, hsw, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk, -, -, -, -⟩ := hpre'
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
  obtain ⟨-, hstok, hstw, -, -, -, -, -, -⟩ := hstk
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hxl0 : xl = 0#64 := BitVec.eq_of_toNat_eq (by simp [hx])
  subst hxl0
  janus_run
  have hJ := core_reuse (M := s.mem) hpre (by simp) (MemFrame.refl _ _)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, post_of hJ (MemFrame.refl _ _) (by simp) (LiveExt.refl R L) (k := 0) (Or.inr ⟨Nat.le_refl _, rfl⟩)
    (by unfold sqrCQ; simp) hJ.inv
    (stackBack_keep hstok (MemFrame.refl _ []) (by simp) (LiveExt.refl R L)) (MemFrame.refl _ _)
    (LiveFrame.refl _ _ _) (s' := _) (l' := 0) ?qF ?_ ?_ ?_ (by simp) rfl (Or.inl rfl)⟩
  case qF => simp only [winA]; janus_frame
  all_goals janus_simp

end FvModexp.Arm64.Q.NatSqr
