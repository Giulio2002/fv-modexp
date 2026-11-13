import FvModexp.Proofs.Arm64.NatQ.SqrMakeAP

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/SqrMakeA2.lean — TIGHT COSTS, divmc s34] `nat.sqr` (arm64), `make_alloc`: the `makeslice(Word, 2n, 2n + 4)` call at `0x1bb500` (`AA`) → the join
`0x1bb524` (`Core`, `JoinAt`) (adapted from MulMakeA2)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatSqr

variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem alloc_call (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibSqr.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (W : Nat)
    (zp _zl zc st xp xl xc : BitVec 64) (s S : State) (hA : AA s S W st xp xl xc)
    (hpre : SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s) (hx : 2 ≤ xl.toNat)
    (hz : zc.toNat < 2 * xl.toNat ∨ zp.toNat + 8 * zc.toNat = xp.toNat + 8 * xc.toNat) (Q : State → Prop)
    (hK : ∀ (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (S : State),
      Core R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat s p c L1 b1 S.mem →
      JoinAt s S p c st xp xl xc → ReachesRet (LibSqr.program.link impl) (s.regs 30) S Q) :
    ReachesRet (LibSqr.program.link impl) (s.regs 30) S Q := by
  obtain ⟨hround, hsize, hnoscan⟩ := mk_facts hpre hA rfl
  have hc := mk_pre hpre hx hA rfl
  have hpre' := hpre
  obtain ⟨hce, hsw, -, -, -, hxlc, -, hxl12, -, hxh, -, -, -, -, -, -, -, -, -, -, -⟩ := hpre'
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hW : 4880 ≤ W := by unfold sqrW ksqrW at hsw; omega
  have hxh' := (hxh (by omega)).1
  have hmc : makeB (2 * xl.toNat) = allocCost (8 * (2 * xl.toNat + 4)) := rfl
  obtain ⟨hpc, hr30, r0, r1, r2, hsp, hg, hfp, h18, mlr, mfp, m96, m88, m208, m216, m224, m232, hF0, hreg⟩ := hA
  have hsp' : S.sp.toNat = s.sp.toNat - 176 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  clear hxh hsw
  refine ReachesRet.call_regions (hmk.pos L b) hpc hc ?_
  intro S1 hpc1 ⟨ptr, junk, f1, v1, m, ex1, ep1, hs1, hMF, hLF, ⟨hobj, hAp⟩, hapS, hinv'⟩ hreg1
  subst hs1
  clear hc
  simp only [makesliceObj, Fresh, hsize, hnoscan] at hobj
  rw [hround] at hAp hinv'
  rw [hg] at hinv'
  obtain ⟨hIn, hle, hacc, h8, -, -, hsz⟩ := hobj
  simp only [calleeStack, hsp'] at hMF hapS
  have hrd : ∀ a, (s.sp.toNat - 184 ≤ a ∧ a + 8 ≤ s.sp.toNat - 168) ∨ (s.sp.toNat - 88 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) →
      m.readLE a 8 = S.mem.readLE a 8 := by
    intro a ha
    refine hMF.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have q96 := (hrd _ (by omega)).trans m96
  have q88 := (hrd _ (by omega)).trans m88
  have q208 := (hrd _ (by omega)).trans m208
  have q216 := (hrd _ (by omega)).trans m216
  have q224 := (hrd _ (by omega)).trans m224
  have q232 := (hrd _ (by omega)).trans m232
  have qlr := (hrd _ (by omega)).trans mlr
  have qfp := (hrd _ (by omega)).trans mfp
  have bx : IntAS.Box (S.mem.readLE (s.sp.toNat - 176) 8 = (s.regs 30).toNat ∧
      S.mem.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat ∧ S.mem.readLE (s.sp.toNat - 80) 8 = 2 * xl.toNat) :=
    ⟨mlr, mfp, m96⟩
  clear hrd m96 m88 m208 m216 m224 m232 mlr mfp
  janus_run [hsp', hr30, hreg, q96, q88, q208, q216, q224, q232] until [0x1bb524]
  all_goals
    refine hK ptr.toNat (2 * xl.toNat + 4) _ _ _ (Core.win (core_alloc (c := 2 * xl.toNat + 4) hpre hF0
        ?qcs hLF hMF hAp hIn hle hacc (h8 (Or.inr (by omega))) hinv' ?q1 ?q2 ?q3 ?q4 ?q5 hz) ?hF2)
      ⟨?jpc, ?j0, ?j1, ?j2, ?j3, ?j4, ?j5, ?j6, ?jsp, ?jg, ?jfp, ?j18, ?jlr, ?jmfp, ?j64, ?j80, ?j88, ?jreg,
        apart_of_held (hxh'.sub (Nat.le_refl _) (by omega)) (hIn.sub (Nat.le_refl _) ?qs1)
          (ApartAll.sub' hAp (Nat.le_refl _) ?qs2), ?qna⟩
    case qna =>
      have := apart_of_held hxh' (hIn.sub (Nat.le_refl _) (n := 8 * (2 * xl.toNat + 4)) (by omega))
        (ApartAll.sub' hAp (Nat.le_refl _) (by omega))
      unfold Apart at this; omega
    case qs1 => omega
    case qs2 => omega
    case hF2 => simp only [winA]; janus_frame
    case qcs => intro a n h; simp only [winA, outside_cons, outside_nil, and_true] at h ⊢; omega
    case q1 => omega
    case q2 => rw [hmc]; exact blockSize_le_allocCost _ true
    case q3 => omega
    case q4 => omega
    case q5 => omega
    case jpc => rfl
    case jsp => rfl
    case j0 => simp only [setReg_apply, callRegs_apply]; simp
    case j1 => simp only [setReg_apply, callRegs_apply]; simp
    case j2 => simp only [setReg_apply, callRegs_apply]; simp
    case j3 => simp only [setReg_apply, callRegs_apply]; simp
    case j4 => simp only [setReg_apply, callRegs_apply]; simp
    case j5 => simp only [setReg_apply, callRegs_apply]; simp
    case j6 => simp only [setReg_apply, callRegs_apply]; simp
    case jg => simp only [setReg_apply, callRegs_apply]; simpa using hg
    case jfp => simp only [setReg_apply, callRegs_apply]; simpa using hfp
    case j18 => simp only [setReg_apply, callRegs_apply]; simpa using h18
    case jlr => janus_simp; first | exact bx.h.1 | exact qlr
    case jmfp => janus_simp; first | exact bx.h.2.1 | exact qfp
    case j64 => janus_simp
    case j80 => janus_simp; first | exact bx.h.2.2 | exact q96
    case j88 => janus_simp
    case jreg => janus_simp; exact hreg1.trans hreg

end FvModexp.Arm64.Q.NatSqr
