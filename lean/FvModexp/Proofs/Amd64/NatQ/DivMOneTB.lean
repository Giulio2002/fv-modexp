import FvModexp.Proofs.Amd64.NatQ.DivMOneT
import FvModexp.Proofs.Amd64.NatQ.DivOneTB

set_option autoImplicit false

/-!
# `nat.div` (amd64), `z = nil`, `z2 = u`, `len v = 1`: `r2 ≠ 0`, `cap u ≠ 0`: `u[0] = r2`, `r = u[:1]` (top s40)

Twin of Arm64/NatQ/DivMOneT.lean's `oneBM` = Amd64/NatQ/DivOneTB.lean's `oneB` with `z = nil`, `z2 = u` (the
remainder's word is written into the dividend's array after `divW` read it), concluding `RQM` via `oneFinM`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- `r2 ≠ 0`, `cap u ≠ 0`: `u[0] = r2`, `r = u[:1]` -/
theorem oneBM (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vc : Nat} {s : State}
    (hpre : PFM R b dc L u ul uc v 1 vc s) {q ql qc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {T : State} (hW : AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T)
    (hr0 : natVal s.mem u ul % natVal s.mem v 1 ≠ 0) (hc0 : 0 < uc)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) T (RQM R b dc L u ul uc v 1 s) := by
  have hp := hpre
  have hce := hp.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hz2 := hp.uo
  obtain ⟨hz8, hz2h, hz2acc, hz248⟩ := hz2.2.1 hc0
  have hz2w := (hz2.2.2 hc0).1
  simp only [win, outside_cons, outside_nil, and_true] at hz2w
  have hz40 := hz2.1
  have hext := hW.ext
  have hB : Box (PFM R b dc L u ul uc v 1 vc s ∧
      AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T) := ⟨⟨hpre, hW⟩⟩
  have hpc := hW.pc; have hsp := hW.sp; have h5 := hW.r5; have h14 := hW.r14; have hfs := hW.fs
  have hx15 := hW.x15; have hdf := hW.df
  have hr0' := hW.r0; have hr3 := hW.r3; have hr1 := hW.r1
  have e7 := hW.r7
  have h7 : (T.regs 7 = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at e7; exact hr0 (by rw [← e7]; rfl)
  have hz2c : (BitVec.ofNat 64 uc = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hTacc : T.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hW.mf.accessible]; exact hw
  have hacc := hW.mf.accessible
  have hzacc : T.mem.accessible u 8 true = true := by
    rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ hz2acc (Nat.le_refl _) (by omega)
  have m1 := hW.ra; have m2 := hW.bp; have m5 := hW.s5; have m7 := hW.s7
  have hinvT := hW.inv
  clear hpre hW hp
  janus64_run [m1, m2, m5, m7, h7, hz2c]
  obtain ⟨hpre, hW⟩ := hB.h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, oneFinM (r := u) (rl := 1) (rc := uc) hpre hW _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hLF
    (LiveExt.refl R L') (Nat.sub_le _ _) ?hI ?hR
    ⟩
  case hM => exact (winFrame2 hce hext (by janus_frame) (lo := (s.regs 4).toNat - 80)
    (hi := (s.regs 4).toNat - 32) (by omega) (by omega) hc0).1
  case hLF => exact (winFrame2 hce hext (by janus_frame) (lo := (s.regs 4).toNat - 80)
    (hi := (s.regs 4).toNat - 32) (by omega) (by omega) hc0).2
  case hI =>
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 80, (s.regs 4).toNat - 32), (u, u + 8)]) (by janus_frame)
      (fun r hr => ?_) hinvT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · rcases hz2h.sub (a := u) (n := 8) (Nat.le_refl _) (by omega) with h | h
      · right; simpa using hext.inRanges_old h
      · left; simpa using h
  case hR =>
    refine ⟨?_, Or.inr ?_, by omega, hz40, natLive_ext hz2.2.1 ?_ hext, Or.inl ⟨rfl, rfl⟩⟩
    · show Janus.Arm64.Memory.readLE _ u (8 * 1) = _
      simp (disch := omega) only [Nat.mul_one, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        FvModexp.Expmc.readLE_writeLE_same]
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt (T.regs 7).isLt]; exact e7
    · show Janus.Arm64.Memory.readLE _ (u + 8 * (1 - 1)) 8 ≠ 0
      simp (disch := omega) only [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        FvModexp.Expmc.readLE_writeLE_same]
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt (T.regs 7).isLt, e7]; exact hr0
    · intro a n w; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hacc]
  all_goals try (janus64_simp; done)
  all_goals first
    | exact hx15.trans hx0.symm
    | exact hfs
    | (rw [hdf0]; rfl)
    | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact ofNat_modL _)

end FvModexp.Amd64.Q.NatDiv
