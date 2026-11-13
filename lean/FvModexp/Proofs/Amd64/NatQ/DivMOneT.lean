import FvModexp.Proofs.Amd64.NatQ.DivMDefs
import FvModexp.Proofs.Amd64.NatQ.DivOneF

set_option autoImplicit false

/-!
# `nat.div` (amd64), `z = nil`, `z2 = u` (`(*Int).Mod`'s call), `len v = 1`: `r = u.setWord(r2)`, return (top s40)

Twin of Arm64/NatQ/DivMOneT.lean: `oneFinM` (the `PostM` of the `len v = 1` paths; no quotient fact: `(*Int).Mod`
ignores it) and `oneAM` (`r2 = 0`: `r = u[:0]`) = Amd64/NatQ/DivOneT.lean's `oneA` with `z = nil`, `z2 = u`.
`oneBM` / `oneCM`: DivMOneTB / DivMOneTC.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the postcondition of the `len v = 1` paths** (`z = nil`, `z2 = u`): the quotient is unconstrained -/
theorem oneFinM {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vc : Nat} {s : State}
    (hpre : PFM R b dc L u ul uc v 1 vc s) {q ql qc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {T : State} (hW : AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T) (s' : State) {r rl rc : Nat}
    {L'' : List (Nat × Nat)} {b'' : Nat}
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (h0 : s'.regs 0 = BitVec.ofNat 64 q) (h1 : s'.regs 3 = BitVec.ofNat 64 ql) (h2 : s'.regs 1 = BitVec.ofNat 64 qc)
    (h3 : s'.regs 7 = BitVec.ofNat 64 r) (h4 : s'.regs 6 = BitVec.ofNat 64 rl) (h5 : s'.regs 8 = BitVec.ofNat 64 rc)
    (hM : MemFrame T.mem s'.mem (R.rt ++ win s 41512 112 ++ ar u uc)) (hLF2 : LiveFrame T.mem s'.mem L' (ar u uc))
    (hext2 : LiveExt R L' L'') (hb2 : b' - makeCost 1 ≤ b'')
    (hinv : R.inv b'' L'' (s.regs 14).toNat (view R.rt L'' s'.mem))
    (hr : ExpHyp.NatOF R L L'' s'.mem u uc 1 r rl rc (natVal s.mem u ul % natVal s.mem v 1)) :
    PostM R b dc L u ul uc v 1 s s' := by
  have hc := hpre.cost
  have hbW := hW.bud
  have e0 : ar 0 0 = [] := rfl
  refine ⟨hfs, hdf, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L'', b'', hr, ⟨hW.ext.trans hext2, ?_, hinv⟩,
    hW.mf.trans hM fun a n h => ⟨?_, ?_⟩, ⟨fun a n hin ho => ?_⟩⟩
  · simp only [costMQ, costQ, DivLarge.costQ] at hc ⊢; omega
  · rw [e0]; simp only [outside_append, outside_nil, and_true] at h ⊢; exact h.1
  · simp only [outside_append] at h ⊢; exact ⟨h.1, outside_ar_of h.2⟩
  · have ho' : Outside a n (ar u uc) := outside_ar_of ho
    rw [hLF2.readLE a n (hW.ext.inRanges_old hin) ho']
    exact hW.lf.readLE a n hin (by rw [e0]; trivial)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- `r2 = 0`: `r = u[:0]` -/
theorem oneAM (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vc : Nat} {s : State}
    (hpre : PFM R b dc L u ul uc v 1 vc s) {q ql qc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {T : State} (hW : AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T)
    (hr0 : natVal s.mem u ul % natVal s.mem v 1 = 0) (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) T (RQM R b dc L u ul uc v 1 s) := by
  have hp := hpre
  have hce := hp.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hz2 := hp.uo
  have hext := hW.ext
  have hB : Box (PFM R b dc L u ul uc v 1 vc s ∧ AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T) := ⟨⟨hpre, hW⟩⟩
  have hpc := hW.pc; have hsp := hW.sp; have h5 := hW.r5; have h14 := hW.r14; have hfs := hW.fs
  have hx15 := hW.x15; have hdf := hW.df
  have hr0' := hW.r0; have hr3 := hW.r3; have hr1 := hW.r1
  have h7 : T.regs 7 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hW.r7, hr0]; rfl)
  have hTacc : T.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hW.mf.accessible]; exact hw
  have m1 := hW.ra; have m2 := hW.bp; have m5 := hW.s5; have m7 := hW.s7
  have hinvT := hW.inv
  have hacc := hW.mf.accessible
  clear hpre hW hp
  janus64_run [m1, m2, m5, m7, h7]
  obtain ⟨hpre, hW⟩ := hB.h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, oneFinM (r := u) (rl := 0) (rc := uc) hpre hW _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hLF
    (LiveExt.refl R L') (Nat.sub_le _ _) ?hI ?hR⟩
  case hM => exact (winFrame hce hext (by janus_frame) (lo := (s.regs 4).toNat - 80)
    (hi := (s.regs 4).toNat - 32) (by omega) (by omega) u uc).1
  case hLF => exact (winFrame hce hext (by janus_frame) (lo := (s.regs 4).toNat - 80)
    (hi := (s.regs 4).toNat - 32) (by omega) (by omega) u uc).2
  case hI =>
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 80, (s.regs 4).toNat - 32)]) (by janus_frame)
      (fun r hr => ?_) hinvT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  case hR =>
    refine ⟨by simp [natVal, hr0], Or.inl rfl, Nat.zero_le _, hz2.1, natLive_ext hz2.2.1 ?_ hext, Or.inl ⟨rfl, rfl⟩⟩
    intro a n w; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hacc]
  all_goals try (janus64_simp; done)
  all_goals first
    | exact hx15.trans hx0.symm
    | exact hfs
    | (rw [hdf0]; rfl)
    | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact ofNat_modL _)

end FvModexp.Amd64.Q.NatDiv
