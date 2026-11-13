import FvModexp.Proofs.Amd64.NatQ.DivMOneT
import FvModexp.Proofs.Amd64.Nat.WordTData

set_option autoImplicit false

/-!
# `nat.div` (amd64), `z = nil`, `z2 = u`, `len v = 1`: `r2 ≠ 0`, `cap u = 0`: `make(nat, 1)`, `r = [r2]` (top s40)

Twin of Arm64/NatQ/DivMOneT.lean's `oneCM` = Amd64/NatQ/DivOneTC.lean's `oneC` with `z = nil` (`cap z = 0`: its
array facts are vacuous), `z2 = u`, concluding `RQM` via `oneFinM`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
/-- `r2 ≠ 0`, `cap u = 0`: `make(nat, 1)` = `makeslice(Word, 1, 1)`, `r = [r2]` -/
theorem oneCM (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibDiv.program.link impl) (cA "runtime.makeslice") 4096 R)
    {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul v vc : Nat} {s : State}
    (hpre : PFM R b dc L u ul 0 v 1 vc s) {q ql qc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {T : State} (hW : AtW R b L 0 0 u 0 u ul v 1 s q ql qc L' b' T)
    (hr0 : natVal s.mem u ul % natVal s.mem v 1 ≠ 0)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) T (RQM R b dc L u ul 0 v 1 s) := by
  have hp := hpre
  have hce := hp.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, -, hro, ⟨htg, htr, htw⟩⟩ := hp.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hal
  unfold Apart at hga htw
  have hsv := hp.srv
  have hcost := hp.cost
  have hext := hW.ext
  have hbud := hW.bud
  have hB : Box (PFM R b dc L u ul 0 v 1 vc s ∧
      AtW R b L 0 0 u 0 u ul v 1 s q ql qc L' b' T) := ⟨⟨hpre, hW⟩⟩
  have hpc := hW.pc; have hsp := hW.sp; have h5 := hW.r5; have h14 := hW.r14; have hfs := hW.fs
  have hx15 := hW.x15; have hdf := hW.df
  have hr0' := hW.r0; have hr3 := hW.r3; have hr1 := hW.r1
  have e7 := hW.r7
  have h7 : (T.regs 7 = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at e7; exact hr0 (by rw [← e7]; rfl)
  have hTacc : T.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hW.mf.accessible]; exact hw
  have hacc := hW.mf.accessible
  have hgacc : T.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hacc]; exact hg2
  -- reads at `T.mem` outside `R.rt`, the window and `z`'s array are those of the entry
  have hkeep : ∀ a n, Outside a n R.rt → (a + n ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ a) →
      (0 < (0 : Nat) → a + n ≤ 0 ∨ 0 + 8 * 0 ≤ a) → T.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2 h3
    refine hW.mf.readLE a n ?_
    simp only [outside_append, win, outside_cons, outside_nil, and_true]
    exact ⟨⟨h1, by omega⟩, outside_ar h3⟩
  have hgS : T.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hkeep _ _ hgr (by omega) (fun hc => absurd hc (Nat.lt_irrefl 0))
  have htS : T.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [hkeep _ _ htr (by omega) (fun hc => absurd hc (Nat.lt_irrefl 0))]
    exact htg.g
  have hTt : T.mem.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hacc]; exact htg.readable
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 41512) (41512 + 112) := apart_of_data hd 1 (by decide) (by decide) hw
  have hWr : ∀ a n, wordT ≤ a → a + n ≤ wordT + 16 → T.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    unfold Apart at hwt
    exact hkeep a n (hty.of_sub h1 h2) (by omega) fun hc => absurd hc (Nat.lt_irrefl 0)
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, 1, 1] := hsv.1 _ _ _ (by omega)
  have hbl := blockSize_le_allocCost 8 true
  have hmc1 : makeCost 1 = allocCost 8 := by unfold makeCost makeCap; rfl
  have hbs : blockSize 8 true ≤ b' := by
    have h1 : makeCost ul + makeCost 1 ≤ b := by simp only [costMQ, costQ, DivLarge.costQ] at hcost; omega
    simp only [allocCost] at hbl hmc1; omega
  have hLs1 : ∀ r ∈ L', Outside r.1 (r.2 - r.1) (win s 41512 112) := by
    have hLs := hce.2.2.2.2.2.2.2.1
    obtain ⟨ns, rfl, hn, -⟩ := hext
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hLs r hr
    · have := FvModexp.Amd64.NatAdd.outside_of_inRanges hout (hn r hr).1
      simp only [win, outside_cons, outside_nil, and_true]; omega
  have m1 := hW.ra; have m2 := hW.bp; have m5 := hW.s5; have m7 := hW.s7
  have hinvT := hW.inv
  unfold Apart at hwt
  obtain ⟨hwa, hws, hwp⟩ := FvModexp.Amd64.wordT_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt hWr
  have hT1 : T.mem.readLE 7233184 8 = 8 := (hWr _ _ (by omega) (by omega)).trans hws
  have hT2 : T.mem.readLE 7233192 8 = 0 := (hWr _ _ (by omega) (by omega)).trans hwp
  have hTa : T.mem.accessible 7233184 16 false = true := (hacc _ _ _).trans hwa
  clear hpre hW hp hkeep hWr
  janus64_run [m1, m2, m5, m7, h7, hT1, hT2, hTa, hgS, htS] calls [hmk.pos]
  rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc' h8 _ _ _ _ hinv' _ _ _
  obtain ⟨hpre, hW⟩ := hB.h
  have hpW : MemFrame T.mem (((((T.mem.writeLE ((s.regs 4).toNat - 56) 8 q).writeLE ((s.regs 4).toNat - 48) 8
      ql).writeLE ((s.regs 4).toNat - 40) 8 qc).writeLE ((s.regs 4).toNat - 104) 8 (T.regs 7).toNat).writeLE
      ((s.regs 4).toNat - 240) 8 6217786) [((s.regs 4).toNat - 240, (s.regs 4).toNat - 32)] := by
    janus_frame
  have hf1 := hpW.trans hMF (rs'' := R.rt ++ win s 41512 112 ++ ar u 0) fun a n h => by
    simp only [outside_append, win, ar, outside_cons, outside_nil, and_true, Nat.lt_irrefl, if_false] at h ⊢
    exact ⟨by omega, h.1, by omega, by omega⟩
  have hpo := FvModexp.Amd64.NatAdd.outside_of_inRanges hout hIn
  have hx1 : LiveExt R L' (L' ++ [(ptr.toNat, ptr.toNat + 8)]) :=
    LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hlf1 : ∀ a n, InRanges a n L' → m.readLE a n = T.mem.readLE a n := by
    intro a n hin
    have := inL_out hce hext hin
    rw [hLF.readLE a n hin trivial]
    exact hpW.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, oneFinM (r := ptr.toNat) (rl := 1) (rc := 1) (b'' := b' - 8) hpre hW _ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?hM ?hLF hx1 ?hb ?hI ?hR⟩
  case hM =>
    refine hf1.trans (by janus_frame : MemFrame m _ [(ptr.toNat, ptr.toNat + 8),
      ((s.regs 4).toNat - 80, (s.regs 4).toNat - 56)]) fun a n h => ⟨h, ?_⟩
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢
    have := FvModexp.Amd64.NatAdd.outside_of_inRanges h.1.1 hIn
    exact ⟨by omega, by omega⟩
  case hLF =>
    refine ⟨fun a n hin _ => ?_⟩
    have h1 := inL_out hce hext hin
    obtain ⟨r, hr, i1, i2⟩ := hin
    have h2 := hAp r hr
    unfold Apart at h2
    rw [← hlf1 a n ⟨r, hr, i1, i2⟩]
    exact (by janus_frame : MemFrame m _ [(ptr.toNat, ptr.toNat + 8),
      ((s.regs 4).toNat - 80, (s.regs 4).toNat - 56)]).readLE a n
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  case hb =>
    have : makeCost 1 = 40 := by unfold makeCost makeCap allocCost; rfl
    omega
  case hI =>
    refine RtInv.inv_frame' (ws := [(ptr.toNat, ptr.toNat + 8), ((s.regs 4).toNat - 80, (s.regs 4).toNat - 56)])
      (by janus_frame) (fun r hr => ?_) hinv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; exact ⟨(ptr.toNat, ptr.toNat + 8), by simp, by simp only; omega, by simp only; omega⟩
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  case hR =>
    have hrd : Janus.Arm64.Memory.readLE ((((m.writeLE ptr.toNat 8 (T.regs 7).toNat).writeLE ((s.regs 4).toNat - 80) 8
        ptr.toNat).writeLE ((s.regs 4).toNat - 72) 8 1).writeLE ((s.regs 4).toNat - 64) 8 1) ptr.toNat 8 =
        (T.regs 7).toNat := by
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt (T.regs 7).isLt]
    refine ⟨?_, Or.inr ?_, Nat.le_refl _, by decide, ?_, Or.inr ⟨Nat.le_refl _, by simpa using hIn, ?_⟩⟩
    · show Janus.Arm64.Memory.readLE _ ptr.toNat (8 * 1) = _
      rw [Nat.mul_one, hrd]; exact e7
    · show Janus.Arm64.Memory.readLE _ (ptr.toNat + 8 * (1 - 1)) 8 ≠ 0
      rw [show ptr.toNat + 8 * (1 - 1) = ptr.toNat by omega, hrd]
      exact fun h => hr0 (by rw [← e7]; exact h)
    · intro _
      refine ⟨h8, Or.inl ⟨(ptr.toNat, ptr.toNat + 8), by simp, Nat.le_refl _, by simp only; omega⟩, ?_, by omega⟩
      simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hMF.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc'
    · intro r hr; exact hAp r (hext.mem_old hr)
  all_goals try (janus64_simp; done)
  all_goals first
    | exact hx0.symm
    | exact hfs
    | (rw [hdf0]; rfl)
    | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact ofNat_modL _)
    | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq])
   

end FvModexp.Amd64.Q.NatDiv
