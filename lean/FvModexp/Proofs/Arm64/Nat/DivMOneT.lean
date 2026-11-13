import FvModexp.Proofs.Arm64.Nat.DivMOneA
import FvModexp.Proofs.Arm64.Nat.DivMDefs
import FvModexp.Proofs.Arm64.Nat.DivOneT

set_option autoImplicit false

/-!
# `nat.div` (arm64), `z = nil`, `z2 = u`, `len v = 1`: `r = u.setWord(r2)`, return

`oneAM`/`oneBM`/`oneCM` = `oneA`/`oneB`/`oneC` (DivOneT) with `z2 = u` (the remainder's word is written into the
dividend's array after `divW` read it), concluding `RQM` via `oneFinM` (no quotient fact: `(*Int).Mod` ignores it).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the postcondition of the `len v = 1` paths** (`z = nil`, `z2 = u`): the quotient is unconstrained -/
theorem oneFinM {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v : Nat} {s : State}
    (hpre : PFM R b dc L u ul uc v 1 s) {q ql qc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {T : State} (hW : AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T) (s' : State) {r rl rc : Nat}
    {L'' : List (Nat × Nat)} {b'' : Nat}
    (h0 : s'.regs 0 = BitVec.ofNat 64 q) (h1 : s'.regs 1 = BitVec.ofNat 64 ql) (h2 : s'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : s'.regs 3 = BitVec.ofNat 64 r) (h4 : s'.regs 4 = BitVec.ofNat 64 rl) (h5 : s'.regs 5 = BitVec.ofNat 64 rc)
    (hM : MemFrame T.mem s'.mem (R.rt ++ winA s 41504 112 ++ ar u uc)) (hLF2 : LiveFrame T.mem s'.mem L' (ar u uc))
    (hext2 : LiveExt R L' L'') (hb2 : b' - makeCost 1 ≤ b'')
    (hinv : R.inv b'' L'' (s.regs 28).toNat (view R.rt L'' s'.mem))
    (hr : ExpHyp.NatOF R L L'' s'.mem u uc 1 r rl rc (natVal s.mem u ul % natVal s.mem v 1)) :
    PostM R b dc L u ul uc v 1 s s' := by
  have hc := hpre.cost
  have hbW := hW.bud
  have e0 : ar 0 0 = [] := rfl
  refine ⟨q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L'', b'', hr, ⟨hW.ext.trans hext2, ?_, hinv⟩,
    hW.mf.trans hM fun a n h => ⟨?_, ?_⟩, ⟨fun a n hin ho => ?_⟩⟩
  · simp only [costM, cost] at hc ⊢; omega
  · rw [e0]; simp only [outside_append, outside_nil, and_true] at h ⊢; exact h.1
  · simp only [outside_append] at h ⊢; exact ⟨h.1, outside_ar_of h.2⟩
  · have ho' : Outside a n (ar u uc) := outside_ar_of ho
    rw [hLF2.readLE a n (hW.ext.inRanges_old hin) ho']
    exact hW.lf.readLE a n hin (by rw [e0]; trivial)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- `r2 = 0`: `r = u[:0]` -/
theorem oneAM (impl : List Segment) (R : RtInv) {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v : Nat} {s : State}
    (hpre : PFM R b dc L u ul uc v 1 s) {q ql qc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {T : State} (hW : AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T)
    (hr0 : natVal s.mem u ul % natVal s.mem v 1 = 0)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) T (RQM R b dc L u ul uc v 1 s) := by
  have hp := hpre
  have hce := hp.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hp.ce
  have hz2 := hp.uo
  have hext := hW.ext
  have hB : Box (PFM R b dc L u ul uc v 1 s ∧ AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T) :=
    ⟨⟨hpre, hW⟩⟩
  have hpc := hW.pc; have hsp := hW.sp; have h28 := hW.r28; have h29 := hW.r29; have h18 := hW.r18
  have hr0' := hW.r0; have hr1 := hW.r1; have hr2 := hW.r2
  have h3 : T.regs 3 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hW.r3, hr0]; rfl)
  have hTacc : T.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hW.mf.accessible]; exact hw
  have m1 := hW.lr; have m2 := hW.fp; have m5 := hW.s5; have m7 := hW.s7
  have hinvT := hW.inv
  have hacc := hW.mf.accessible
  clear hpre hW hp
  janus_run [m1, m2, m5, m7, h3]
  obtain ⟨hpre, hW⟩ := hB.h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, oneFinM (r := u) (rl := 0) (rc := uc) hpre hW _ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hLF (LiveExt.refl R L') (Nat.sub_le _ _) ?hI ?hR⟩
  case hM => exact (winFrame hce hext (by janus_frame) (lo := s.sp.toNat - 80) (hi := s.sp.toNat - 32) (by omega) (by omega) u uc).1
  case hLF => exact (winFrame hce hext (by janus_frame) (lo := s.sp.toNat - 80) (hi := s.sp.toNat - 32) (by omega) (by omega) u uc).2
  case hI =>
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 80, s.sp.toNat - 32)]) (by janus_frame) (fun r hr => ?_) hinvT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  case hR =>
    refine ⟨by simp [natVal, hr0], Or.inl rfl, Nat.zero_le _, hz2.1, natLive_ext hz2.2.1 ?_ hext, Or.inl ⟨rfl, rfl⟩⟩
    intro a n w; simp only [Memory.accessible_writeLE]; rw [hacc]
  all_goals janus_simp
  all_goals exact ofNat_modL _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- `r2 ≠ 0`, `cap u ≠ 0`: `u[0] = r2`, `r = u[:1]` -/
theorem oneBM (impl : List Segment) (R : RtInv) {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v : Nat} {s : State}
    (hpre : PFM R b dc L u ul uc v 1 s) {q ql qc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {T : State} (hW : AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T)
    (hr0 : natVal s.mem u ul % natVal s.mem v 1 ≠ 0) (hc0 : 0 < uc)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) T (RQM R b dc L u ul uc v 1 s) := by
  have hp := hpre
  have hce := hp.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hp.ce
  have hz2 := hp.uo
  obtain ⟨hz8, hz2h, hz2acc, hz248⟩ := hz2.2.1 hc0
  have hz2w := (hz2.2.2 hc0).1
  simp only [win, outside_cons, outside_nil, and_true] at hz2w
  have hz40 := hz2.1
  have hext := hW.ext
  have hB : Box (PFM R b dc L u ul uc v 1 s ∧ AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T) :=
    ⟨⟨hpre, hW⟩⟩
  have hpc := hW.pc; have hsp := hW.sp; have h28 := hW.r28; have h29 := hW.r29; have h18 := hW.r18
  have hr0' := hW.r0; have hr1 := hW.r1; have hr2 := hW.r2
  have e3 := hW.r3
  have h3 : (T.regs 3 = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at e3; exact hr0 (by rw [← e3]; rfl)
  have hTacc : T.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hW.mf.accessible]; exact hw
  have hacc := hW.mf.accessible
  have hzacc : T.mem.accessible u 8 true = true := by
    rw [hacc]; exact Memory.accessible_mono _ hz2acc (Nat.le_refl _) (by omega)
  have m1 := hW.lr; have m2 := hW.fp; have m5 := hW.s5; have m7 := hW.s7
  have hinvT := hW.inv
  clear hpre hW hp
  janus_run [m1, m2, m5, m7, h3]
  obtain ⟨hpre, hW⟩ := hB.h
  refine ⟨⟨?_, ?_, ?_, ?_⟩, oneFinM (r := u) (rl := 1) (rc := uc) hpre hW _ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hLF
    (LiveExt.refl R L') (Nat.sub_le _ _) ?hI ?hR⟩
  case hM => exact (winFrame2 hce hext (by janus_frame) (lo := s.sp.toNat - 80) (hi := s.sp.toNat - 32) (by omega)
    (by omega) hc0).1
  case hLF => exact (winFrame2 hce hext (by janus_frame) (lo := s.sp.toNat - 80) (hi := s.sp.toNat - 32) (by omega)
    (by omega) hc0).2
  case hI =>
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 80, s.sp.toNat - 32), (u, u + 8)]) (by janus_frame)
      (fun r hr => ?_) hinvT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
    · rcases hz2h.sub (a := u) (n := 8) (Nat.le_refl _) (by omega) with h | h
      · right; simpa using hext.inRanges_old h
      · left; simpa using h
  case hR =>
    have hrd : natVal ((((((((T.mem.writeLE (s.sp.toNat - 56) 8 q).writeLE (s.sp.toNat - 48) 8 ql).writeLE
        (s.sp.toNat - 40) 8 qc).writeLE u 8 (T.regs 3).toNat).writeLE (s.sp.toNat - 80) 8 u).writeLE
        (s.sp.toNat - 72) 8 1).writeLE (s.sp.toNat - 64) 8 uc)) u 1 = (T.regs 3).toNat := by
      show Memory.readLE _ u (8 * 1) = _
      simp (disch := omega) only [Nat.mul_one, Memory.readLE_writeLE_of_disjoint,
        FvModexp.Expmc.readLE_writeLE_same]
      have := (T.regs 3).isLt; omega
    refine ⟨?_, Or.inr ?_, by omega, hz40, natLive_ext hz2.2.1 ?_ hext, Or.inl ⟨rfl, rfl⟩⟩
    · first | (rw [hrd]; exact e3) | skip
    · first | (show Memory.readLE _ (u + 8 * (1 - 1)) 8 ≠ 0; simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero];
                exact fun h => hr0 (by rw [← e3, ← hrd]; exact h)) | skip
    · intro a n w; simp only [Memory.accessible_writeLE]; rw [hacc]
  all_goals janus_simp
  all_goals exact ofNat_modL _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `r2 ≠ 0`, `cap u = 0`: `make(nat, 1)` = `makeslice(Word, 1, 1)`, `r = [r2]` -/
theorem oneCM (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibDiv.program.link impl) (cA "runtime.makeslice") 4096 R)
    {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul v : Nat} {s : State}
    (hpre : PFM R b dc L u ul 0 v 1 s) {q ql qc : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {T : State} (hW : AtW R b L 0 0 u 0 u ul v 1 s q ql qc L' b' T)
    (hr0 : natVal s.mem u ul % natVal s.mem v 1 ≠ 0)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) T (RQM R b dc L u ul 0 v 1 s) := by
  have hp := hpre
  have hce := hp.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, -, hro⟩ := hp.ce
  unfold Apart at hga
  have hsv := hp.sv
  have hcost := hp.cost
  have hext := hW.ext
  have hbud := hW.bud
  have hB : Box (PFM R b dc L u ul 0 v 1 s ∧ AtW R b L 0 0 u 0 u ul v 1 s q ql qc L' b' T) :=
    ⟨⟨hpre, hW⟩⟩
  have hpc := hW.pc; have hsp := hW.sp; have h28 := hW.r28; have h29 := hW.r29; have h18 := hW.r18
  have hr0' := hW.r0; have hr1 := hW.r1; have hr2 := hW.r2
  have e3 := hW.r3
  have h3 : (T.regs 3 = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at e3; exact hr0 (by rw [← e3]; rfl)
  have hTacc : T.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by rw [hW.mf.accessible]; exact hw
  have hacc := hW.mf.accessible
  have hgacc : T.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hacc]; exact hg2
  -- reads at `T.mem` outside `R.rt`, the window and `z`'s array are those of the entry
  have hkeep : ∀ a n, Outside a n R.rt → (a + n ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ a) →
      T.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    refine hW.mf.readLE a n ?_
    simp only [outside_append, winA, outside_cons, outside_nil, and_true]
    exact ⟨⟨h1, by omega, by omega⟩, outside_ar fun h => absurd h (by decide)⟩
  have hgS : T.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hkeep _ _ hgr (by omega)
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 (s.sp.toNat - 41504) (41504 + 112) := apart_of_data hd 1 (by decide) (by decide) hw
  have hWr : ∀ a n, wordT ≤ a → a + n ≤ wordT + 16 → T.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    unfold Apart at hwt
    exact hkeep a n (hty.of_sub h1 h2) (by omega)
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, 1, 1] := hsv.1 _ _ _ (by omega)
  have hbl := blockSize_le_allocCost 8 true
  have hmc1 : makeCost 1 = allocCost 8 := by unfold makeCost makeCap; rfl
  have hbs : blockSize 8 true ≤ b' := by
    have h1 : makeCost ul + makeCost 1 ≤ b := by simp only [costM, cost] at hcost; omega
    simp only [allocCost] at hbl hmc1; omega
  have hLs1 := lsepL hce hext
  have m1 := hW.lr; have m2 := hW.fp; have m5 := hW.s5; have m7 := hW.s7
  have hinvT := hW.inv
  unfold Apart at hwt
  janus_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt hWr
  have hT1 : T.mem.readLE 2641088 8 = s.mem.readLE 2641088 8 := hWr _ _ (by omega) (by omega)
  have hT2 : T.mem.readLE 2641096 8 = s.mem.readLE 2641096 8 := hWr _ _ (by omega) (by omega)
  have hTa : T.mem.accessible 2641088 16 false = s.mem.accessible 2641088 16 false := hacc _ _ _
  clear hpre hW hp hkeep hWr
  janus_run [m1, m2, m5, m7, h3, hT1, hT2, hTa, hgS] calls [hmk.pos]
  rename_i ptr _ _ _ m _ _ hLF hMF hAp hIn hle hacc' h8 _ _ _ hrb hinv' hapw _ _
  obtain ⟨hpre, hW⟩ := hB.h
  have hpW : MemFrame T.mem ((((T.mem.writeLE (s.sp.toNat - 56) 8 q).writeLE (s.sp.toNat - 48) 8 ql).writeLE
      (s.sp.toNat - 40) 8 qc).writeLE (s.sp.toNat - 96) 8 (T.regs 3).toNat) [(s.sp.toNat - 96, s.sp.toNat - 32)] := by
    janus_frame
  have hf1 := hpW.trans hMF (rs'' := R.rt ++ winA s 41504 112 ++ ar u 0) fun a n h => by
    simp only [outside_append, winA, ar, outside_cons, outside_nil, and_true, Nat.lt_irrefl, if_false] at h ⊢
    exact ⟨by omega, h.1, by omega, by omega⟩
  have hpo := FvModexp.Arm64.NatAdd.outside_of_inRanges hout hIn
  have hx1 : LiveExt R L' (L' ++ [(ptr.toNat, ptr.toNat + 8)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hlf1 : ∀ a n, InRanges a n L' → m.readLE a n = T.mem.readLE a n := by
    intro a n hin
    have := inL_out hce hext hin
    rw [hLF.readLE a n hin trivial]
    exact hpW.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, oneFinM (r := ptr.toNat) (rl := 1) (rc := 1) (b'' := b' - 8) hpre hW _ ?_ ?_ ?_ ?_ ?_ ?_ ?hM ?hLF hx1 ?hb
    ?hI ?hR⟩
  case hM =>
    refine hf1.trans (by janus_frame : MemFrame m _ [(ptr.toNat, ptr.toNat + 8), (s.sp.toNat - 80, s.sp.toNat - 56)])
      fun a n h => ⟨h, ?_⟩
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
    have := FvModexp.Arm64.NatAdd.outside_of_inRanges h.1.1 hIn
    exact ⟨by omega, by omega⟩
  case hLF =>
    refine ⟨fun a n hin _ => ?_⟩
    have h1 := inL_out hce hext hin
    obtain ⟨r, hr, i1, i2⟩ := hin
    have h2 := hAp r hr
    unfold Apart at h2
    rw [← hlf1 a n ⟨r, hr, i1, i2⟩]
    exact (by janus_frame : MemFrame m _ [(ptr.toNat, ptr.toNat + 8), (s.sp.toNat - 80, s.sp.toNat - 56)]).readLE a n
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  case hb =>
    have : makeCost 1 = 40 := by unfold makeCost makeCap allocCost; rfl
    omega
  case hI =>
    refine RtInv.inv_frame' (ws := [(ptr.toNat, ptr.toNat + 8), (s.sp.toNat - 80, s.sp.toNat - 56)]) (by janus_frame)
      (fun r hr => ?_) hinv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; exact ⟨(ptr.toNat, ptr.toNat + 8), by simp, by simp only; omega, by simp only; omega⟩
    · left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  case hR =>
    have hrd : Memory.readLE ((((m.writeLE ptr.toNat 8 (T.regs 3).toNat).writeLE (s.sp.toNat - 80) 8 ptr.toNat).writeLE
        (s.sp.toNat - 72) 8 1).writeLE (s.sp.toNat - 64) 8 1) ptr.toNat 8 = (T.regs 3).toNat := by
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same]
      have := (T.regs 3).isLt; omega
    refine ⟨?_, Or.inr ?_, Nat.le_refl _, by decide, ?_, Or.inr ⟨Nat.le_refl _, by simpa using hIn, ?_⟩⟩
    · show Memory.readLE _ ptr.toNat (8 * 1) = _
      rw [Nat.mul_one, hrd]; exact e3
    · show Memory.readLE _ (ptr.toNat + 8 * (1 - 1)) 8 ≠ 0
      rw [show ptr.toNat + 8 * (1 - 1) = ptr.toNat by omega, hrd]
      exact fun h => hr0 (by rw [← e3]; exact h)
    · intro _
      refine ⟨h8, Or.inl ⟨(ptr.toNat, ptr.toNat + 8), by simp, Nat.le_refl _, by simp only; omega⟩, ?_, by omega⟩
      simp only [Memory.accessible_writeLE]; rw [hMF.accessible]; simp only [Memory.accessible_writeLE]; exact hacc'
    · intro r hr; exact hAp r (hext.mem_old hr)
  all_goals janus_simp
  all_goals exact ofNat_modL _

end FvModexp.Arm64.NatDiv
