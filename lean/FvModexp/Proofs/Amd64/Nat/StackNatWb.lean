import FvModexp.Proofs.Amd64.Nat.StackNatTail

/-!
# `(*stack).nat` (amd64): the join `+0xdd` → the header's `len`/`cap` stores, the write-barrier flag test and (flag on)
`gcWriteBarrier2` with its buffer stores `(new ptr, old ptr)` → `+0x101`, then `tail`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.StackNat

/-- a store-only frame is a live frame -/
theorem lf_of_mf {m m' : Janus.Arm64.Memory} {L ws : List (Nat × Nat)} (h : MemFrame m m' ws) : LiveFrame m m' L ws :=
  ⟨fun a n _ ho => h.readLE a n ho⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem joinW (impl : List Amd64.Segment) (R : RtInv)
    (hwb : WbLiveContract64 (LibStackNat.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (M : Janus.Arm64.Memory) (h : J R b L st.toNat n.toNat s L1 b1 w1 c1 M)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 pJ) (hsp : S.regs 4 = s.regs 4 - 88#64) (h0 : S.regs 0 = st)
    (h3 : S.regs 3 = n) (h1 : S.regs 1 = BitVec.ofNat 64 c1)
    (h7 : S.regs 7 = BitVec.ofNat 64 (rnd n.toNat)) (h8 : S.regs 8 = BitVec.ofNat 64 w1)
    (h2 : S.regs 2 = BitVec.ofNat 64 (stLen s.mem st.toNat)) (h14 : S.regs 14 = s.regs 14)
    (h5 : S.regs 5 = s.regs 4 - 8#64) (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false)
    (hm : S.mem = M) :
    ReachesRet (LibStackNat.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostL R b L 4192 24 st.toNat n.toNat s s' := by
  have hpre := h.pre
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, hwbf, hwbA, hfa⟩ := hpre
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hcb⟩ := hok
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hc1len := h.c1len
  have hc1b := h.c1b
  have hw64 := h.w64
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hsp88 : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hstaccM : M.accessible st.toNat 24 true = true := by rw [h.mf.accessible]; exact hstacc
  have hacc16 : M.accessible (st.toNat + 8) 16 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hstaccM (by omega) (by omega)
  have hacc8 : M.accessible st.toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hstaccM (by omega) (by omega))
  have hwbM : M.accessible wbA 4 false = true := by rw [h.mf.accessible]; exact hwbf
  have hsaccM : M.accessible ((s.regs 4).toNat - 4192) (4192 + 24) true = true := by rw [h.mf.accessible]; exact hw
  have hwbv : wbA = 12283968 := rfl
  rw [hwbv] at hwbA hwbM
  unfold Apart at hwbA
  have hnr : rnd n.toNat ≤ n.toNat + 3 := by simp only [rnd]; omega
  have hsth1 := h.ext.held hsth
  have hra := h.ra
  have hbp := h.bp
  have hra47 := h.ra47
  have e6 : BitVec.ofNat 64 (stLen s.mem st.toNat) + BitVec.ofNat 64 (rnd n.toNat) =
      BitVec.ofNat 64 (stLen s.mem st.toNat + rnd n.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hinvW : ∀ v1 v2 (ws : List (Nat × Nat)) (m' : Janus.Arm64.Memory),
      MemFrame ((M.writeLE (st.toNat + 8) 8 v1).writeLE (st.toNat + 16) 8 v2) m' ws →
      (∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt) →
      R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 m') := fun v1 v2 ws m' hws hwo =>
    RtInv.inv_frame' hws (fun r hr => Or.inl (hwo r hr)) (RtInv.inv_frame' (ws := [(st.toNat, st.toNat + 24)])
      (by janus_frame)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [show st.toNat + 24 - st.toNat = 24 by omega]; exact hsth1.symm) h.inv)
  janus64_run [hm, hsp88, hacc16, hacc8, hwbM, e6] until [cA "runtime.gcWriteBarrier2", pS]
  · -- the barrier is off
    refine tail impl R b L st n s L1 b1 w1 c1 M _ h ?_ ?_ (hinvW _ _ [] _ (MemFrame.refl _ _) (by simp)) ?_ ?_ _
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    · janus_frame
    · exact lf_of_mf (by janus_frame)
    · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt (by omega)]
    · rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    all_goals first | exact hfs | exact hdf | janus64_simp
  · -- the barrier is on
    have hwb2 := hsv.2.2.2.2.2.1 [2]
    have hLW : LiveSep L1 [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96 + 8)] := fun r hr => by
      have := h.lsep r hr
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
    have hWR : LiveSep [((s.regs 4).toNat - 96 - 4096, (s.regs 4).toNat - 96 + 8)] R.rt := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hout.of_sub (by omega) (by simp; omega)
    have hsp96 : (s.regs 4 - 88#64 - 8#64).toNat = (s.regs 4).toNat - 96 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat, hsp88]; omega), hsp88]; rfl
    have hwacc : M.accessible ((s.regs 4).toNat - 4192) (4096 + 8) true = true :=
      Janus.Arm64.Memory.accessible_mono _ hsaccM (by omega) (by omega)
    have hsp96' : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    refine ReachesRet.call (hwb L1 b1) rfl ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hwb2, ?_, ?_, ?_⟩ ?_
    all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96', h14]
    · rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
    · omega
    · omega
    · omega
    · simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_mono _ hsaccM (by omega) (by omega)
    · exact hinvW _ _ [((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)] _ (by janus_frame) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hout.of_sub (by simp only; omega) (by simp only; omega))
    · exact hLW
    · exact hWR
    intro S2 hpc2 ⟨buf, f2, x2, yh2, m', zh2, kr2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩
    subst hs2
    try dsimp only at hfr2 hlf2 hapW hinvS hsl hapL
    try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96', h14] at hfr2 hapW hinvS
    obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := hsl
    have hbufR : InRanges buf.toNat 16 R.rt := by simpa using hsl1
    have hacc16b : m'.accessible buf.toNat 16 true = true := by simpa using hsl3
    have hb8a : m'.accessible buf.toNat 8 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc16b (Nat.le_refl _) (by omega)
    have hb8b : m'.accessible (buf.toNat + 8) 8 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc16b (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    have hstb : st.toNat + 24 ≤ buf.toNat ∨ buf.toNat + 16 ≤ st.toNat := by
      rcases hsth1 with hL | hO
      · have := hapL.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hkeep : ∀ a k, st.toNat ≤ a → a + k ≤ st.toNat + 24 →
        m'.readLE a k = (((M.writeLE (st.toNat + 8) 8 (stLen s.mem st.toNat)).writeLE (st.toNat + 16) 8 c1).writeLE ((s.regs 4).toNat - 96) 8 6186362).readLE a k := by
      intro a k h1 h2
      rcases hsth1 with hL | hO
      · exact hlf2.readLE a k (hL.sub h1 h2) trivial
      · refine hfr2.readLE a k ?_
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hO.of_sub h1 h2, by omega⟩
    have hF1 : MemFrame M (((M.writeLE (st.toNat + 8) 8 (stLen s.mem st.toNat)).writeLE (st.toNat + 16) 8 c1).writeLE ((s.regs 4).toNat - 96) 8 6186362) [(st.toNat, st.toNat + 24), ((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)] := by
      janus_frame
    janus64_run [hb8a, hb8b, hbuf64] until [pS]
    have hbs : MemFrame m' ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8)) [(buf.toNat, buf.toNat + 16)] := by janus_frame
    have hF2 : MemFrame M ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8)) (R.rt ++ [(st.toNat, st.toNat + 24), ((s.regs 4).toNat - 4192, (s.regs 4).toNat - 88)]) := by
      refine MemFrame.trans (rs := R.rt ++ [(st.toNat, st.toNat + 24), ((s.regs 4).toNat - 4192, (s.regs 4).toNat - 88)])
        (MemFrame.trans (rs'' := R.rt ++ [(st.toNat, st.toNat + 24), ((s.regs 4).toNat - 4192, (s.regs 4).toNat - 88)])
          hF1 hfr2 (fun a k ho => ?_)) hbs (fun a k ho => ?_)
      · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨⟨ho.2.1, by omega⟩, ho.1, by omega⟩
      · refine ⟨ho, ?_⟩
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        have := hbufR.apart ho.1; unfold Apart at this; omega
    have hLF2 : LiveFrame M ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8)) L1 [(st.toNat, st.toNat + 24)] := by
      refine ⟨fun a k hin hout => ?_⟩
      rw [hbs.readLE a k ?_, hlf2.readLE a k hin trivial, hF1.readLE a k ?_]
      · obtain ⟨r, hr, h1, h2⟩ := hin
        have h3 := h.lsep r hr
        simp only [win, outside_cons, outside_nil, and_true] at h3 hout ⊢
        exact ⟨hout, by omega⟩
      · simp only [outside_cons, outside_nil, and_true]
        have := hapL.apart_of_inRanges hin; omega
    have hinv2 : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8))) := by
      have hv1 : view R.rt L1 ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8)) =
          ((view R.rt L1 m').writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8) := by
        rw [view_writeLE_vis (hbufR.sub (by omega) (by omega)) (Outside.of_sub hapL.outside (by omega) (by omega)),
          view_writeLE_vis (hbufR.sub (Nat.le_refl _) (by omega)) (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))]
      rw [hv1]
      exact hinvS _ (by janus_frame)
    have hl2 : (((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8))).readLE (st.toNat + 8) 8 = stLen s.mem st.toNat := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hkeep _ _ (by omega) (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    have hc2 : (((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st.toNat 8))).readLE (st.toNat + 16) 8 = c1 := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hkeep _ _ (by omega) (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    refine tail impl R b L st n s L1 b1 w1 c1 M _ h hF2 hLF2 hinv2 hl2 hc2 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
    all_goals first | exact hfs | exact hdf | janus64_simp

end FvModexp.Amd64.StackNat
