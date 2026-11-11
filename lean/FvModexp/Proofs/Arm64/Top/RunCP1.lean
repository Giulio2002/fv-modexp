import FvModexp.Proofs.Arm64.Top.RunCPDefs

/-! # `Run` (arm64): `V` to the return (`len(v) ≥ modLen`) or to `P` (`makeslice` of the `LeftPadBytes` buffer) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem cp1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (b : Nat) (L : List (Nat × Nat)) (p len : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (W : Nat) (hW : 4800 ≤ W)
    (henv : CallEnv R L s W 40) (Q : Outcome → Prop) (hbB : okB s p len ≤ b)
    (V : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelV R b L p len s ret W L1 b1 V)
    (hpc : V.pc = BitVec.ofNat 64 pcCV)
    (hOk : ∀ S' : State, ABIReturn s S' → OkRet S' (resV s p len) (hdrV s p len 2) →
      OkFrame R b (okB s p len) L W s S' (S'.regs 0).toNat (hdrV s p len 2) → Q (.returned S'))
    (hk : ∀ (U : State) (Lk : List (Nat × Nat)) (bk vp vn buf : Nat), JoinP R b L p len s ret W Lk bk vp vn buf U →
      U.pc = BitVec.ofNat 64 pcP → Reaches ((LibRun.program.link impl).withExit ret) U Q) :
    Reaches ((LibRun.program.link impl).withExit ret) V Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hs3, hl2, hdS, hvn, hvv, hvl, hext, hbud, hinv, hLsS, hMF, hLF⟩ := hrel
  generalize hvpd : (V.regs 0).toNat = vp at hvv hvl
  generalize hvnd : (V.regs 1).toNat = vn at hvn hvv hvl
  have hr1 : V.regs 1 = BitVec.ofNat 64 vn := by rw [← hvnd, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hr0 : V.regs 0 = BitVec.ofNat 64 vp := by rw [← hvpd, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hI1 := toInt_small (BitVec.ofNat 64 vn) (by simp; omega)
  have hI5 := toInt_small (BitVec.ofNat 64 (hdrV s p len 2)) (by simp; omega)
  have hn1 : (BitVec.ofNat 64 vn).toNat = vn := by simp; omega
  have hn5 : (BitVec.ofNat 64 (hdrV s p len 2)).toNat = hdrV s p len 2 := by simp; omega
  by_cases hge : hdrV s p len 2 ≤ vn
  · -- `len(v) ≥ modLen`: return `v`
    have heq : vn = hdrV s p len 2 := by omega
    janus_run [hm1, hm2, hs3, hr0, hr1, hI1, hI5, hn1, hn5]
    refine hOk _ ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29, hm2, regFP],
      by janus_simp [h18, regPlatform]⟩ ⟨by janus_simp, by janus_simp; omega, ?v⟩
      ⟨L1, b1, hext, bud_nopad hbud, ?inv, ?held, ?mf, ?lf⟩
    case v => janus_simp; rw [← heq]; exact hvv
    case inv => dsimp only; exact hinv
    case held => janus_simp; intro h; rw [← heq]; exact Or.inl (hvl (by omega)).1
    case mf => dsimp only; exact hMF
    case lf => dsimp only; exact hLF
  · -- `len(v) < modLen`: `makeslice(uint8, modLen, modLen)`
    have hlt : vn < hdrV s p len 2 := by omega
    have hgS : V.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
      hMF.readLE _ _ (by
        simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
        unfold Apart at hga; exact ⟨hgr, by omega⟩)
    unfold Apart at hga
    have hwS : V.mem.accessible (s.sp.toNat - W) (W + 40) true = true := by rw [hMF.accessible]; exact hw
    have hmk' : MakesliceLiveContract (LibRun.program.link impl) (cA "runtime.makeslice") 4096 R :=
      MakesliceLiveContract.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmk
    have hmkP := hmk'.pos L1 b1
    janus_eval_nat h_u : uint8T
    have hokb : R.ok (cA "runtime.makeslice") [uint8T, hdrV s p len 2, hdrV s p len 2] := hokB _ hl2
    rw [h_u] at hokb
    have hU1 : s.mem.accessible 2639168 16 false = true := by
      janus_data hd; exact Memory.accessible_mono _ h_data0 (by omega) (by omega)
    have hU2 : V.mem.readLE 2639168 8 = 1 := by
      janus_data hdS; rw [h_rodata _ _ (by decide)]; decide
    have hU3 : V.mem.readLE 2639176 8 = 0 := by
      janus_data hdS; rw [h_rodata _ _ (by decide)]; decide
    have hut : Apart 2639168 16 (s.sp.toNat - W) (W + 40) :=
      apart_of_data (x := 2639168) (l := 16) hdS 0 (by decide) (by decide) hwS
    unfold Apart at hut
    have ⟨hBS, hbudk⟩ := bud_pad (n := hdrV s p len 2) hl2 hbB hbud
    have hLSc : ∀ r ∈ L1, (r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 624 - 4096 ∨ s.sp.toNat - 624 - 8 ≤ r.fst) ∧
        (r.fst + (r.snd - r.fst) ≤ s.sp.toNat - 624 + 8 ∨ s.sp.toNat - 624 + 8 + 24 ≤ r.fst) := by
      intro r hr; have := hLsS r hr
      simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this; omega
    have hvW : 0 < vn → vp + vn ≤ s.sp.toNat - W ∨ s.sp.toNat + 40 ≤ vp := fun h => by
      have := InRanges.apart (hvl h).2.1 hout; unfold Apart at this; omega
    set_option janus.callRegions true in
    janus_run [hm1, hm2, hs3, hr0, hr1, hI1, hI5, hn1, hn5, hU2, hU3, hgS] until [pcP] calls [hmkP]
    rename_i ptr _ _ _ mk _ _ hLFk hMFk hapk hink hbk hack h8k h16k hzk hrk hapSk hinvk
    have hdk := dataLoaded_win (lo := s.sp.toNat - W) (n := W + 40) ?d0 (by rw [hrg1]; simp) hro hMFk ?wacc ?ws
    case d0 => janus_callpre
    case wacc => simpa only [Memory.accessible_writeLE] using hwS
    case ws =>
      intro r hr
      simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
    have hLFS : LiveFrame V.mem mk L1 [] :=
      (LiveFrame.of_win (by simp only [win]; janus_frame) hLsS).trans hLFk (fun _ _ h => h)
    have hext' : LiveExt R L1 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) :=
      LiveExt.single (by simpa using hink) (by simpa using hapk)
    have hMF2 : MemFrame s.mem mk (R.rt ++ win s W 40) :=
      (hMF.trans ?w1 fun a n h => ⟨h, outW_w h⟩).trans hMFk fun a n h => ⟨h, outW_cs hW h⟩
    case w1 => simp only [win]; janus_frame
    refine hk _ (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) (b1 - blockSize (hdrV s p len 2) true)
      vp vn ptr.toNat ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29], by janus_simp [h18],
        by janus_simp [hm1], by janus_simp [hm2], by janus_simp [hs3], hl2, by janus_simp, by janus_simp, hlt,
        by janus_simp, by omega, Memory.accessible_mono _ hack (Nat.le_refl _) (by omega),
        fun j hj => by janus_simp; rw [hzk j hj]; rfl,
        ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩,
        hink.sub (Nat.le_refl _) (by omega), ?sepL, ?val, ?vfacts, hdk, hext.trans hext', hbudk, hinvk, ?sepW,
        hMF2, hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)⟩ (by janus_simp)
    case sepL =>
      intro r hr
      have := hapk r (hext.mem_old hr); unfold Apart at this
      simp only [Janus.outside_cons, Janus.outside_nil, and_true]; omega
    case val =>
      janus_simp
      rcases Nat.eq_zero_or_pos vn with h0 | h0
      · rw [h0] at hvv ⊢; exact hvv
      · rw [beVal_liveFrame hLFS (hvl h0).1 (by simp [Outside]), hvv]
    case vfacts =>
      intro h0
      obtain ⟨hi, -, hac, h48⟩ := hvl h0
      refine ⟨h48, Memory.accessible_read_of_write _ (by rw [← hMF.accessible]; exact hac), ?_⟩
      have := (hapk.apart_of_inRanges hi).symm
      have hw' := hvW h0
      unfold Apart at this ⊢; exact ⟨by omega, hw'⟩
    case sepW =>
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hLsS r hr
      · simp only [List.mem_singleton] at hr; subst hr
        have := InRanges.apart hink hout; unfold Apart at this
        simp only [win, Janus.outside_cons, Janus.outside_nil, and_true]; omega

end FvModexp.Arm64.Run
