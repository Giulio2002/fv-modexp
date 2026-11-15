import FvModexp.Proofs.Amd64.Top.RunCPDefs
import FvModexp.Proofs.Amd64.Top.RunU8

/-! # `Run` (amd64): `V` to the return (`len(v) ≥ modLen`) or to `P` (`makeslice` of the `LeftPadBytes` buffer)

`V` = `fn + 0xbc5`: `DX = modLen`; `CMPQ BX, DX; JGE` → return `v = (AX, BX, CX)` with a nil error (`DI = SI = 0`);
else spill `v`'s pointer / length, `makeslice(uint8, modLen, modLen)` (call `fn + 0xbf0`), return to `P`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem cp1 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (b : Nat) (L : List (Nat × Nat)) (p len : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (W : Nat) (hW : 4800 ≤ W)
    (henv : CallEnv R L s W 40) (Q : Janus.Amd64.Outcome → Prop) (hbB : okB s p len ≤ b)
    (V : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelV R b L p len s ret W L1 b1 V)
    (hpc : V.rip = BitVec.ofNat 64 pcCV)
    (hOk : ∀ S' : State, ABIReturn s S' → OkRet S' (resV s p len) (hdrV s p len 2) →
      OkFrame R b (okB s p len) L W s S' (S'.regs 0).toNat (hdrV s p len 2) → Q (.returned S'))
    (hk : ∀ (U : State) (Lk : List (Nat × Nat)) (bk vp vn buf : Nat), JoinP R b L p len s ret W Lk bk vp vn buf U →
      U.rip = BitVec.ofNat 64 pcP → Reaches ((LibRun.program.link impl).withExit ret) U Q) :
    Reaches ((LibRun.program.link impl).withExit ret) V Q := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hs3, hl2, hdS, hvn, hvv, hvl, hext, hbud, hinv, hLsS, hMF, hLF⟩ := hrel
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  generalize hvpd : (V.regs 0).toNat = vp at hvv hvl
  generalize hvnd : (V.regs 3).toNat = vn at hvn hvv hvl
  have hr3 : V.regs 3 = BitVec.ofNat 64 vn := by rw [← hvnd, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hr0 : V.regs 0 = BitVec.ofNat 64 vp := by rw [← hvpd, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hI1 := toInt_small (BitVec.ofNat 64 vn) (by simp; omega)
  have hI5 := toInt_small (BitVec.ofNat 64 (hdrV s p len 2)) (by simp; omega)
  have hn1 : (BitVec.ofNat 64 vn).toNat = vn := by simp; omega
  have hn5 : (BitVec.ofNat 64 (hdrV s p len 2)).toNat = hdrV s p len 2 := by simp; omega
  have hs3' : V.mem.readLE ((s.regs 4).toNat - 472) 8 = (BitVec.ofNat 64 (hdrV s p len 2)).toNat := by rw [hs3, hn5]
  by_cases hge : hdrV s p len 2 ≤ vn
  · -- `len(v) ≥ modLen`: return `v`
    have heq : vn = hdrV s p len 2 := by omega
    janus64_run [hsp, hm1, hm2, hs3', hr0, hr3, hI1, hI5, hn1, hn5, BitVec.msb_eq_decide]
    refine hOk _ ⟨by janus64_simp [hsp], by janus64_simp [hm2, regFP], by janus64_simp [h14, regG],
      by janus64_simp [hx15]⟩ ⟨by janus64_simp, by janus64_simp; omega, ?v⟩
      ⟨by janus64_simp [hfs], by janus64_simp [hdf], L1, b1, hext, bud_nopad hbud, ?inv, ?held, ?mf, ?lf⟩
    case v => janus64_simp; rw [← heq]; exact hvv
    case inv => dsimp only; exact hinv
    case held => janus64_simp; intro h; rw [← heq]; exact Or.inl (hvl (by omega)).1
    case mf => dsimp only; exact hMF
    case lf => dsimp only; exact hLF
  · -- `len(v) < modLen`: `makeslice(uint8, modLen, modLen)`
    have hlt : vn < hdrV s p len 2 := by omega
    have hwS : V.mem.accessible ((s.regs 4).toNat - W) (W + 40) true = true := by rw [hMF.accessible]; exact hw
    have hmk' : MakesliceLiveContract64 (LibRun.program.link impl) (cA "runtime.makeslice") 4096 R :=
      MakesliceLiveContract64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hmk
    have hmkP := hmk'.pos L1 b1
    janus_eval_nat h_u : uint8T
    have hokb : R.ok (cA "runtime.makeslice") [7231264, hdrV s p len 2, hdrV s p len 2] := by
      have := hokB _ hl2; rwa [h_u] at this
    have hU2 : V.mem.readLE 7231264 8 = 1 := u8T_size hdS
    have hU3 : V.mem.readLE 7231272 8 = 0 := u8T_ptr hdS
    have hut : Apart 7231264 16 ((s.regs 4).toNat - W) (W + 40) :=
      apart_of_data (x := 7231264) (l := 16) hd 0 (by decide) (by decide) hw
    unfold Apart at hut
    have hU1 : V.mem.accessible 7231264 16 false = true := by rw [hMF.accessible]; exact u8T_acc hd
    have ⟨hBS, hbudk⟩ := bud_pad (n := hdrV s p len 2) hl2 hbB hbud
    have hLSm : ∀ r ∈ L1, Outside r.fst (r.snd - r.fst)
        ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
            ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
          [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) := by
      intro r hr; have := hLsS r hr
      simp only [win, Outside, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
      omega
    have hvW : 0 < vn → vp + vn ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 40 ≤ vp := fun h => by
      have := InRanges.apart (hvl h).2.1 hout; unfold Apart at this; omega
    unfold Apart at hga
    obtain ⟨hcf1, hcf2, hcf3, hcf4⟩ := frame_call_factsW hW hal hg3 hga
    set_option janus.callRegions true in
    janus64_run [hsp, hm1, hm2, hs3', hr0, hr3, hI1, hI5, hn1, hn5, hU2, hU3, BitVec.msb_eq_decide] until [pcP]
      calls [hmkP]
    rename_i ptr _ _ _ _ mk _ _ hLFk hMFk hapk hink hbk hack h8k _ hzk hrk hapSk hinvk
    have hMFm : MemFrame V.mem mk (R.rt ++ win s W 40) :=
      frame_cs_trans hW hb' (frame_w _ (frame_w _ (frame_w _ (MemFrame.refl _ _) hb' (by decide) (Nat.le_trans (by decide) hW)) hb' (by decide) (Nat.le_trans (by decide) hW)) hb' (by decide) (Nat.le_trans (by decide) hW)) hMFk
    have hdk := dataLoaded_frame64 hdS (by simp [hrg1]) hro hMFm (fun r hr _ => by
      simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      exact Janus.Arm64.Memory.accessible_mono _ hwS (Nat.le_refl _) (by omega))
    have hLFS : LiveFrame V.mem mk L1 [] :=
      (LiveFrame.of_win (by simp only [win]; janus_frame) hLsS).trans hLFk (fun _ _ h => h)
    have hext' : LiveExt R L1 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) :=
      LiveExt.single (by simpa using hink) (by simpa using hapk)
    have hMF2 : MemFrame s.mem mk (R.rt ++ win s W 40) := hMF.trans hMFm fun _ _ h => ⟨h, h⟩
    refine hk _ (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) (b1 - blockSize (hdrV s p len 2) true)
      vp vn ptr.toNat ⟨by janus64_simp [hsp], by janus64_simp [h14], by janus64_simp [h5], by janus64_simp [hx15],
        by janus64_simp [hfs], by janus64_simp [hdf],
        by janus64_simp [hm1], by janus64_simp [hm2], by janus64_simp [hs3], hl2, by janus64_simp, by janus64_simp, hlt,
        by janus64_simp, by omega, Janus.Arm64.Memory.accessible_mono _ hack (Nat.le_refl _) (by omega),
        fun j hj => by janus64_simp; rw [hzk j hj]; rfl,
        ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩,
        hink.sub (Nat.le_refl _) (by omega), ?sepL, ?val, ?vfacts, hdk, hext.trans hext', hbudk, hinvk, ?sepW,
        hMF2, hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)⟩ (by janus64_simp)
    case sepL =>
      intro r hr
      have := hapk r (hext.mem_old hr); unfold Apart at this
      simp only [Janus.outside_cons, Janus.outside_nil, and_true]; omega
    case val =>
      janus64_simp
      rcases Nat.eq_zero_or_pos vn with h0 | h0
      · rw [h0] at hvv ⊢; exact hvv
      · rw [beVal_liveFrame hLFS (hvl h0).1 (by simp [Outside]), hvv]
    case vfacts =>
      intro h0
      obtain ⟨hi, -, hac, h48⟩ := hvl h0
      refine ⟨h48, Janus.Arm64.Memory.accessible_read_of_write _ (by rw [← hMF.accessible]; exact hac), ?_⟩
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

end FvModexp.Amd64.Run
