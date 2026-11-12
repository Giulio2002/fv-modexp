import FvModexp.Proofs.Arm64.Top.RunDRel
import FvModexp.Proofs.Arm64.Top.RunL
import FvModexp.Proofs.Arm64.Top.RunD1
import FvModexp.Proofs.Arm64.Top.RunD1J
import FvModexp.Proofs.Arm64.Top.RunBox

/-! # `Run` (arm64): `C0` to `D1`, base operand of more than 32 bytes, shorter than the input rest: `makeslice` buffer, `memmove` -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem d1l (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 3 L1 b1 S)
    (T : State) (hTpc : T.pc = BitVec.ofNat 64 pcC0) (hTm : T.mem = S.mem) (hTsp : T.sp = S.sp)
    (hT28 : T.regs 28 = S.regs 28) (hT29 : T.regs 29 = S.regs 29) (hT18 : T.regs 18 = S.regs 18)
    (hl0 : hdrV s p len 0 ≤ 1024) (hl1 : hdrV s p len 1 ≤ 1024) (hl2 : hdrV s p len 2 ≤ 1024)
    (hnz : ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0))
    (hr8 : (T.regs 8).toNat = hdrV s p len 0) (hr11 : (T.regs 11).toNat = hdrV s p len 1)
    (hr12 : (T.regs 12).toNat = hdrV s p len 2)
    (hr1 : (T.regs 1).toNat = p.toNat + (if 96 < len.toNat then 96 else 0))
    (hr3 : (T.regs 3).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0)) (hr7 : (T.regs 7).toNat = len.toNat - 96)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b) (hndir : len.toNat - 96 < hdrV s p len 0) (hlg : 32 < hdrV s p len 0)
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 1 L2 b2 S2 → S2.pc = BitVec.ofNat 64 pcD1 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  have henv0 := henv
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, -, hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF, hLF,
    -⟩ := hrel
  have hap1 := hap.1
  have hLs0 := hLsS
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  simp only [win, Outside, and_true] at hpw hcw
  have hI7 := toInt_small (T.regs 7) (by omega)
  have hI8 := toInt_small (T.regs 8) (by omega)
  have hI11 := toInt_small (T.regs 11) (by omega)
  have hI12 := toInt_small (T.regs 12) (by omega)
  have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hMF.readLE _ _ (by
      simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      unfold Apart at hga; exact ⟨hgr, by omega, by omega⟩)
  have hwS : S.mem.accessible (s.sp.toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hspn : S.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  unfold Apart at hga
  have hwT : Outside SetBytes.wordT 16 R.rt := RoOut.out' hro 1 (by decide) (by decide)
  janus_eval_nat h_t : SetBytes.wordT
  rw [h_t] at hwT hokS
  have hLS1 : ∀ r ∈ L1, r.fst + (r.snd - r.fst) ≤ BitVec.toNat s.sp - 624 - 4160 ∨ BitVec.toNat s.sp - 624 + 48 ≤ r.fst := by
    intro r hr; have := hLsS r hr; simp only [Outside, and_true] at this; omega
  have hS := RunCallees.sbFixD impl hap R hmk b1 L1
  have hr8' : T.regs 8 = BitVec.ofNat 64 (hdrV s p len 0) := by
    apply BitVec.eq_of_toNat_eq; rw [hr8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmv' : MemmoveLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmv
  have hc : (len.toNat - 96 < hdrV s p len 0) = True := by simp; omega
  have hmk' : MakesliceLiveContract (LibRun.program.link impl) (cA "runtime.makeslice") 4096 R :=
    MakesliceLiveContract.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmk
  have hmkP := hmk'.pos L1 b1
  have hc32 : (32 < hdrV s p len 0) = True := by simp; omega
  janus_eval_nat h_u : uint8T
  have hokb : R.ok (cA "runtime.makeslice") [uint8T, hdrV s p len 0, hdrV s p len 0] := hokB _ (by omega)
  rw [h_u] at hokb
  have hU1 : s.mem.accessible 2639168 16 false = true := by
    janus_data hd; exact Memory.accessible_mono _ h_data0 (by omega) (by omega)
  have hU2 : S.mem.readLE 2639168 8 = 1 := by
    janus_data hdS; rw [h_rodata _ _ (by decide)]; decide
  have hU3 : S.mem.readLE 2639176 8 = 0 := by
    janus_data hdS; rw [h_rodata _ _ (by decide)]; decide
  have hut : Apart 2639168 16 (s.sp.toNat - 4800) (4800 + 40) := by
    exact apart_of_data (x := 2639168) (l := 16) hdS 0 (by decide) (by decide) hwS
  unfold Apart at hut
  have hBS : blockSize (hdrV s p len 0) true ≤ b1 := by
    have := blockSize_le_allocCost (hdrV s p len 0) true
    simp only [allocCost, dCost, makeCost, makeCap] at this hbudD hbud ⊢; omega
  set_option janus.callRegions true in
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hgS, hr7, hr8', hr11, hr12, hI7, hI8, hI11, hI12, hc, hc32, hU2, hU3,
    natLive_zero, toInt_ite, toNat_ite] until [segAddr Extracted.program fn + 0x4a0] calls [hmkP]
  rename_i ptr _ _ _ mk _ _ hLFk hMFk hapk hink hbk hack h8k h16k hzk hrk hapSk hinvk
  clear hut hcw
  have bxp := Box.mk hpw
  clear hpw
  have hdk := dataLoaded_win (lo := s.sp.toNat - 4800) (n := 4800 + 40) ?d0 (by rw [hrg1]; simp) hro hMFk ?wacc ?ws
  case d0 => janus_callpre
  case wacc => simpa only [Memory.accessible_writeLE] using hwS
  case ws =>
    intro r hr
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
  clear hdS hinv
  have hlen1 : 0 < len.toNat := by
    refine Nat.pos_of_ne_zero fun h0 => hnz ⟨?_, ?_⟩ <;>
      (simp only [hdrV]; exact padBE_past _ _ _ _ _ (by omega))
  obtain ⟨off, hoffd⟩ : ∃ off, (if 96 < len.toNat then 96 else 0) = off := ⟨_, rfl⟩
  have hoffc : (96 < len.toNat ∧ off = 96) ∨ (len.toNat ≤ 96 ∧ off = 0) := by
    subst hoffd; split <;> omega
  have hr1n : (T.regs 1).toNat = p.toNat + off := by rw [hr1, hoffd]
  have hmvok : R.ok (cA "runtime.memmove") [ptr.toNat, (T.regs 1).toNat, len.toNat - 96] := hokM _ _ _ (by omega)
  have hs1 : (T.regs 1).toNat + (len.toNat - 96) ≤ 2 ^ 48 := by rw [hr1n]; omega
  have hs2 : s.mem.accessible (T.regs 1).toNat (len.toNat - 96) false = true := by
    rw [hr1n]; exact Memory.accessible_mono _ hpacc (by omega) (by omega)
  have hs3 : (T.regs 1).toNat + (len.toNat - 96) ≤ BitVec.toNat s.sp - 624 - 4096 ∨
      BitVec.toNat s.sp - 624 - 8 ≤ (T.regs 1).toNat := by have hpw := bxp.h; rw [hr1n]; omega
  have hs4 : (T.regs 1).toNat + (len.toNat - 96) ≤ BitVec.toNat s.sp - 624 + 8 ∨
      BitVec.toNat s.sp - 624 + 8 + 24 ≤ (T.regs 1).toNat := by have hpw := bxp.h; rw [hr1n]; omega
  have hpo : ptr.toNat + blockSize (hdrV s p len 0) true ≤ s.sp.toNat - 4800 ∨ s.sp.toNat + 40 ≤ ptr.toNat := by
    have := InRanges.apart hink hout; unfold Apart at this; omega
  have hpI : (T.regs 1).toNat + (len.toNat - 96) ≤ ptr.toNat ∨ ptr.toNat + blockSize (hdrV s p len 0) true ≤ (T.regs 1).toNat := by
    have h1 : Outside (T.regs 1).toNat (len.toNat - 96) R.rt ∨ InRanges (T.regs 1).toNat (len.toNat - 96) L1 := by
      rw [hr1n]; exact (hext.held (hheld.sub (by omega) (by omega))).symm
    rcases h1 with h1 | h1
    · have := InRanges.apart hink h1; unfold Apart at this; omega
    · have := hapk.apart_of_inRanges h1; unfold Apart at this; omega
  have hsrcA : (T.regs 1).toNat + 1 ≤ ptr.toNat ∨ ptr.toNat + blockSize (hdrV s p len 0) true ≤ (T.regs 1).toNat := by
    rw [hr1n]
    rcases hext.held (hheld.sub (a := p.toNat + off) (n := 1) (by omega) (by omega)) with h | h
    · have := hapk.apart_of_inRanges h; unfold Apart at this; omega
    · have := InRanges.apart hink h; unfold Apart at this; omega
  have hne : (ptr.toNat = (T.regs 1).toNat) = False := by
    simp only [eq_iff_iff, iff_false]; omega
  have hne' : ((T.regs 1).toNat = ptr.toNat) = False := by
    simp only [eq_iff_iff, iff_false]; omega
  set_option janus.callRegions true in
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hgS, hr7, hr8', hr11, hr12, hI7, hI8, hI11, hI12, hc, hc32, hne, hne',
    natLive_zero, toInt_ite, toNat_ite] until [segAddr Extracted.program fn + 0x4dc] calls [hmv']
  rename_i m2 _ _ hMFm hLFm hinvm hcp
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hr7, hr8', hr11, hr12, hI7, hI8, hI11, hI12, hc, hc32,
    toInt_ite, toNat_ite] until [pcJ1]
  have hstk : stk = 4800 := rfl
  have hLsL1 : LiveSep L1 (win s 4800 40) := hLs0
  have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (by omega)
  have hext' : LiveExt R L1 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 0) true)]) :=
    LiveExt.single (by simpa using hink) (by simpa using hapk)
  have hlr : len.toNat - 96 ≤ blockSize (hdrV s p len 0) true := by omega
  have hink' : InRanges ptr.toNat (len.toNat - 96) R.rt := hink.sub (Nat.le_refl _) (by omega)
  have hm : ∀ a n w, mk.accessible a n w = s.mem.accessible a n w := fun a n w => by
    simp only [hMFk.accessible, Memory.accessible_writeLE, hMF.accessible]
  have hdk' : Extracted.program.DataLoaded (mk.writeLE (BitVec.toNat s.sp - 248) 8 (BitVec.toNat ptr)) :=
    hdk.writeLE (by rw [hm]; exact Memory.accessible_mono _ hw (by omega) (by omega))
  have hd2 : Extracted.program.DataLoaded m2 := by
    refine dataLoaded_frame hdk' (by rw [hrg2]; simp) hro (by rw [List.append_assoc] at hMFm; exact hMFm) fun r hr _ => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [Memory.accessible_writeLE]
    rcases hr with (rfl | rfl) | rfl
    · rw [hm]; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · rw [hm]; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · rw [hm]; exact Memory.accessible_mono _ hack (Nat.le_refl _)
        (by dsimp only; rw [Nat.add_sub_cancel_left]; exact Nat.add_le_add_left hlr _)
  have hMF2 : MemFrame s.mem m2 (R.rt ++ winA s stk 40) := by
    simp only [winA, stk] at hMF ⊢
    refine (((hMF.trans ?w1 fun a n h => ⟨h, out_wA h⟩).trans hMFk fun a n h => ⟨h, out_cs hb' h⟩).trans ?w2
      fun a n h => ⟨h, out_wA h⟩).trans hMFm fun a n h => ⟨h, out_csd hb' hink' h⟩
    case w1 => janus_frame
    case w2 => janus_frame
  have hdst : LiveSep L1 [(ptr.toNat, ptr.toNat + (len.toNat - 96))] := by
    intro r hr; have := hapk r hr; unfold Apart at this
    simp only [Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hLF2 : LiveFrame s.mem m2 L [] :=
    ((((hLF.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => hext.inRanges_old h)).trans
      hLFk (fun _ _ h => hext.inRanges_old h)).trans
      (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1) (fun _ _ h => hext.inRanges_old h)).trans
      (LiveFrame.drop (L := L1) ⟨fun a n h hw => hLFm.readLE a n (h.append_left _) hw⟩ hdst) (fun _ _ h => hext.inRanges_old h))
  have hLx := LiveFrame.of_nil' hLF2 (winA s stk 40)
  have hpo' : Outside p.toNat len.toNat (winA s stk 40) := by
    simp only [winA, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hco' : Outside c.toNat 3 (winA s stk 40) := by
    simp only [winA, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hIn : ∀ a n, p.toNat ≤ a → a + n ≤ p.toNat + len.toNat → m2.readLE a n = s.mem.readLE a n :=
    fun a n h1 h2 => (hheld.sub h1 h2).readLE hMF2 hLx (hpo'.of_sub h1 (by omega))
  have hCc : m2.readLE c.toNat 3 = s.mem.readLE c.toNat 3 := hcheld.readLE hMF2 hLx hco'
  refine d1join impl hap R hmk hokS b L c p len cp ret hret s henv0 hin0 Q hbudD hk _
    (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 0) true)]) (b1 - blockSize (hdrV s p len 0) true) ptr.toNat
    ?hj (by janus_simp)
  case hj =>
  refine ⟨by janus_simp [hsp], by janus_simp [h28, hT28], by janus_simp [h29, hT29], by janus_simp [h18, hT18],
     by janus_simp [hm1], by janus_simp [hm2], by janus_simp [hm3], by janus_simp [hm4], by janus_simp [hm5],
     by janus_simp [hm6], by janus_simp [hr8], by janus_simp [hr11], by janus_simp [hr12], by janus_simp [hr7],
     by janus_simp [hr3], by janus_simp [hr1], ?spill, by janus_simp, by janus_simp, by janus_simp, hl0, hl1, hl2, hnz,
     by janus_simp, by janus_simp, (by janus_simp <;> omega), ?r6, by janus_simp [hr11], by omega,
     (Memory.accessible_read_of_write _ (Memory.accessible_mono _ hack (Nat.le_refl _) (by omega))), ?held, (by omega),
     ?bytes, ?dl, hIn, hCc,
     hext.trans hext', (by have hBS' := blockSize_le_allocCost (hdrV s p len 0) true
                           simp only [dCost, allocCost] at hbud hBS' ⊢; omega), ?inv, ?ls, hMF2, hLF2⟩
  case held => exact Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩
  case spill => janus_simp [hr7] <;> omega
  case r6 => janus_simp [hr7] <;> omega
  case dl => exact hd2
  case inv => exact hinvm
  case ls =>
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hLsL1 r hr
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [win, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  case bytes =>
    intro j hj
    have hLFw : LiveFrame (mk.writeLE (BitVec.toNat s.sp - 248) 8 (BitVec.toNat ptr)) m2
        (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 0) true)])
        ([(BitVec.toNat s.sp - 624 - 4096, BitVec.toNat s.sp - 624 - 8),
          (BitVec.toNat s.sp - 624 + 8, BitVec.toNat s.sp - 624 + 8 + 24)] ++
          [(BitVec.toNat ptr, BitVec.toNat ptr + (len.toNat - 96))]) :=
      ⟨fun a n h ho => hLFm.readLE a n h (by
        simp only [Janus.outside_append] at ho; exact ho.2)⟩
    unfold padByte
    split
    · rename_i hjl
      obtain ⟨-, rfl⟩ : 96 < len.toNat ∧ off = 96 := by omega
      have hcj := hcp j (by omega)
      rw [hcj, ← Memory.readLE_one, hr1n]
      have hH : Held R (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 0) true)]) (p.toNat + 96 + j) 1 :=
        (hext.trans hext').held (hheld.sub (by omega) (by omega))
      rw [← hH.readLE (by rw [List.append_assoc] at hMFm; exact hMFm) hLFw (by
        simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rcases hext.held (hheld.sub (a := p.toNat + 96 + j) (n := 1) (by omega) (by omega)) with h | h
        · have := hapk.apart_of_inRanges h; unfold Apart at this; omega
        · have := InRanges.apart hink h; unfold Apart at this; omega)]
      rw [hIn _ _ (by omega) (by omega), Memory.readLE_one, Nat.add_assoc]
    · rename_i hjl
      rw [← Memory.readLE_one, hLFw.readLE _ _ ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        by dsimp only; omega, by dsimp only; omega⟩ (by
          simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
          refine ⟨⟨by omega, by omega⟩, by omega⟩),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_one, hzk j hj]
      rfl

end FvModexp.Arm64.Run
