import FvModexp.Proofs.Arm64.Top.RunD3ZDefs

/-! # `Run` (arm64): `D2` to `Z3`, modulus operand of more than 32 bytes longer than the input rest: the `makeslice`
buffer of `RightPadBytes` (see `RunD3ZDefs`), with `nb` input bytes left to copy (`0` or more) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

theorem past_nb (l a b : Nat) : l ≤ 96 + (a + b) + (l - 96 - min (b + a) (l - 96)) := by omega

theorem nb_facts {l a b off mN h2 : Nat} (p : Nat) (hoff : (96 < l ∧ off = 96) ∨ (l ≤ 96 ∧ off = 0))
    (hmN : mN ≤ min (b + a) (l - 96) ∧ (l - 96 - min (b + a) (l - 96) = 0 ∨ mN = min (b + a) (l - 96)))
    (hndir : l - 96 < min (b + a) (l - 96) + h2) (hn : 0 < l - 96 - min (b + a) (l - 96)) :
    p + off + mN = p + 96 + (a + b) ∧ p + off + mN + (l - 96 - min (b + a) (l - 96)) = p + l ∧
      l - 96 - min (b + a) (l - 96) < h2 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem d3zA (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelD R b L c p len cp s ret 2 L1 b1 S)
    (hpc : S.pc = BitVec.ofNat 64 pcD2)
    (hndir : len.toNat - 96 < min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2) (hlg : 32 < hdrV s p len 2)
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (hkZ : ∀ U Lk bk B src, JoinZ3 R b L c p len cp s ret Lk bk B src
      (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) U → U.pc = BitVec.ofNat 64 pcZ3 →
      Reaches ((LibRun.program.link impl).withExit ret) U Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  have henv0 := henv
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hl0, hl1, hl2, hnz, hk1, hk2,
    hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  obtain ⟨hk1a, hk1b⟩ := hk1 (by omega)
  have hk2a := hk2 (by omega)
  have hS1n : (if len.toNat - 96 < hdrV s p len 1 + hdrV s p len 0 then len.toNat - 96 else hdrV s p len 1 + hdrV s p len 0) =
      min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) := by split <;> omega
  have hS1 : (if len.toNat - 96 < hdrV s p len 1 + hdrV s p len 0 then BitVec.ofNat 64 (len.toNat - 96)
      else BitVec.ofNat 64 (hdrV s p len 1 + hdrV s p len 0)) = BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) := by
    rw [← hS1n, apply_ite (BitVec.ofNat 64)]
  have hadd : BitVec.ofNat 64 (hdrV s p len 2) + BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) =
      BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2) := bv_add_of_lt _ _ (by omega)
  have hmod : (hdrV s p len 2 + min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) % 18446744073709551616 = min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2 := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hap1 := hap.1
  have hLs0 := hLsS
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  simp only [win, Outside, and_true] at hpw hcw
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
  have hMC0 : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2))) ≤ allocCost (8 * 132) := by
    have h1 : SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2)) ≤ 128 := by simp [SetBytes.nW]; omega
    have h3 : makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2))) ≤ 132 := by unfold makeCap; split <;> omega
    simp only [makeCost, allocCost]; omega
  have hMC : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2))) ≤ b1 := by
    simp only [dCost, allocCost] at hbudD hbud hMC0 ⊢; omega
  have hokm : R.ok (cA "runtime.makeslice") [2641088, SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2)),
      makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 2)))] := hokS _ (by simp [SetBytes.nW]; omega)
  have hc : (len.toNat - 96 < min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2) = True := by simp; omega
  have hc32 : (32 < hdrV s p len 2) = True := by simp; omega
  have hIe := toInt_small (BitVec.ofNat 64 (hdrV s p len 2)) (by simp; omega)
  obtain ⟨off, hoffd⟩ : ∃ off, inOff len = off := ⟨_, rfl⟩
  have hoffc : (96 < len.toNat ∧ off = 96) ∨ (len.toNat ≤ 96 ∧ off = 0) := by
    subst hoffd; simp only [inOff]; split <;> omega
  rw [hoffd] at hs5 hs6
  have hcap : min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) ≤ cp.toNat - off := by omega
  obtain ⟨mN, hmNd⟩ : ∃ mN, (if min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) < cp.toNat - off then
      min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) else 0) = mN := ⟨_, rfl⟩
  have hmN : mN ≤ min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) ∧
      (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) = 0 ∨ mN = min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) := by
    subst hmNd; split <;> omega
  have hmask : (BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) &&&
      (BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) - BitVec.ofNat 64 (cp.toNat - off)).sshiftRight 63) =
      BitVec.ofNat 64 mN := by
    apply BitVec.eq_of_toNat_eq
    rw [sliceMask_le _ _ hcap (by omega), hmNd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : BitVec.ofNat 64 (len.toNat - 96) - BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) =
      BitVec.ofNat 64 (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) :=
    bv_sub_of_le _ _ (Nat.min_le_right _ _) (by omega)
  have hcsub : BitVec.ofNat 64 (cp.toNat - off) - BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) =
      BitVec.ofNat 64 (cp.toNat - off - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) :=
    bv_sub_of_le _ _ hcap (by omega)
  have hsrc : BitVec.ofNat 64 mN + BitVec.ofNat 64 (p.toNat + off) = BitVec.ofNat 64 (p.toNat + off + mN) :=
    bv_add_of_lt _ _ (by omega)
  have hpast := past_nb len.toNat (hdrV s p len 0) (hdrV s p len 1)
  have hsrcb : p.toNat ≤ p.toNat + off + mN ∧ p.toNat + off + mN ≤ p.toNat + len.toNat := by omega
  have hpo' : Outside p.toNat len.toNat (winA s stk 40) := outA_of hpw
  have hco' : Outside c.toNat 3 (winA s stk 40) := outA_of hcw
  have hIa := toInt_small (BitVec.ofNat 64 (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96))) (by simp; omega)
  have hmk' : MakesliceLiveContract (LibRun.program.link impl) (cA "runtime.makeslice") 4096 R :=
    MakesliceLiveContract.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmk
  have hmkP := hmk'.pos L1 b1
  janus_eval_nat h_u : uint8T
  have hokb : R.ok (cA "runtime.makeslice") [uint8T, hdrV s p len 2, hdrV s p len 2] := hokB _ (by omega)
  rw [h_u] at hokb
  have hU1 : s.mem.accessible 2639168 16 false = true := by
    janus_data hd; exact Memory.accessible_mono _ h_data0 (by omega) (by omega)
  have hU2 : S.mem.readLE 2639168 8 = 1 := by
    janus_data hdS; rw [h_rodata _ _ (by decide)]; decide
  have hU3 : S.mem.readLE 2639176 8 = 0 := by
    janus_data hdS; rw [h_rodata _ _ (by decide)]; decide
  have hut : Apart 2639168 16 (s.sp.toNat - 4800) (4800 + 40) :=
    apart_of_data (x := 2639168) (l := 16) hdS 0 (by decide) (by decide) hwS
  unfold Apart at hut
  have hBS : blockSize (hdrV s p len 2) true ≤ b1 := by
    have := blockSize_le_allocCost (hdrV s p len 2) true
    simp only [allocCost, dCost, makeCost, makeCap] at this hbudD hbud ⊢; omega
  set_option janus.callRegions true in
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hk1a, hk1b, hk2a, hS1, hS1n, hadd, hmod, hc, hc32, hIe, hIa, hmask, hsub,
    hcsub, hsrc, hU2, hU3, toInt_ite, toNat_ite, toInt_small] until [segAddr Extracted.program fn + 0x6f8] calls [hmkP]
  rename_i ptr _ _ _ mk _ _ hLFk hMFk hapk hink hbk hack h8k h16k hzk hrk hapSk hinvk
  have hdk := dataLoaded_win (lo := s.sp.toNat - 4800) (n := 4800 + 40) ?d0 (by rw [hrg1]; simp) hro hMFk ?wacc ?ws
  case d0 => janus_callpre
  case wacc => simpa only [Memory.accessible_writeLE] using hwS
  case ws =>
    intro r hr
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
  clear hdS hinv
  have hpo : ptr.toNat + blockSize (hdrV s p len 2) true ≤ s.sp.toNat - 4800 ∨ s.sp.toNat + 40 ≤ ptr.toNat := by
    have := InRanges.apart hink hout; unfold Apart at this; omega
  have hLsL1 : LiveSep L1 (win s 4800 40) := hLs0
  have hext' : LiveExt R L1 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) :=
    LiveExt.single (by simpa using hink) (by simpa using hapk)
  have hMF2 : MemFrame s.mem mk (R.rt ++ winA s stk 40) := by
    simp only [winA, stk] at hMF ⊢
    refine (hMF.trans ?w1 fun a n h => ⟨h, out_wA h⟩).trans hMFk fun a n h => ⟨h, out_cs hb' h⟩
    case w1 => janus_frame
  have hLFS : LiveFrame S.mem mk L1 [] :=
    (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans hLFk (fun _ _ h => h)
  have hLF2 : LiveFrame s.mem mk L [] := hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)
  have hLx := LiveFrame.of_nil' hLF2 (winA s stk 40)
  have hBloc : ptr.toNat + hdrV s p len 2 ≤ s.sp.toNat - 624 - 4160 ∨ s.sp.toNat + 40 ≤ ptr.toNat := by omega
  have hls : LiveSep (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) (win s stk 40) := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hLsL1 r hr
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [win, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hsep : LiveSep (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) [(ptr.toNat, ptr.toNat)] := by
    intro r hr; simp only [Janus.outside_cons, Janus.outside_nil, and_true]
    rcases List.mem_append.1 hr with hr | hr
    · have := hapk r hr; unfold Apart at this; omega
    · simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega
  have hsepB : LiveSep L1 [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)] := by
    intro r hr; simp only [Janus.outside_cons, Janus.outside_nil, and_true]
    have := hapk r hr; unfold Apart at this; omega
  have hbytes : ∀ j, j < hdrV s p len 2 →
      (mk.bytes (ptr.toNat + j)).toNat = padByte s.mem p.toNat len.toNat (96 + (hdrV s p len 0 + hdrV s p len 1) + j) := by
    intro j hj
    rw [hzk j hj]; rfl
  have hbudk : b - (3 * makeCost 4 + 2 * dCost + allocCost 1024) ≤ b1 - blockSize (hdrV s p len 2) true := by
    have hBS' := blockSize_le_allocCost (hdrV s p len 2) true
    simp only [dCost, allocCost] at hbud hBS' ⊢; omega
  have hacc' : s.mem.accessible ptr.toNat (hdrV s p len 2) true = true :=
    Memory.accessible_mono _ hack (Nat.le_refl _) (by omega)
  have hrt' : InRanges ptr.toNat (hdrV s p len 2) R.rt := hink.sub (Nat.le_refl _) (by omega)
  have hB48 : ptr.toNat + hdrV s p len 2 ≤ 2 ^ 48 := by omega
  have hheld' : Held R (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) ptr.toNat (hdrV s p len 2) :=
    Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩
  have hinp : ∀ a n, p.toNat ≤ a → a + n ≤ p.toNat + len.toNat → mk.readLE a n = s.mem.readLE a n :=
    fun a n h1 h2 => (hheld.sub h1 h2).readLE hMF2 hLx (hpo'.of_sub h1 (by omega))
  have hcc := hcheld.readLE hMF2 hLx hco'
  have hnbp : 0 < (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) →
      p.toNat + off + mN = p.toNat + 96 + (hdrV s p len 0 + hdrV s p len 1) ∧
      p.toNat + off + mN + (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) = p.toNat + len.toNat ∧ (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) < hdrV s p len 2 ∧
      (p.toNat + off + mN + (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) ≤ ptr.toNat ∨ ptr.toNat + blockSize (hdrV s p len 2) true ≤ p.toNat + off + mN) := by
    intro hn
    obtain ⟨e1, e2, e3⟩ := nb_facts p.toNat hoffc hmN hndir hn
    refine ⟨e1, e2, e3, ?_⟩
    clear hoffc hmN hpw hcw hpo hga hut hLS1
    rcases hext.held (hheld.sub (a := p.toNat + off + mN) (n := (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96))) (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _)) (Nat.le_of_eq e2)) with h | h
    · have := hapk.apart_of_inRanges h; unfold Apart at this; omega
    · have := InRanges.apart hink h; unfold Apart at this; omega
  have hnbm : (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) % 18446744073709551616 = (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt ((Nat.sub_le _ _).trans (Nat.sub_le _ _)) len.isLt)
  clear hoffc hmN hpw hcw hpo hga hut hLS1 hink hapk hzk
  have ho0 : OpDone mk s p len L1 0 := OpDone.transport (hop 0 (by omega)) (by janus_simp [opAt]) (by janus_simp [opAt])
    (by janus_simp [opAt]) (by janus_simp [opAt]) hLFS (fun _ _ h => h)
  have ho1 : OpDone mk s p len L1 1 := OpDone.transport (hop 1 (by omega)) (by janus_simp [opAt]) (by janus_simp [opAt])
    (by janus_simp [opAt]) (by janus_simp [opAt]) hLFS (fun _ _ h => h)
  refine hkZ _ (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 2) true)]) (b1 - blockSize (hdrV s p len 2) true)
    ptr.toNat (p.toNat + off + mN) ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29], by janus_simp [h18],
     by janus_simp [hm1], by janus_simp [hm2], by janus_simp [hm3], by janus_simp [hm4], by janus_simp [hm5],
     by janus_simp [hm6], by janus_simp [hs1], by janus_simp [hs2], by janus_simp [hs3], by janus_simp [hs4],
     by janus_simp [hs5, hoffd], by janus_simp [hs6, hoffd], by janus_simp [hk1a], by janus_simp [hk1b], by janus_simp [hk2a],
     by janus_simp, by janus_simp, by janus_simp, hl0, hl1, hl2, hnz, hlg,
     by janus_simp, (by janus_simp [hnbm]), (by janus_simp [hsrc]), hsrcb.1, hsrcb.2, hB48, hacc', hheld', hBloc,
     hrt', hsep, hbytes, hpast, hnbp, hdk, hinp, hcc, hext.trans hext', hbudk, hinvk, hls, hMF2, hLF2,
     ho0.transport rfl rfl rfl rfl (LiveFrame.refl _ _ _) (fun _ _ h => hext'.inRanges_old h),
     ho1.transport rfl rfl rfl rfl (LiveFrame.refl _ _ _) (fun _ _ h => hext'.inRanges_old h),
     OpsApart.transport hopA (fun i hi => by
       rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> exact ⟨by janus_simp [opAt], by janus_simp [opAt]⟩),
     ⟨L1, rfl, hext, hsepB, ho0, ho1⟩⟩ (by janus_simp)

end FvModexp.Arm64.Run
