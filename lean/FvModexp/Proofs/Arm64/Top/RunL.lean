import FvModexp.Proofs.Arm64.Top.RunLa

/-! # `Run` (arm64): `P1` to `C0` — EIP-7823 (`inputLenOverflow`, `max > 1024`: `errors.New`), the empty case, the input slice -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

abbrev pcC0 : Nat := segAddr Extracted.program fn + 0x424

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem lb (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (hrecv : s.mem.readLE c.toNat 3 = 65793) (hokn : R.ok (cA "runtime.newobject") [errT])
    (hcostE : 3 * makeCost 4 + allocCost 16 ≤ b)
    (Q : Outcome → Prop)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 3 L1 b1 S)
    (T : State) (hTpc : T.pc = BitVec.ofNat 64 pcP1) (hTm : T.mem = S.mem) (hTsp : T.sp = S.sp)
    (hT28 : T.regs 28 = S.regs 28) (hT29 : T.regs 29 = S.regs 29) (hT18 : T.regs 18 = S.regs 18)
    (hL0 : LenRegs (hdrV s p len 0) (T.regs 6) (T.regs 8)) (hL1 : LenRegs (hdrV s p len 1) (T.regs 7) (T.regs 11))
    (hL2 : LenRegs (hdrV s p len 2) (T.regs 9) (T.regs 12))
    (hErr : ∀ S' : State, (1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2) →
      ABIReturn s S' → ErrRet S' → RunFrame R b (3 * makeCost 4 + allocCost 16) L s S' → Q (.returned S'))
    (hZero : ∀ S' : State, hdrV s p len 0 = 0 → hdrV s p len 1 ≤ 1024 → hdrV s p len 2 = 0 →
      ABIReturn s S' → S'.regs 1 = 0#64 → S'.regs 3 = 0#64 → RunFrame R b (3 * makeCost 4) L s S' → Q (.returned S'))
    (hk : ∀ T' : State, T'.pc = BitVec.ofNat 64 pcC0 → T'.mem = S.mem → T'.sp = S.sp → T'.regs 28 = S.regs 28 →
      T'.regs 29 = S.regs 29 → T'.regs 18 = S.regs 18 →
      hdrV s p len 0 ≤ 1024 → hdrV s p len 1 ≤ 1024 → hdrV s p len 2 ≤ 1024 →
      ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0) →
      (T'.regs 8).toNat = hdrV s p len 0 → (T'.regs 11).toNat = hdrV s p len 1 → (T'.regs 12).toNat = hdrV s p len 2 →
      (T'.regs 1).toNat = p.toNat + (if 96 < len.toNat then 96 else 0) →
      (T'.regs 3).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0) → (T'.regs 7).toNat = len.toNat - 96 →
      Reaches ((LibRun.program.link impl).withExit ret) T' Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, -, hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF, hLF,
    -⟩ := hrel
  have hno' : NewobjectLiveContract (LibRun.program.link impl) (cA "runtime.newobject") 4096 R :=
    NewobjectLiveContract.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hno
  have hap1 := hap.1
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  have hc1 : S.mem.readLE (c.toNat + 1) 1 = 1 := by
    rw [← hcS] at hrecv
    have h3 := Memory.readLE_add S.mem c.toNat 1 2
    have h4 := Memory.readLE_add S.mem (c.toNat + 1) 1 1
    have l1 := Memory.readLE_lt S.mem c.toNat 1
    have l2 := Memory.readLE_lt S.mem (c.toNat + 1) 1
    have l3 := Memory.readLE_lt S.mem (c.toNat + 1 + 1) 1
    rw [hrecv] at h3; rw [h4] at h3; omega
  have hLSn : ∀ r ∈ L1, (r.1 + (r.2 - r.1) ≤ BitVec.toNat s.sp - 624 - 4096 ∨ BitVec.toNat s.sp - 624 - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ BitVec.toNat s.sp - 624 + 8 ∨ BitVec.toNat s.sp - 624 + 8 + 8 ≤ r.1) := by
    intro r hr; have := hLsS r hr; simp only [Outside, and_true] at this; omega
  have hT1 : S.mem.accessible 2762976 16 false = true := by
    janus_data hdS; exact Memory.accessible_mono _ h_data3 (Nat.le_refl _) (by omega)
  have hT2 : S.mem.readLE 2762976 8 = 16 := by
    janus_data hdS; rw [h_rodata _ _ (by decide)]; decide
  have hT3 : blockSize 16 (S.mem.readLE 2762984 8 == 0) ≤ b1 := by
    have := blockSize_le_allocCost 16 (S.mem.readLE 2762984 8 == 0); simp only [allocCost] at this
    simp only [makeCost, allocCost, makeCap] at hbud hcostE; omega
  have hnoP := hno'.pos L1 b1
  have hL0' := hL0
  have hL1' := hL1
  have hL2' := hL2
  obtain ⟨hB0, hO0, hU0⟩ := hL0
  obtain ⟨hB1, hO1, hU1⟩ := hL1
  obtain ⟨hB2, hO2, hU2⟩ := hL2
  have hI6 := toInt_small (T.regs 6) (by omega)
  have hI7 := toInt_small (T.regs 7) (by omega)
  have hI9 := toInt_small (T.regs 9) (by omega)
  have hIl : len.toInt = (len.toNat : Int) := toInt_small len (by omega)
  have hT4 : Apart 2762976 16 (s.sp.toNat - stk) (stk + 40) :=
    apart_of_data hd 3 (by decide) ⟨by decide +kernel, by decide +kernel⟩ (by simp only [stk]; exact hw)
  simp only [stk] at hT4; unfold Apart at hT4
  clear hinS hcS hLs hcheld hheld hpw hcw hpacc hd hno hdS hro hrecv
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hc1, hT2, hI6, hI7, hI9, hIl, toInt_ite, toNat_ite, ite3_int_gt, ite3_nat_le] until [pcC0,
    segAddr Extracted.program fn + 0x3c4] calls [hnoP]
  next =>
    (
         have hcond : 1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2 := by
           first
           | exact err_of_big hL0' hL1' hL2' (by omega)
           | exact err_of_u hL0' hL1' hL2' (by omega) (by omega)
         rename_i ptr _ _ _ m _ _ hLFn hMFn hapL hinR hb48 hacc h8 h16 hz hround hapS hinvn
         have hpo : ptr.toNat + 16 ≤ s.sp.toNat - 4800 ∨ s.sp.toNat + 40 ≤ ptr.toNat := by
           have := InRanges.apart hinR hout; unfold Apart at this; omega
         janus_run [hm1, hm2]
         refine hErr _ hcond ⟨by janus_simp [hsp], by janus_simp [h28, hT28], by janus_simp [hT29, h29, hm2, regFP],
           by janus_simp [h18, hT18, regPlatform]⟩ ⟨by janus_simp, by janus_simp, by janus_simp⟩
           ⟨L1 ++ [(ptr.toNat, ptr.toNat + blockSize 16 (S.mem.readLE 2762984 8 == 0))],
            b1 - blockSize 16 (S.mem.readLE 2762984 8 == 0), ?_, ?_, ?_, ?_, ?_⟩
         · exact hext.trans (LiveExt.single (by simpa using hinR) (by simpa using hapL))
         · have := blockSize_le_allocCost 16 (S.mem.readLE 2762984 8 == 0)
           simp only [makeCost, allocCost, makeCap] at this hbud hcostE ⊢; omega
         · dsimp only
           have hI : ∀ a, ptr.toNat ≤ a → a + 8 ≤ ptr.toNat + 16 →
               InRanges a 8 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize 16 (S.mem.readLE 2762984 8 == 0))]) :=
             fun a h1 h2 => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩
           exact inv_store_live (inv_store_live hinvn (hI _ (Nat.le_refl _) (by omega))) (hI _ (by omega) (by omega))
         · dsimp only
           refine ⟨fun a n h => ?_, fun a n w => by simp only [Memory.accessible_writeLE, hMFn.accessible, hMF.accessible]⟩
           have h' := h
           simp only [win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h'
           have hd1 := InRanges.apart hinR h'.1
           unfold Apart at hd1
           rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
             hMFn.readLE _ _ (by
               simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
               exact ⟨h'.1, by omega, by omega⟩),
             hMF.readLE _ _ (by
               simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
               exact ⟨h'.1, by omega, by omega⟩)]
         · dsimp only
           have ho := hapL.outside
           refine hLF.trans (((hLFn.writeLE _ (ho.of_sub (Nat.le_refl _) (by omega))).writeLE _
             (ho.of_sub (by omega) (by omega)))) (fun _ _ h => hext.inRanges_old h)
         )
  next =>
    (
         have hx0 : (T.regs 6).toNat ≤ 64 := by omega
         have hx1 : (T.regs 7).toNat ≤ 64 := by omega
         have hx2 : (T.regs 9).toNat ≤ 64 := by omega
         have hv0 := hU0 hx0
         have hv1 := hU1 hx1
         have hv2 := hU2 hx2
         refine hZero _ (by omega) (by omega) (by omega) ⟨by janus_simp [hsp], by janus_simp [h28, hT28], by janus_simp [hT29, h29, hm2, regFP],
           by janus_simp [h18, hT18, regPlatform]⟩
           (by janus_simp) (by janus_simp) ⟨L1, b1, hext, by omega, ?_, ?_, ?_⟩
         · dsimp only; (try rw [hTm]); exact hinv
         · dsimp only; (try rw [hTm])
           refine ⟨fun a n h => hMF.readLE a n ?_, hMF.accessible⟩
           simp only [winA, win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
           exact ⟨h.1, by omega, by omega⟩
         · dsimp only; (try rw [hTm]); exact hLF)
  next =>
    (
         have hx0 : (T.regs 6).toNat ≤ 64 := by omega
         have hx1 : (T.regs 7).toNat ≤ 64 := by omega
         have hx2 : (T.regs 9).toNat ≤ 64 := by omega
         have hv0 := hU0 hx0
         have hv1 := hU1 hx1
         have hv2 := hU2 hx2
         refine hk _ (by janus_simp) rfl hsp.symm (by janus_simp [h28]) (by janus_simp [h29]) (by janus_simp [h18])
           (by omega) (by omega) (by omega) (by omega) (by janus_simp; omega) (by janus_simp; omega) (by janus_simp; omega)
           ?_ ?_ ?_ <;>
         (janus_simp <;> (try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]) <;> (try split) <;> omega))
  next =>
    (
         have hx0 : (T.regs 6).toNat ≤ 64 := by omega
         have hx1 : (T.regs 7).toNat ≤ 64 := by omega
         have hx2 : (T.regs 9).toNat ≤ 64 := by omega
         have hv0 := hU0 hx0
         have hv1 := hU1 hx1
         have hv2 := hU2 hx2
         refine hk _ (by janus_simp) rfl hsp.symm (by janus_simp [h28]) (by janus_simp [h29]) (by janus_simp [h18])
           (by omega) (by omega) (by omega) (by omega) (by janus_simp; omega) (by janus_simp; omega) (by janus_simp; omega)
           ?_ ?_ ?_ <;>
         (janus_simp <;> (try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]) <;> (try split) <;> omega))
  next =>
    (
         have hcond : 1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2 := by
           first
           | exact err_of_big hL0' hL1' hL2' (by omega)
           | exact err_of_u hL0' hL1' hL2' (by omega) (by omega)
         rename_i ptr _ _ _ m _ _ hLFn hMFn hapL hinR hb48 hacc h8 h16 hz hround hapS hinvn
         have hpo : ptr.toNat + 16 ≤ s.sp.toNat - 4800 ∨ s.sp.toNat + 40 ≤ ptr.toNat := by
           have := InRanges.apart hinR hout; unfold Apart at this; omega
         janus_run [hm1, hm2]
         refine hErr _ hcond ⟨by janus_simp [hsp], by janus_simp [h28, hT28], by janus_simp [hT29, h29, hm2, regFP],
           by janus_simp [h18, hT18, regPlatform]⟩ ⟨by janus_simp, by janus_simp, by janus_simp⟩
           ⟨L1 ++ [(ptr.toNat, ptr.toNat + blockSize 16 (S.mem.readLE 2762984 8 == 0))],
            b1 - blockSize 16 (S.mem.readLE 2762984 8 == 0), ?_, ?_, ?_, ?_, ?_⟩
         · exact hext.trans (LiveExt.single (by simpa using hinR) (by simpa using hapL))
         · have := blockSize_le_allocCost 16 (S.mem.readLE 2762984 8 == 0)
           simp only [makeCost, allocCost, makeCap] at this hbud hcostE ⊢; omega
         · dsimp only
           have hI : ∀ a, ptr.toNat ≤ a → a + 8 ≤ ptr.toNat + 16 →
               InRanges a 8 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize 16 (S.mem.readLE 2762984 8 == 0))]) :=
             fun a h1 h2 => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩
           exact inv_store_live (inv_store_live hinvn (hI _ (Nat.le_refl _) (by omega))) (hI _ (by omega) (by omega))
         · dsimp only
           refine ⟨fun a n h => ?_, fun a n w => by simp only [Memory.accessible_writeLE, hMFn.accessible, hMF.accessible]⟩
           have h' := h
           simp only [win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h'
           have hd1 := InRanges.apart hinR h'.1
           unfold Apart at hd1
           rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
             hMFn.readLE _ _ (by
               simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
               exact ⟨h'.1, by omega, by omega⟩),
             hMF.readLE _ _ (by
               simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
               exact ⟨h'.1, by omega, by omega⟩)]
         · dsimp only
           have ho := hapL.outside
           refine hLF.trans (((hLFn.writeLE _ (ho.of_sub (Nat.le_refl _) (by omega))).writeLE _
             (ho.of_sub (by omega) (by omega)))) (fun _ _ h => hext.inRanges_old h)
         )
  next =>
    (
         have hcond : 1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2 := by
           first
           | exact err_of_big hL0' hL1' hL2' (by omega)
           | exact err_of_u hL0' hL1' hL2' (by omega) (by omega)
         rename_i ptr _ _ _ m _ _ hLFn hMFn hapL hinR hb48 hacc h8 h16 hz hround hapS hinvn
         have hpo : ptr.toNat + 16 ≤ s.sp.toNat - 4800 ∨ s.sp.toNat + 40 ≤ ptr.toNat := by
           have := InRanges.apart hinR hout; unfold Apart at this; omega
         janus_run [hm1, hm2]
         refine hErr _ hcond ⟨by janus_simp [hsp], by janus_simp [h28, hT28], by janus_simp [hT29, h29, hm2, regFP],
           by janus_simp [h18, hT18, regPlatform]⟩ ⟨by janus_simp, by janus_simp, by janus_simp⟩
           ⟨L1 ++ [(ptr.toNat, ptr.toNat + blockSize 16 (S.mem.readLE 2762984 8 == 0))],
            b1 - blockSize 16 (S.mem.readLE 2762984 8 == 0), ?_, ?_, ?_, ?_, ?_⟩
         · exact hext.trans (LiveExt.single (by simpa using hinR) (by simpa using hapL))
         · have := blockSize_le_allocCost 16 (S.mem.readLE 2762984 8 == 0)
           simp only [makeCost, allocCost, makeCap] at this hbud hcostE ⊢; omega
         · dsimp only
           have hI : ∀ a, ptr.toNat ≤ a → a + 8 ≤ ptr.toNat + 16 →
               InRanges a 8 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize 16 (S.mem.readLE 2762984 8 == 0))]) :=
             fun a h1 h2 => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩
           exact inv_store_live (inv_store_live hinvn (hI _ (Nat.le_refl _) (by omega))) (hI _ (by omega) (by omega))
         · dsimp only
           refine ⟨fun a n h => ?_, fun a n w => by simp only [Memory.accessible_writeLE, hMFn.accessible, hMF.accessible]⟩
           have h' := h
           simp only [win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h'
           have hd1 := InRanges.apart hinR h'.1
           unfold Apart at hd1
           rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
             hMFn.readLE _ _ (by
               simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
               exact ⟨h'.1, by omega, by omega⟩),
             hMF.readLE _ _ (by
               simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
               exact ⟨h'.1, by omega, by omega⟩)]
         · dsimp only
           have ho := hapL.outside
           refine hLF.trans (((hLFn.writeLE _ (ho.of_sub (Nat.le_refl _) (by omega))).writeLE _
             (ho.of_sub (by omega) (by omega)))) (fun _ _ h => hext.inRanges_old h)
         )
  next =>
    (
         have hx0 : (T.regs 6).toNat ≤ 64 := by omega
         have hx1 : (T.regs 7).toNat ≤ 64 := by omega
         have hx2 : (T.regs 9).toNat ≤ 64 := by omega
         have hv0 := hU0 hx0
         have hv1 := hU1 hx1
         have hv2 := hU2 hx2
         refine hZero _ (by omega) (by omega) (by omega) ⟨by janus_simp [hsp], by janus_simp [h28, hT28], by janus_simp [hT29, h29, hm2, regFP],
           by janus_simp [h18, hT18, regPlatform]⟩
           (by janus_simp) (by janus_simp) ⟨L1, b1, hext, by omega, ?_, ?_, ?_⟩
         · dsimp only; (try rw [hTm]); exact hinv
         · dsimp only; (try rw [hTm])
           refine ⟨fun a n h => hMF.readLE a n ?_, hMF.accessible⟩
           simp only [winA, win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
           exact ⟨h.1, by omega, by omega⟩
         · dsimp only; (try rw [hTm]); exact hLF)
  next =>
    (
         have hx0 : (T.regs 6).toNat ≤ 64 := by omega
         have hx1 : (T.regs 7).toNat ≤ 64 := by omega
         have hx2 : (T.regs 9).toNat ≤ 64 := by omega
         have hv0 := hU0 hx0
         have hv1 := hU1 hx1
         have hv2 := hU2 hx2
         refine hk _ (by janus_simp) rfl hsp.symm (by janus_simp [h28]) (by janus_simp [h29]) (by janus_simp [h18])
           (by omega) (by omega) (by omega) (by omega) (by janus_simp; omega) (by janus_simp; omega) (by janus_simp; omega)
           ?_ ?_ ?_ <;>
         (janus_simp <;> (try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]) <;> (try split) <;> omega))
  next =>
    (
         have hx0 : (T.regs 6).toNat ≤ 64 := by omega
         have hx1 : (T.regs 7).toNat ≤ 64 := by omega
         have hx2 : (T.regs 9).toNat ≤ 64 := by omega
         have hv0 := hU0 hx0
         have hv1 := hU1 hx1
         have hv2 := hU2 hx2
         refine hk _ (by janus_simp) rfl hsp.symm (by janus_simp [h28]) (by janus_simp [h29]) (by janus_simp [h18])
           (by omega) (by omega) (by omega) (by omega) (by janus_simp; omega) (by janus_simp; omega) (by janus_simp; omega)
           ?_ ?_ ?_ <;>
         (janus_simp <;> (try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]) <;> (try split) <;> omega))
  next =>
    (
         have hcond : 1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2 := by
           first
           | exact err_of_big hL0' hL1' hL2' (by omega)
           | exact err_of_u hL0' hL1' hL2' (by omega) (by omega)
         rename_i ptr _ _ _ m _ _ hLFn hMFn hapL hinR hb48 hacc h8 h16 hz hround hapS hinvn
         have hpo : ptr.toNat + 16 ≤ s.sp.toNat - 4800 ∨ s.sp.toNat + 40 ≤ ptr.toNat := by
           have := InRanges.apart hinR hout; unfold Apart at this; omega
         janus_run [hm1, hm2]
         refine hErr _ hcond ⟨by janus_simp [hsp], by janus_simp [h28, hT28], by janus_simp [hT29, h29, hm2, regFP],
           by janus_simp [h18, hT18, regPlatform]⟩ ⟨by janus_simp, by janus_simp, by janus_simp⟩
           ⟨L1 ++ [(ptr.toNat, ptr.toNat + blockSize 16 (S.mem.readLE 2762984 8 == 0))],
            b1 - blockSize 16 (S.mem.readLE 2762984 8 == 0), ?_, ?_, ?_, ?_, ?_⟩
         · exact hext.trans (LiveExt.single (by simpa using hinR) (by simpa using hapL))
         · have := blockSize_le_allocCost 16 (S.mem.readLE 2762984 8 == 0)
           simp only [makeCost, allocCost, makeCap] at this hbud hcostE ⊢; omega
         · dsimp only
           have hI : ∀ a, ptr.toNat ≤ a → a + 8 ≤ ptr.toNat + 16 →
               InRanges a 8 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize 16 (S.mem.readLE 2762984 8 == 0))]) :=
             fun a h1 h2 => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩
           exact inv_store_live (inv_store_live hinvn (hI _ (Nat.le_refl _) (by omega))) (hI _ (by omega) (by omega))
         · dsimp only
           refine ⟨fun a n h => ?_, fun a n w => by simp only [Memory.accessible_writeLE, hMFn.accessible, hMF.accessible]⟩
           have h' := h
           simp only [win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h'
           have hd1 := InRanges.apart hinR h'.1
           unfold Apart at hd1
           rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
             hMFn.readLE _ _ (by
               simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
               exact ⟨h'.1, by omega, by omega⟩),
             hMF.readLE _ _ (by
               simp only [winA, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
               exact ⟨h'.1, by omega, by omega⟩)]
         · dsimp only
           have ho := hapL.outside
           refine hLF.trans (((hLFn.writeLE _ (ho.of_sub (Nat.le_refl _) (by omega))).writeLE _
             (ho.of_sub (by omega) (by omega)))) (fun _ _ h => hext.inRanges_old h)
         )


end FvModexp.Arm64.Run
