import FvModexp.Proofs.Amd64.Nat.StackNatXG3

set_option autoImplicit false

/-!
# `(*stack).nat` (amd64): the `growslice` call of `slices.Grow` → the `memclrNoHeapPointers` call (`g3`)

After `growslice` returns (`+0x85`): `R9 = 0x40(SP')` (num), `R8 = AX` (the block), `R10 = BX` (newLen);
`0x30(SP') = CX` (the new capacity), `0x48(SP') = R8`; `AX = R8 + 8·(newLen - num)`, `BX = 8·num`; `CALL memclr`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.StackNatX

open FvModexp.Amd64.StackNat (fn names wbA rnd)

/-- the return site of the `growslice` call -/
abbrev pGR : Nat := segAddr Extracted.program fn + 0x85

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem g2 (impl : List Amd64.Segment) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (LibStackNat.program.link impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibStackNat.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (LibStackNat.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15s : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (hpre : PreX R b L 4192 24 st.toNat n.toNat s)
    (hk : stCap s.mem st.toNat < stLen s.mem st.toNat + rnd n.toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 (cA "runtime.growslice")) (hsp : S.regs 4 = s.regs 4 - 96#64)
    (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64) (hx15 : S.xmm 15 = s.xmm 15)
    (hfs : S.fsBase = s.fsBase) (hdf : S.df = false)
    (sret : S.mem.readLE ((s.regs 4).toNat - 96) 8 = 6186245)
    (h0 : (S.regs 0).toNat = stW s.mem st.toNat) (h3 : S.regs 3 = BitVec.ofNat 64 (stLen s.mem st.toNat + rnd n.toNat))
    (h1 : (S.regs 1).toNat = stCap s.mem st.toNat)
    (h7 : (S.regs 7).toNat = stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat) (h6 : (S.regs 6).toNat = wT)
    (hF : MemFrame s.mem S.mem (win s 4192 24))
    (sra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (sbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (s30 : S.mem.readLE ((s.regs 4).toNat - 48) 8 = stLen s.mem st.toNat)
    (s20 : S.mem.readLE ((s.regs 4).toNat - 32) 8 = rnd n.toNat)
    (s18 : S.mem.readLE ((s.regs 4).toNat - 24) 8 = stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat)
    (sst : S.mem.readLE ((s.regs 4).toNat + 8) 8 = st.toNat) (sn : S.mem.readLE ((s.regs 4).toNat + 16) 8 = n.toNat) :
    ReachesRet (LibStackNat.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostXL R b L 4192 24 st.toNat n.toNat s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr', hLs, hro, htls⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, -⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok
  have hnr : rnd n.toNat ≤ n.toNat + 3 := by simp only [rnd]; omega
  have hsp96 : (S.regs 4).toNat = (s.regs 4).toNat - 96 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have h3' : (S.regs 3).toNat = stLen s.mem st.toNat + rnd n.toNat := by
    rw [h3, BitVec.toNat_ofNat]; simp only [stLen] at hln ⊢; omega
  refine ReachesRet.call (hgr L b) hpc (gcall_pre hpre hk S hF (by omega) h14 (by rw [hsp96, sret]; decide)
    h0 h3' h1 h7 h6) ?_
  intro S1 hpc1 ⟨ptr, junk, f1, x1, yh1, m1, zh1, kr1, hs1, hMF, hLF, ⟨hobj, hapL⟩, hapS, hinv1⟩
  subst hs1
  have hround : growsliceRound64 S = 8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat) := by
    simp only [growsliceRound64, h3', h1]
  simp only [growsliceObj64, Fresh, h3', h1, h7, hround] at hobj
  rw [hround] at hapL hinv1
  obtain ⟨⟨hpin, hp48, hpacc, hal8, -, -, -⟩, -, -⟩ := hobj
  have hgcl := le_growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat)
  have hgcb := growCap_lt (stLen s.mem st.toNat) n.toNat (stCap s.mem st.toNat) hk (by omega)
  have hpw := hpin.apart hout
  unfold Apart at hpw
  simp only [calleeStack64, hsp96] at hMF
  have hrd : ∀ a, ((s.regs 4).toNat - 48 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 24) →
      m1.readLE a 8 = S.mem.readLE a 8 := by
    intro a ha
    refine hMF.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have r30 := (hrd _ (by omega)).trans s30
  have r20 := (hrd _ (by omega)).trans s20
  have r18 := (hrd _ (by omega)).trans s18
  have rst := (hrd _ (by omega)).trans sst
  have rn := (hrd _ (by omega)).trans sn
  have rra := (hrd _ (by omega)).trans sra
  have rbp := (hrd _ (by omega)).trans sbp
  have hret : retAddrOf S = 6186245#64 := by
    simp only [retAddrOf, hsp96, sret]
  have hsp88 : (s.regs 4 - 96#64 + 8#64).toNat = (s.regs 4).toNat - 88 := by
    rw [← hsp, BitVec.toNat_add, hsp96]; simp only [BitVec.toNat_ofNat]; omega
  rw [hret] at hpc1
  have hgc64 : growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat) < 2 ^ 64 := by omega
  have hp64 : ptr.toNat < 2 ^ 64 := ptr.isLt
  have esub : BitVec.ofNat 64 (stLen s.mem st.toNat + rnd n.toNat) -
      BitVec.ofNat 64 (stLen s.mem st.toNat + rnd n.toNat - stCap s.mem st.toNat) =
      BitVec.ofNat 64 (stCap s.mem st.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [stLen, stCap] at hln hk ⊢; omega
  janus64_run [r30, r20, r18, rst, rn, hsp88, hsp, h5, h3, esub, h1] until [cA "runtime.memclrNoHeapPointers"]
  have hLw : LiveSep L (win s 4192 24) := hLs
  generalize hM2 : ((m1.writeLE ((s.regs 4).toNat - 40) 8
      (growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))).writeLE ((s.regs 4).toNat - 16) 8
      ptr.toNat).writeLE ((s.regs 4).toNat - 96) 8 6186285 = M2
  have hst2 : MemFrame m1 M2 [((s.regs 4).toNat - 40, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 16,
      (s.regs 4).toNat - 8), ((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)] := by rw [← hM2]; janus_frame
  have hwr : LiveSep [((s.regs 4).toNat - 40, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 16, (s.regs 4).toNat - 8),
      ((s.regs 4).toNat - 96, (s.regs 4).toNat - 88)] R.rt := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)
  have hF1 : MemFrame s.mem m1 (R.rt ++ win s 4192 24) := by
    refine MemFrame.trans hF hMF fun a k ho => ?_
    simp only [win, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨hrt, h1⟩ := ho
    exact ⟨h1, hrt, by omega, by omega⟩
  have hF2 := hF1.trans hst2 fun a k ho => by
    refine ⟨ho, ?_⟩
    simp only [win, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hLF2 : LiveFrame s.mem M2 L [] := by
    refine ⟨fun a k hin _ => ?_⟩
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLw r hr
    simp only [win, outside_cons, outside_nil, and_true] at this
    rw [hst2.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hLF.readLE a k ⟨r, hr, h1, h2⟩ trivial, hF.readLE a k (by simp only [win, outside_cons, outside_nil, and_true]; omega)]
  have hpacc2 : M2.accessible ptr.toNat (8 * growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat))
      true = true := by
    rw [← hM2]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hpacc
  have hinv2 := RtInv.inv_frame hst2 hwr hinv1
  rw [h14] at hinv2
  have qk : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat - 32 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 16 ∨ (s.regs 4).toNat - 8 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 96 ∨ (s.regs 4).toNat - 88 ≤ a) → M2.readLE a 8 = m1.readLE a 8 := fun a h1 h2 h3 => by
    rw [← hM2, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have q28 : M2.readLE ((s.regs 4).toNat - 40) 8 = growCap8 (stLen s.mem st.toNat + rnd n.toNat) (stCap s.mem st.toNat) := by
    rw [← hM2, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (by omega)]
  have q10 : M2.readLE ((s.regs 4).toNat - 16) 8 = ptr.toNat := by
    rw [← hM2, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (by omega)]
  have qret : M2.readLE ((s.regs 4).toNat - 96) 8 = pMR := by
    rw [← hM2, Janus.Arm64.Memory.readLE_writeLE_self]; rfl
  refine g3 impl R hmc hwb b L st n s hra hx15s hdf0 hpre hk ptr.toNat hpin hp48 (hal8 (Or.inr (by omega))) hapL _ rfl
    ?_ ?_ ?_ ?_ hfs ?_ qret ?_ ?_ hF2 hLF2 hpacc2 hinv2 ?_ ?_ ?_ q28 ?_ q10 ?_ ?_
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  · simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or]; exact h5
  · simp only [hx15s, ↓reduceIte]
  · first | exact hdf | (simp only [hdf]) | janus64_simp
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp only [stLen, stCap] at hln hk ⊢; omega
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    simp only [stLen, stCap] at hln hk ⊢; omega
  · exact (qk _ (by omega) (by omega) (by omega)).trans rra
  · exact (qk _ (by omega) (by omega) (by omega)).trans rbp
  · exact (qk _ (by omega) (by omega) (by omega)).trans r30
  · exact (qk _ (by omega) (by omega) (by omega)).trans r20
  · exact (qk _ (by omega) (by omega) (by omega)).trans rst
  · exact (qk _ (by omega) (by omega) (by omega)).trans rn

end FvModexp.Amd64.StackNatX
