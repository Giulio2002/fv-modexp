import FvModexp.Proofs.Arm64.Nat.StackNatJ

/-!
# `(*stack).nat` (arm64): `+0xec` (`s.w`'s pointer store, after the write barrier) … return

`MOVD R6, (R0)`; `s.w = s.w[:off+nr]` (`CMP R5, R2`, `MOVD R5, 8(R0)`); `x := s.w[off : off+n : off+n]` (bounds checks,
masked pointer `R0 = R6 + 8·(off & -(n>0))`); `if n > 0 { x[0] = 0xfedcb }`; `R2 = R1`; epilogue.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.StackNat

theorem x0_eq (w len : Nat) (n : BitVec 64) (hw : w + 8 * len < 2 ^ 64) (hl : len < 2 ^ 61) (hn : 0 < n.toNat)
    (hn' : n.toNat < 2 ^ 63) :
    BitVec.ofNat 64 w + (BitVec.ofNat 64 len &&& (0#64 - n).sshiftRight 63) <<< 3 = BitVec.ofNat 64 (w + 8 * len) := by
  have hm := sliceMask_lt len 0#64 n (by simp; omega) hn' (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega), hm, Nat.shiftLeft_eq]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tail (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (M M2 : Memory) (h : J R b L st.toNat n.toNat s L1 b1 w1 c1 M)
    (hf : MemFrame M M2 (R.rt ++ [(st.toNat, st.toNat + 24), (s.sp.toNat - 4208, s.sp.toNat - 120)]))
    (hl : LiveFrame M M2 L1 [(st.toNat, st.toNat + 24)])
    (hinv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M2))
    (hlen : M2.readLE (st.toNat + 8) 8 = stLen s.mem st.toNat) (hcap : M2.readLE (st.toNat + 16) 8 = c1)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 pS) (hsp : S.sp = s.sp - 112#64) (h0 : S.regs 0 = st)
    (h1 : S.regs 1 = n) (h2 : S.regs 2 = BitVec.ofNat 64 c1)
    (h5 : S.regs 5 = BitVec.ofNat 64 (stLen s.mem st.toNat + rnd n.toNat)) (h6 : S.regs 6 = BitVec.ofNat 64 w1)
    (h7 : S.regs 7 = BitVec.ofNat 64 (stLen s.mem st.toNat)) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 120#64) (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M2) :
    ReachesRet (LibStackNat.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L 4208 24 st.toNat n.toNat s s' := by
  have hpre := h.pre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, hwb⟩ := hpre
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hcb⟩ := hok
  have hc1len := h.c1len
  have hc1b := h.c1b
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hsp112 : (s.sp - 112#64).toNat = s.sp.toNat - 112 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hlr : M2.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat := by
    rw [hf.readLE _ _ ?_]; exact h.lr
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have hfp : M2.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat := by
    rw [hf.readLE _ _ ?_]; exact h.fp
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have hstacc2 : M2.accessible st.toNat 24 true = true := by
    rw [hf.accessible, h.mf.accessible]; exact hstacc
  have hacc8a : M2.accessible st.toNat 8 true = true := Memory.accessible_mono _ hstacc2 (by omega) (by omega)
  have hacc8b : M2.accessible (st.toNat + 8) 8 true = true := Memory.accessible_mono _ hstacc2 (by omega) (by omega)
  have hsacc : M2.accessible (s.sp.toNat - 4208) (4208 + 24) true = true := by
    rw [hf.accessible, h.mf.accessible]; exact hw
  have hlr4 := h.lr4
  have hlr48 := h.lr48
  have hnr1 : n.toNat ≤ rnd n.toNat := by simp only [rnd]; omega
  have hnr2 : rnd n.toNat ≤ n.toNat + 3 := by simp only [rnd]; omega
  by_cases hn0 : n.toNat = 0
  · janus_run [hm, hsp112, hlr, hfp, hacc8a, hacc8b]
    refine ⟨fun h0 => absurd h0 (by omega), ?_, ?_,
      post_fin h hf hl hinv 0 (by omega) (fun h => absurd h (by omega)) ?_ ?_ ?_ ?_⟩
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [List.replicate]; janus_frame
    · dsimp only
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := h.w64; omega)]
    · dsimp only
      rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    · dsimp only
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), hcap]
  · have hc0 : 0 < c1 := by omega
    obtain ⟨hw8, hwh, hwacc, hw48⟩ := h.wl hc0
    have hwacc2 : M2.accessible (w1 + 8 * stLen s.mem st.toNat) 8 true = true := by
      rw [hf.accessible, h.mf.accessible]; exact Memory.accessible_mono _ hwacc (by omega) (by omega)
    have hmask := sliceMask_lt (stLen s.mem st.toNat) 0#64 n (by simp; omega) (by omega) (by omega)
    have hwW := h.wwin hc0
    simp only [win, outside_cons, outside_nil, and_true] at hwW
    have hha := h.hdr (by omega)
    unfold Apart at hha
    have hw64 := h.w64
    janus_run [hm, hsp112, hlr, hfp, hacc8a, hacc8b, hmask, hwacc2]
    have hrd : (((M2.writeLE st.toNat 8 w1).writeLE (st.toNat + 8) 8 (stLen s.mem st.toNat + rnd n.toNat)).writeLE
        (w1 + 8 * stLen s.mem st.toNat) 8 1043915).readLE st.toNat 8 = w1 := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    refine ⟨fun _ => ?_, ?_, ?_, post_fin h hf hl hinv 1 (by omega) (fun _ => by omega) ?_ hrd ?_ ?_⟩
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, stW]
      rw [hrd]
      exact x0_eq w1 _ n (by omega) (by omega) (by omega) (by omega)
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [List.replicate]; janus_frame
    · dsimp only
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    · dsimp only
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), hcap]

end FvModexp.Arm64.StackNat
