import FvModexp.Proofs.Amd64.Nat.StackNatJ
import FvModexp.Proofs.Common.DivmcBits

/-!
# `(*stack).nat` (amd64): `+0x101` (`s.w`'s pointer store, after the write barrier) … return
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.StackNat

/-- registers kept by the call (callee-saved part of the Go ABI) -/
@[reducible] def RegsOK (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15

theorem x0_eq (w len : Nat) (n : BitVec 64) (hw : w + 8 * len < 2 ^ 64) (hl : len < 2 ^ 61) (hn : 0 < n.toNat)
    (hn' : n.toNat < 2 ^ 63) :
    BitVec.ofNat 64 w + ((0#64 - n).sshiftRight 63 &&& BitVec.ofNat 64 len <<< 3) = BitVec.ofNat 64 (w + 8 * len) := by
  rw [neg_sshr63_and n _ hn (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tail (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st n : BitVec 64) (s : State)
    (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (M M2 : Janus.Arm64.Memory) (h : J R b L st.toNat n.toNat s L1 b1 w1 c1 M)
    (hf : MemFrame M M2 (R.rt ++ [(st.toNat, st.toNat + 24), ((s.regs 4).toNat - 4192, (s.regs 4).toNat - 88)]))
    (hl : LiveFrame M M2 L1 [(st.toNat, st.toNat + 24)])
    (hinv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M2))
    (hlen : M2.readLE (st.toNat + 8) 8 = stLen s.mem st.toNat) (hcap : M2.readLE (st.toNat + 16) 8 = c1)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 pS) (hsp : S.regs 4 = s.regs 4 - 88#64) (h0 : S.regs 0 = st)
    (h3 : S.regs 3 = n) (h1 : S.regs 1 = BitVec.ofNat 64 c1)
    (h6 : S.regs 6 = BitVec.ofNat 64 (stLen s.mem st.toNat + rnd n.toNat)) (h8 : S.regs 8 = BitVec.ofNat 64 w1)
    (h2 : S.regs 2 = BitVec.ofNat 64 (stLen s.mem st.toNat)) (h14 : S.regs 14 = s.regs 14)
    (h5 : S.regs 5 = s.regs 4 - 8#64) (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hm : S.mem = M2) :
    ReachesRet (LibStackNat.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ Post R b L 4192 24 st.toNat n.toNat s s' := by
  have hpre := h.pre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩, hsv, hok, hstw, harr, hn16, hln,
    hcost, hinv0, hwb, hwbA, hfa⟩ := hpre
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hcb⟩ := hok
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hc1len := h.c1len
  have hc1b := h.c1b
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hsp88 : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hra : M2.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hf.readLE _ _ ?_]; exact h.ra
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have hbp : M2.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hf.readLE _ _ ?_]; exact h.bp
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have hstacc2 : M2.accessible st.toNat 24 true = true := by
    rw [hf.accessible, h.mf.accessible]; exact hstacc
  have hacc8a : M2.accessible st.toNat 8 true = true := Janus.Arm64.Memory.accessible_mono _ hstacc2 (by omega) (by omega)
  have hacc8b : M2.accessible (st.toNat + 8) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hstacc2 (by omega) (by omega)
  have hsacc : M2.accessible ((s.regs 4).toNat - 4192) (4192 + 24) true = true := by
    rw [hf.accessible, h.mf.accessible]; exact hw
  have hra47 := h.ra47
  have hnr1 : n.toNat ≤ rnd n.toNat := by simp only [rnd]; omega
  have hnr2 : rnd n.toNat ≤ n.toNat + 3 := by simp only [rnd]; omega
  by_cases hn0 : n.toNat = 0
  · janus64_run [hm, hsp88, hra, hbp, hacc8a, hacc8b, BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun h0 => absurd h0 (by omega), ?_, ?_,
      post_fin h hf hl hinv 0 (by omega) (fun h => absurd h (by omega)) ?_ ?_ ?_ ?_⟩
    all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14, hx15, hfs, h3, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
    all_goals first
      | with_reducible rfl
      | (simp only [List.replicate]; janus_frame)
      | (rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hcap])
      | (rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hcap])
      | (rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := h.w64; omega)])
      | (rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := h.w64; omega)])
      | (rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := h.w64; omega)])
      | rfl
  · have hc0 : 0 < c1 := by omega
    obtain ⟨hw8, hwh, hwacc, hw48⟩ := h.wl hc0
    have hwacc2 : M2.accessible (w1 + 8 * stLen s.mem st.toNat) 8 true = true := by
      rw [hf.accessible, h.mf.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
    have hwW := h.wwin hc0
    simp only [win, outside_cons, outside_nil, and_true] at hwW
    have hha := h.hdr (by omega)
    unfold Apart at hha
    have hw64 := h.w64
    have hx0 := x0_eq w1 (stLen s.mem st.toNat) n (by omega) (by omega) (by omega) (by omega)
    janus64_run [hm, hsp88, hra, hbp, hacc8a, hacc8b, hwacc2, hx0, BitVec.msb_eq_decide]
    have hrd : (((M2.writeLE st.toNat 8 w1).writeLE (st.toNat + 8) 8 (stLen s.mem st.toNat + rnd n.toNat)).writeLE
        (w1 + 8 * stLen s.mem st.toNat) 8 1043915).readLE st.toNat 8 = w1 := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun _ => ?_, ?_, ?_, post_fin h hf hl hinv 1 (by omega) (fun _ => by omega) ?_ hrd ?_ ?_⟩
    all_goals try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, h14, hx15, hfs, h3, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, stW]
    all_goals first
      | with_reducible rfl
      | (simp only [List.replicate]; janus_frame)
      | (rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hcap])
      | (rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hcap])
      | (rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := h.w64; omega)])
      | (rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := h.w64; omega)])
      | (rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by have := h.w64; omega)])
      | (rw [hrd]; done)
      | rfl

end FvModexp.Amd64.StackNat
