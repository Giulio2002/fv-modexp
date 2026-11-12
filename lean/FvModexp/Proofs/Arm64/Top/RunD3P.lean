import FvModexp.Proofs.Arm64.Top.RunD2Lem
import FvModexp.Proofs.Arm64.Top.RunGS
import FvModexp.Proofs.Arm64.Top.RunD3J
import FvModexp.Proofs.Arm64.Top.RunArith
import FvModexp.Proofs.Arm64.Top.RunBox
import FvModexp.Proofs.Arm64.Top.RunDSlot

/-! # `Run` (arm64): `D1` to `J2`, exponent operand longer than the input rest, at most 32 bytes: stack buffer, `memmove` -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem d3p (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelD R b L c p len cp s ret 2 L1 b1 S)
    (hpc : S.pc = BitVec.ofNat 64 pcD2)
    (hndir : len.toNat - 96 < min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2) (hsm : hdrV s p len 2 ≤ 32)
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 3 L2 b2 S2 →
      (S2.regs 0).toNat = S2.mem.readLE (s.sp.toNat - 192) 8 → (S2.regs 1).toNat = S2.mem.readLE (s.sp.toNat - 184) 8 →
      S2.pc = BitVec.ofNat 64 pcD3 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
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
    gS_read hMF hga hgr
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
  have hmv' : MemmoveLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmv
  have hc : (len.toNat - 96 < min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) + hdrV s p len 2) = True := by simp; omega
  have hc32 : (32 < hdrV s p len 2) = False := by simp; omega
  have hIe := toInt_small (BitVec.ofNat 64 (hdrV s p len 2)) (by simp; omega)
  obtain ⟨off, hoffd⟩ : ∃ off, inOff len = off := ⟨_, rfl⟩
  have hoffc : (96 < len.toNat ∧ off = 96) ∨ (len.toNat ≤ 96 ∧ off = 0) := by
    subst hoffd; simp only [inOff]; split <;> omega
  rw [hoffd] at hs5 hs6
  have hcap : min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) ≤ cp.toNat - off := cap_le _ _ _ _ (Nat.min_le_right _ _) hlcp hoffc
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
    bv_sub_of_le _ _ (Nat.min_le_right _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) len.isLt)
  have hcsub : BitVec.ofNat 64 (cp.toNat - off) - BitVec.ofNat 64 (min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) =
      BitVec.ofNat 64 (cp.toNat - off - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) :=
    bv_sub_of_le _ _ hcap (Nat.lt_of_le_of_lt (Nat.sub_le _ _) cp.isLt)
  obtain ⟨hr1, hr2, hr3⟩ := rng_le p.toNat len.toNat off mN _ hmN.1 (Nat.min_le_right _ _) hoffc hmN.2
  have hsrc : BitVec.ofNat 64 mN + BitVec.ofNat 64 (p.toNat + off) = BitVec.ofNat 64 (p.toNat + off + mN) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := mN) (by omega), Nat.mod_eq_of_lt (a := p.toNat + off) (by omega),
      Nat.mod_eq_of_lt (a := p.toNat + off + mN) (by omega)]; omega
  have hIa := toInt_small (BitVec.ofNat 64 (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96))) (by simp; omega)
  have hmvok : R.ok (cA "runtime.memmove") [s.sp.toNat - 456, p.toNat + off + mN,
      len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)] := hokM _ _ _ (by omega)
  have hsA : s.mem.accessible (p.toNat + off + mN) (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) false
      = true := Memory.accessible_mono _ hpacc hr1 hr2
  have hne : (BitVec.toNat s.sp - 456 = p.toNat + off + mN) = False := stk_ne _ _ _ _ _ _ hpw hr3 hb' (by decide) (by decide)
  have hpo' : Outside p.toNat len.toNat (winA s stk 40) := by
    simp only [winA, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hco' : Outside c.toNat 3 (winA s stk 40) := by
    simp only [winA, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hsw1 : p.toNat + off + mN + (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) ≤ BitVec.toNat s.sp - 624 - 4096 ∨
      BitVec.toNat s.sp - 624 - 8 ≤ p.toNat + off + mN := by omega
  have hsw2 : p.toNat + off + mN + (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)) ≤ BitVec.toNat s.sp - 624 + 8 ∨
      BitVec.toNat s.sp - 624 + 8 + 24 ≤ p.toNat + off + mN := by omega
  have bxo := Box.mk (And.intro hpo' hco')
  have bxp := Box.mk (And.intro hpw hcw)
  clear hpo' hco' hpw hcw
  set_option janus.callRegions true in
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hk1a, hk1b, hk2a, hS1, hS1n, hadd, hmod, hc, hc32, hIe, hIa, hmask, hsub,
    hcsub, hsrc, hne, toInt_ite, toNat_ite, toInt_small] until [segAddr Extracted.program fn + 0x728] calls [hmv']
  rename_i m _ _ hMFm hLFm hinvm hcp
  have bxq := Box.mk (And.intro hoffc (And.intro hmN (And.intro hsw1 hsw2))); have bxnz := Box.mk hnz
  have bxga := Box.mk hga
  clear hoffc hmN hsw1 hsw2 hnz hga
  have hMFm' := hMFm
  rw [List.append_assoc] at hMFm'
  have hd1 := dataLoaded_win (lo := s.sp.toNat - 4800) (n := 4800 + 40) ?d0 (by rw [hrg1]; simp) hro hMFm' ?wacc ?ws
  case d0 => janus_callpre
  case wacc => simpa only [Memory.accessible_writeLE] using hwS
  case ws =>
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
  clear hdS
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hk1a, hk1b, hk2a, hS1, hS1n, hadd, hmod, hk2a, hS1, hS1n, hadd, hmod] until [pcJ3]
  have hstk : stk = 4800 := rfl
  have hLsL1 : LiveSep L1 (win s 4800 40) := hLs0
  have hMF2 : MemFrame s.mem m (R.rt ++ winA s stk 40) := by
    simp only [winA, stk] at hMF ⊢
    refine (hMF.trans ?w1 fun a n h => ⟨h, out_wA h⟩).trans hMFm fun a n h => ⟨h, out_csw hb' (by omega) (by omega) h⟩
    case w1 => janus_frame
  have hdst : LiveSep L1 [(BitVec.toNat s.sp - 456, BitVec.toNat s.sp - 456 +
      (len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96)))] := by
    intro r hr; have := hLsS r hr
    simp only [Outside, and_true] at this ⊢; omega
  have hLFS : LiveFrame S.mem m L1 [] :=
    (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans (LiveFrame.drop hLFm hdst) (fun _ _ h => h)
  have hLF2 : LiveFrame s.mem m L [] := hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)
  have hLx := LiveFrame.of_nil' hLF2 (winA s stk 40)
  have hpo' := bxo.h.1
  have hco' := bxo.h.2
  refine d3join impl hap R hmk hokS b L c p len cp ret hret s henv0 hin0 Q hbudD hk _ L1 b1 (s.sp.toNat - 456)
    ?hj (by janus_simp)
  case hj =>
  refine ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29], by janus_simp [h18],
     by janus_simp [hm1], by janus_simp [hm2], by janus_simp [hm3], by janus_simp [hm4], by janus_simp [hm5],
     by janus_simp [hm6], by janus_simp [hs1], by janus_simp [hs2], by janus_simp [hs3], by janus_simp [hs4],
     by janus_simp [hs5, hoffd], by janus_simp [hs6, hoffd], by janus_simp [hk1a], by janus_simp [hk1b], by janus_simp [hk2a],
     by janus_simp, by janus_simp, by janus_simp, hl0, hl1, hl2, bxnz.h,
     by janus_simp, (by janus_simp [hs3] <;> omega), by omega,
     (Memory.accessible_read_of_write _ (Memory.accessible_mono _ hw (by omega) (by omega))),
     Or.inr (hout.of_sub (by omega) (by omega)), (by omega), ?bytes, hd1,
     fun a n h1 h2 => (hheld.sub h1 h2).readLE hMF2 hLx (hpo'.of_sub h1 (by omega)),
     hcheld.readLE hMF2 hLx hco', hext, (by simp only [dCost, allocCost] at hbud ⊢; omega), hinvm, hLsL1, hMF2, hLF2,
     OpDone.transportS (hop 0 (by omega)) (k := 2) (by omega) (by intro a n h1 h2; simp only [opAt] at h1 h2; janus_simp) hLFS (fun _ _ h => h),
     OpDone.transportS (hop 1 (by omega)) (k := 2) (by omega) (by intro a n h1 h2; simp only [opAt] at h1 h2; janus_simp) hLFS (fun _ _ h => h), OpsApart.transportS hopA (by intro a n h1 h2; simp only [opAt] at h1 h2; janus_simp)⟩
  case bytes =>
    intro j hj
    unfold padByte
    split
    · rename_i hjl
      have hpw := bxp.h.1; have hoffc := bxq.h.1; have hmN := bxq.h.2.1
      have hn0 : 0 < len.toNat - 96 - min (hdrV s p len 1 + hdrV s p len 0) (len.toNat - 96) := by omega
      obtain ⟨-, rfl⟩ : 96 < len.toNat ∧ off = 96 := by omega
      have hmE : mN = hdrV s p len 1 + hdrV s p len 0 := by omega
      have hcj := hcp j (by omega)
      rw [hcj, ← Memory.readLE_one, hmE]
      repeat rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hinS _ _ (by omega) (by omega), Memory.readLE_one, show p.toNat + 96 + (hdrV s p len 1 + hdrV s p len 0) + j =
        p.toNat + (96 + (hdrV s p len 0 + hdrV s p len 1) + j) by omega]
    · rename_i hjl
      rw [← Memory.readLE_one, hMFm.readLE _ _ (by
        simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
        exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)]
      rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ 24 ≤ j) with h | h | h | h <;>
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_inside, Nat.zero_div,
        Nat.zero_mod]

end FvModexp.Arm64.Run
