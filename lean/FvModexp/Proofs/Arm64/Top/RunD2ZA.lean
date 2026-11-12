import FvModexp.Proofs.Arm64.Top.RunD2ZDefs
import FvModexp.Proofs.Arm64.Top.RunGS

/-! # `Run` (arm64): `D1` to `Z2`, exponent operand of more than 32 bytes with no input byte left: the `makeslice`
buffer of `RightPadBytes` (see `RunD2ZDefs`) -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem d2zA (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelD R b L c p len cp s ret 1 L1 b1 S)
    (hpc : S.pc = BitVec.ofNat 64 pcD1)
    (hndir : len.toNat - 96 < min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1) (hlg : 32 < hdrV s p len 1)
    (hz0 : len.toNat - 96 - min (hdrV s p len 0) (len.toNat - 96) = 0)
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
    (hkZ : ∀ U Lk bk B src, JoinZ2 R b L c p len cp s ret Lk bk B src U → U.pc = BitVec.ofNat 64 pcZ2 →
      Reaches ((LibRun.program.link impl).withExit ret) U Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  have henv0 := henv
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hl0, hl1, hl2, hnz, hk1, -,
    hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF, hLF, hop, hopA⟩ := hrel
  obtain ⟨hk1a, hk1b⟩ := hk1 (Nat.le_refl _)
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
  have hMC0 : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1))) ≤ allocCost (8 * 132) := by
    have h1 : SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1)) ≤ 128 := by simp [SetBytes.nW]; omega
    have h3 : makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1))) ≤ 132 := by unfold makeCap; split <;> omega
    simp only [makeCost, allocCost]; omega
  have hMC : makeCost (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1))) ≤ b1 := by
    simp only [dCost, allocCost] at hbudD hbud hMC0 ⊢; omega
  have hokm : R.ok (cA "runtime.makeslice") [2641088, SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1)),
      makeCap (SetBytes.nW (BitVec.ofNat 64 (hdrV s p len 1)))] := hokS _ (by simp [SetBytes.nW]; omega)
  have hc : (len.toNat - 96 < min (hdrV s p len 0) (len.toNat - 96) + hdrV s p len 1) = True := by simp; omega
  have hc32 : (32 < hdrV s p len 1) = True := by simp; omega
  have hIe := toInt_small (BitVec.ofNat 64 (hdrV s p len 1)) (by simp; omega)
  obtain ⟨off, hoffd⟩ : ∃ off, inOff len = off := ⟨_, rfl⟩
  have hoffc : (96 < len.toNat ∧ off = 96) ∨ (len.toNat ≤ 96 ∧ off = 0) := by
    subst hoffd; simp only [inOff]; split <;> omega
  rw [hoffd] at hs5 hs6
  have hcap : min (hdrV s p len 0) (len.toNat - 96) ≤ cp.toNat - off := by omega
  obtain ⟨mN, hmNd⟩ : ∃ mN, (if min (hdrV s p len 0) (len.toNat - 96) < cp.toNat - off then
      min (hdrV s p len 0) (len.toNat - 96) else 0) = mN := ⟨_, rfl⟩
  have hmN : mN ≤ min (hdrV s p len 0) (len.toNat - 96) ∧
      (len.toNat - 96 - min (hdrV s p len 0) (len.toNat - 96) = 0 ∨ mN = min (hdrV s p len 0) (len.toNat - 96)) := by
    subst hmNd; split <;> omega
  have hmask : (BitVec.ofNat 64 (min (hdrV s p len 0) (len.toNat - 96)) &&&
      (BitVec.ofNat 64 (min (hdrV s p len 0) (len.toNat - 96)) - BitVec.ofNat 64 (cp.toNat - off)).sshiftRight 63) =
      BitVec.ofNat 64 mN := by
    apply BitVec.eq_of_toNat_eq
    rw [sliceMask_le _ _ hcap (by omega), hmNd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : BitVec.ofNat 64 (len.toNat - 96) - BitVec.ofNat 64 (min (hdrV s p len 0) (len.toNat - 96)) =
      BitVec.ofNat 64 (len.toNat - 96 - min (hdrV s p len 0) (len.toNat - 96)) :=
    bv_sub_of_le _ _ (Nat.min_le_right _ _) (by omega)
  have hcsub : BitVec.ofNat 64 (cp.toNat - off) - BitVec.ofNat 64 (min (hdrV s p len 0) (len.toNat - 96)) =
      BitVec.ofNat 64 (cp.toNat - off - min (hdrV s p len 0) (len.toNat - 96)) :=
    bv_sub_of_le _ _ hcap (by omega)
  have hsrc : BitVec.ofNat 64 mN + BitVec.ofNat 64 (p.toNat + off) = BitVec.ofNat 64 (p.toNat + off + mN) :=
    bv_add_of_lt _ _ (by omega)
  have hpast : len.toNat ≤ 96 + hdrV s p len 0 := by omega
  have hsrcb : p.toNat ≤ p.toNat + off + mN ∧ p.toNat + off + mN ≤ p.toNat + len.toNat := by omega
  have hpo' : Outside p.toNat len.toNat (winA s stk 40) := outA_of hpw
  have hco' : Outside c.toNat 3 (winA s stk 40) := outA_of hcw
  have hIa := toInt_small (BitVec.ofNat 64 (len.toNat - 96 - min (hdrV s p len 0) (len.toNat - 96))) (by simp; omega)
  have hmk' : MakesliceLiveContract (LibRun.program.link impl) (cA "runtime.makeslice") 4096 R :=
    MakesliceLiveContract.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmk
  have hmkP := hmk'.pos L1 b1
  janus_eval_nat h_u : uint8T
  have hokb : R.ok (cA "runtime.makeslice") [uint8T, hdrV s p len 1, hdrV s p len 1] := hokB _ (by omega)
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
  have hBS : blockSize (hdrV s p len 1) true ≤ b1 := by
    have := blockSize_le_allocCost (hdrV s p len 1) true
    simp only [allocCost, dCost, makeCost, makeCap] at this hbudD hbud ⊢; omega
  set_option janus.callRegions true in
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hk1a, hk1b, hc, hc32, hIe, hIa, hmask, hsub,
    hcsub, hsrc, hU2, hU3, toInt_ite, toNat_ite, toInt_small] until [segAddr Extracted.program fn + 0x5cc] calls [hmkP]
  rename_i ptr _ _ _ mk _ _ hLFk hMFk hapk hink hbk hack h8k h16k hzk hrk hapSk hinvk
  have hdk := dataLoaded_win (lo := s.sp.toNat - 4800) (n := 4800 + 40) ?d0 (by rw [hrg1]; simp) hro hMFk ?wacc ?ws
  case d0 => janus_callpre
  case wacc => simpa only [Memory.accessible_writeLE] using hwS
  case ws =>
    intro r hr
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
  clear hdS hinv
  have hpo : ptr.toNat + blockSize (hdrV s p len 1) true ≤ s.sp.toNat - 4800 ∨ s.sp.toNat + 40 ≤ ptr.toNat := by
    have := InRanges.apart hink hout; unfold Apart at this; omega
  have hLsL1 : LiveSep L1 (win s 4800 40) := hLs0
  have hext' : LiveExt R L1 (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 1) true)]) :=
    LiveExt.single (by simpa using hink) (by simpa using hapk)
  have hMF2 : MemFrame s.mem mk (R.rt ++ winA s stk 40) := by
    simp only [winA, stk] at hMF ⊢
    refine (hMF.trans ?w1 fun a n h => ⟨h, out_wA h⟩).trans hMFk fun a n h => ⟨h, out_cs hb' h⟩
    case w1 => janus_frame
  have hLFS : LiveFrame S.mem mk L1 [] :=
    (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans hLFk (fun _ _ h => h)
  have hLF2 : LiveFrame s.mem mk L [] := hLF.trans hLFS (fun _ _ h => hext.inRanges_old h)
  have hLx := LiveFrame.of_nil' hLF2 (winA s stk 40)
  have hBloc : ptr.toNat + hdrV s p len 1 ≤ s.sp.toNat - 624 - 4160 ∨ s.sp.toNat + 40 ≤ ptr.toNat := by omega
  have hls : LiveSep (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 1) true)]) (win s stk 40) := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hLsL1 r hr
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [win, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hsep : LiveSep (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 1) true)]) [(ptr.toNat, ptr.toNat)] := by
    intro r hr; simp only [Janus.outside_cons, Janus.outside_nil, and_true]
    rcases List.mem_append.1 hr with hr | hr
    · have := hapk r hr; unfold Apart at this; omega
    · simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega
  have hbytes : ∀ j, j < hdrV s p len 1 →
      (mk.bytes (ptr.toNat + j)).toNat = padByte s.mem p.toNat len.toNat (96 + hdrV s p len 0 + j) := by
    intro j hj
    unfold padByte
    rw [if_neg (Nat.not_lt.2 (Nat.le_trans hpast (Nat.le_add_right _ _))), hzk j hj]
    rfl
  have hbudk : b - (3 * makeCost 4 + dCost + allocCost 1024) ≤ b1 - blockSize (hdrV s p len 1) true := by
    have hBS' := blockSize_le_allocCost (hdrV s p len 1) true
    simp only [dCost, allocCost] at hbud hBS' ⊢; omega
  have hacc' : s.mem.accessible ptr.toNat (hdrV s p len 1) true = true :=
    Memory.accessible_mono _ hack (Nat.le_refl _) (by omega)
  have hrt' : InRanges ptr.toNat (hdrV s p len 1) R.rt := hink.sub (Nat.le_refl _) (by omega)
  have hB48 : ptr.toNat + hdrV s p len 1 ≤ 2 ^ 48 := by omega
  have hheld' : Held R (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 1) true)]) ptr.toNat (hdrV s p len 1) :=
    Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩
  have hinp : ∀ a n, p.toNat ≤ a → a + n ≤ p.toNat + len.toNat → mk.readLE a n = s.mem.readLE a n :=
    fun a n h1 h2 => (hheld.sub h1 h2).readLE hMF2 hLx (hpo'.of_sub h1 (by omega))
  have hcc := hcheld.readLE hMF2 hLx hco'
  have hz0' : (0 : Nat) = len.toNat - 96 - min (hdrV s p len 0) (len.toNat - 96) := hz0.symm
  clear hoffc hmN hpw hcw hpo hga hut hLS1 hpast hink hapk hzk
  refine hkZ _ (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (hdrV s p len 1) true)]) (b1 - blockSize (hdrV s p len 1) true)
    ptr.toNat (p.toNat + off + mN) ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29], by janus_simp [h18],
     by janus_simp [hm1], by janus_simp [hm2], by janus_simp [hm3], by janus_simp [hm4], by janus_simp [hm5],
     by janus_simp [hm6], by janus_simp [hs1], by janus_simp [hs2], by janus_simp [hs3], by janus_simp [hs4],
     by janus_simp [hs5, hoffd], by janus_simp [hs6, hoffd], by janus_simp [hk1a], by janus_simp [hk1b],
     by janus_simp, by janus_simp, by janus_simp, hl0, hl1, hl2, hnz, hlg,
     by janus_simp, (by janus_simp [hz0]), (by janus_simp [hsrc]), hsrcb.1, hsrcb.2, hB48, hacc', hheld', hBloc,
     hrt', hsep, hbytes, hdk, hinp, hcc, hext.trans hext', hbudk, hinvk, hls, hMF2, hLF2,
     OpDone.transport (hop 0 (by omega)) (by janus_simp [opAt]) (by janus_simp [opAt]) (by janus_simp [opAt])
       (by janus_simp [opAt]) hLFS (fun _ _ h => hext'.inRanges_old h)⟩ (by janus_simp)

end FvModexp.Arm64.Run
