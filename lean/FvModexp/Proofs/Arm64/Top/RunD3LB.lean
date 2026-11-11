import FvModexp.Proofs.Arm64.Top.RunD3ZDefs

/-! # `Run` (arm64): `Z3` to `J3` with `nb > 0` input bytes left for the modulus: `memmove` of the input rest into the
fresh `makeslice` buffer (`copy(padded, data)` of `RightPadBytes`), the remaining bytes stay zero -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem d3lB (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (Q : Outcome → Prop)
    (hbudD : 3 * makeCost 4 + 3 * dCost ≤ b)
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 3 L2 b2 S2 →
      (S2.regs 0).toNat = S2.mem.readLE (s.sp.toNat - 192) 8 → (S2.regs 1).toNat = S2.mem.readLE (s.sp.toNat - 184) 8 →
      S2.pc = BitVec.ofNat 64 pcD3 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q)
    (U : State) (Lk : List (Nat × Nat)) (bk B src nb : Nat) (hj : JoinZ3 R b L c p len cp s ret Lk bk B src nb U)
    (hpc : U.pc = BitVec.ofNat 64 pcZ3) (hnb : 0 < nb) :
    Reaches ((LibRun.program.link impl).withExit ret) U Q := by
  have henv0 := henv
  have hin0 := hin
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := henv
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h28, h29, h18, hm1, hm2, hm3, hm4, hm5, hm6, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hz1, hz2, hz3,
    hl0, hl1, hl2, hnz, hlg, hr0, hy1, hy2, hsrc1, hsrc2, hB48, hBacc, hBH, hBW, hBrt, hBsep, hBv, hpst, hnbp, hdS, hinS,
    hcS, hext, hbud, hinv, hLsS, hMF, hLF, hop0, hop1, hopA, L0, hLk, hext0, hsep0, hq0, hq1⟩ := hj
  obtain ⟨hsrc, hsrcE, hnbl, hsB⟩ := hnbp hnb
  subst hLk
  have hap1 := hap.1
  have hLs0 := hLsS
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  simp only [win, Outside, and_true] at hpw hcw
  unfold Apart at hga
  have hwS : U.mem.accessible (s.sp.toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hspn : U.sp.toNat = s.sp.toNat - 624 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hr0' : U.regs 0 = BitVec.ofNat 64 B := by
    apply BitVec.eq_of_toNat_eq; rw [hr0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hIe := toInt_small (BitVec.ofNat 64 (hdrV s p len 2)) (by simp; omega)
  have hmv' : MemmoveLive (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibRun.names) hmv
  have hbs := le_blockSize (hdrV s p len 2) true
  have hmvok : R.ok (cA "runtime.memmove") [B, src, nb] := hokM _ _ _ (by omega)
  have hsA : s.mem.accessible src nb false = true := Memory.accessible_mono _ hpacc (by omega) (by omega)
  have hBA : s.mem.accessible B nb true = true := Memory.accessible_mono _ hBacc (Nat.le_refl _) (by omega)
  have hBHn : Held R (L0 ++ [(B, B + blockSize (hdrV s p len 2) true)]) B nb := hBH.sub (Nat.le_refl _) (by omega)
  have hsH : Held R (L0 ++ [(B, B + blockSize (hdrV s p len 2) true)]) src nb :=
    hext.held (hheld.sub (by omega) (by omega))
  have hn1 : (src = B) = False := by simp only [eq_iff_iff, iff_false]; omega
  have hn2 : (B = src) = False := by simp only [eq_iff_iff, iff_false]; omega
  have hn3 : (BitVec.ofNat 64 src = BitVec.ofNat 64 B) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
  have hn4 : (BitVec.ofNat 64 B = BitVec.ofNat 64 src) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega
  have hgt : (0 < ((hdrV s p len 2 : Nat) : Int)) = True := by simp only [eq_iff_iff, iff_true]; omega
  set_option janus.callRegions true in
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs2, hs3, hs4, hs5, hs6, hy1, hy2, hr0', hIe, toInt_small, hn1, hn2, hn3, hn4, hgt]
    until [segAddr Extracted.program fn + 0x728] calls [hmv']
  rename_i m2 _ _ hMFm hLFm hinvm hcp
  have hm : ∀ a n w, U.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    simp only [hMF.accessible]
  have hdk' : Extracted.program.DataLoaded (U.mem.writeLE (BitVec.toNat s.sp - 264) 8 B) :=
    hdS.writeLE (by rw [hm]; exact Memory.accessible_mono _ hw (by omega) (by omega))
  have hMFm' := hMFm
  rw [List.append_assoc] at hMFm'
  have hd2 : Extracted.program.DataLoaded m2 := by
    refine dataLoaded_frame hdk' (by rw [hrg1]; simp) hro hMFm' fun r hr _ => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [Memory.accessible_writeLE]
    rcases hr with (rfl | rfl) | rfl
    · rw [hm]; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · rw [hm]; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · rw [hm]; exact Memory.accessible_mono _ hBacc (Nat.le_refl _) (by dsimp only; omega)
  janus_run [hm1, hm2, hm3, hm4, hm5, hm6, hs2, hs3, hs4, hs5, hs6] until [pcJ3]
  have hBn : InRanges B nb R.rt := hBrt.sub (Nat.le_refl _) (by omega)
  have hMF2 : MemFrame s.mem m2 (R.rt ++ winA s stk 40) := by
    simp only [winA, stk] at hMF ⊢
    refine (hMF.trans ?w2 fun a n h => ⟨h, out_wA h⟩).trans hMFm fun a n h => ⟨h, out_csd hb' hBn h⟩
    case w2 => janus_frame
  have hLsL0 : LiveSep L0 (win s 4800 40) := fun r hr => hLs0 r (List.mem_append_left _ hr)
  have hdst : LiveSep L0 [(B, B + nb)] := by
    intro r hr; have := hsep0 r hr
    simp only [Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢; omega
  have hLFS : LiveFrame U.mem m2 L0 [] :=
    (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL0).trans
      (LiveFrame.drop (L := L0) ⟨fun a n h hw => hLFm.readLE a n (h.append_left _) hw⟩ hdst) (fun _ _ h => h)
  have hLF2 : LiveFrame s.mem m2 L [] := hLF.trans hLFS (fun _ _ h => hext0.inRanges_old h)
  have hLx := LiveFrame.of_nil' hLF2 (winA s stk 40)
  have hpo' : Outside p.toNat len.toNat (winA s stk 40) := by
    simp only [winA, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hco' : Outside c.toNat 3 (winA s stk 40) := by
    simp only [winA, stk, Janus.outside_cons, Janus.outside_nil, and_true]; omega
  have hIn : InRanges B (hdrV s p len 2) (L0 ++ [(B, B + blockSize (hdrV s p len 2) true)]) :=
    ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩
  have hbytes : ∀ j, j < hdrV s p len 2 →
      (m2.bytes (B + j)).toNat = padByte s.mem p.toNat len.toNat (96 + (hdrV s p len 0 + hdrV s p len 1) + j) := by
    intro j hj
    unfold padByte
    split
    · rename_i hjl
      have hcj := hcp j (by omega)
      rw [hcj, ← Memory.readLE_one, Memory.readLE_writeLE_of_disjoint _ _ (by omega), hinS _ _ (by omega) (by omega),
        Memory.readLE_one, show src + j = p.toNat + (96 + (hdrV s p len 0 + hdrV s p len 1) + j) by omega]
    · rename_i hjl
      rw [← Memory.readLE_one, hLFm.readLE _ _ (hIn.sub (by omega) (by omega)) (by
          simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
          refine ⟨⟨by omega, by omega⟩, by omega⟩),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_one, hBv j hj]
  refine d3join impl hap R hmk hokS b L c p len cp ret hret s henv0 hin0 Q hbudD hk _ _ bk B ?hj (by janus_simp)
  case hj =>
  refine ⟨by janus_simp [hsp], by janus_simp [h28], by janus_simp [h29], by janus_simp [h18],
     by janus_simp [hm1], by janus_simp [hm2], by janus_simp [hm3], by janus_simp [hm4], by janus_simp [hm5],
     by janus_simp [hm6], by janus_simp [hs1], by janus_simp [hs2], by janus_simp [hs3], by janus_simp [hs4],
     by janus_simp [hs5], by janus_simp [hs6], by janus_simp [hs7], by janus_simp [hs8], by janus_simp [hs9],
     by janus_simp [hz1], by janus_simp [hz2], by janus_simp [hz3], hl0, hl1, hl2, hnz,
     by janus_simp, by janus_simp [hs3], hB48,
     Memory.accessible_read_of_write _ hBacc, hBH, (by rcases hBW with h | h; exact Or.inl h; exact Or.inr (Or.inr h)),
     hbytes, hd2, fun a n h1 h2 => (hheld.sub h1 h2).readLE hMF2 hLx (hpo'.of_sub h1 (by omega)),
     hcheld.readLE hMF2 hLx hco', hext, hbud, hinvm, hLsS, hMF2, hLF2,
     OpDone.transport hq0 (by janus_simp [opAt]) (by janus_simp [opAt]) (by janus_simp [opAt])
       (by janus_simp [opAt]) hLFS (fun _ _ h => h.append_left _),
     OpDone.transport hq1 (by janus_simp [opAt]) (by janus_simp [opAt]) (by janus_simp [opAt])
       (by janus_simp [opAt]) hLFS (fun _ _ h => h.append_left _), OpsApart.transport hopA (fun i hi => by
       rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> exact ⟨by janus_simp [opAt], by janus_simp [opAt]⟩)⟩

end FvModexp.Arm64.Run
