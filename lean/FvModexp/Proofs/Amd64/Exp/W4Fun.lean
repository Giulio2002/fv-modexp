import FvModexp.Proofs.Amd64.Exp.W4FunP

set_option autoImplicit false

/-!
# window-4 (amd64): the function-level post `post_of` (agent expmc s59)

From the chain's post `W4En.EnPost` (entry → `RET`): anchor the prologue posts at the reserve's memory (`AncI.refl`,
`sepL1`), consume them (`xnQ_anc`), then walk the eleven segments (`chainA`/`chainT`) for the frame, the header and the
value (`w4_value`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpW4

open FvModexp.Amd64.W4En (EPre EnPost XnB)
open FvModexp.Amd64.W4Pro (Zw rd_step ap_fresh arr_ap akf_trans out_S2 out10_hdr hdr_fields chainA chainT
  final_out final_outL zw_of_ap zw_of_sep out10_p out10_fresh natLive_tr inv_fin res_of norm_tr top_ne)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the function-level post of window-4** (amd64) from the chain's post `EnPost` -/
theorem post_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K costD g fs sp st bp r zp zc xp xl xc yp ylen mp n mc : Nat}
    {costF : Nat → Nat → Nat → Nat} {s s' : State}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc s)
    (hMo : s.mem.readLE mp (8 * n) % 2 = 1) (hM1 : 1 < s.mem.readLE mp (8 * n))
    (hB : XnB costF n costD (stLen s.mem st + StackNat.rnd (23 * n)) xl
      (b - stackNatCost (stLen s.mem st) (23 * n)))
    (hE : EnPost R b L K g fs sp st bp r zp zc xp xl xc yp ylen mp n mc costD s s') :
    (s'.regs 4 = BitVec.ofNat 64 (sp + 0x390) ∧ s'.regs 5 = BitVec.ofNat 64 bp ∧ s'.regs 14 = BitVec.ofNat 64 g ∧
      s'.fsBase.toNat = fs ∧ s'.xmm 15 = 0 ∧ s'.df = false) ∧
    PostG R b L K costD g zp zc st xp xl yp ylen mp n s s' := by
  have hP' := hP
  obtain ⟨he, -, -, -, hn, -, -, -, hmO, -, -, -, -, -, -, hyN, hyl, -, -, -, -, -, -, -, -, -, -, -, hz, -,
    hsok, hstw, -, -, -, -, hstf, -, -, -, -, -, -, -, -, -, -⟩ := hP'
  obtain ⟨hs4, -, -, -, -, -, hK, -, hce, -⟩ := he
  obtain ⟨-, hK0, hA0, -, -, -, -, hrt, -, -, hLs, -⟩ := hce
  have hK8 : K + 8 ≤ sp := k8_of hK0 hK
  have hK4 : 4296 ≤ K := k4_of hK
  have hs8 : 8 ≤ sp := Nat.le_trans (Nat.le_add_left 8 K) hK8
  have hS : (s.regs 4).toNat = sp + 0x388 := by rw [hs4]; exact MontW.toNat_of (sp_lt hA0)
  have hlc0 : stLen s.mem st ≤ stCap s.mem st := hsok.2.2.2.2.2.1
  have hmpos : 0 < s.mem.readLE mp (8 * n) := pos_of_lt hM1
  have hmB := Expmc.readLE_lt_B s.mem mp n
  obtain ⟨M, L1, b1, hF0, hLF0, -, hx0, hb1, hkf0, hai0, hlen0, hcapM, -, -, -, -, hXn⟩ := hE
  have hA := W4Pro.AncI.refl (R := R) (L0 := L1) (sp := sp) (K := K) (st := st) (M0 := M) hcapM
    (sepL1 hx0 hrt hLs hs8)
  obtain ⟨lenM, Xv, hlM1, hlM2, hXv, hL⟩ := W4Pro.xnQ_anc hA (Nat.le_of_eq hlen0) (Nat.le_of_eq hlen0.symm) hK8
    (W4Pro.xnBudA_of (hB.mono hb1)) hXn
  clear hXn hA
  obtain ⟨zzp, zzc, hzzl, hzzin, hzzap, Md, Ld, bd, rp, rl, rc, M1, rrq, rrc, onep, M2, L2, b2, hAd, hbd, hlenD, -,
    hRR, hOC, hRet, hzzA, hzzH⟩ := hL
  obtain ⟨hF1, hLF1⟩ := W4Pro.Anc.frame hAd.1 hK8 hcapM
  obtain ⟨⟨hxd1, -, -, -, hkfd, haid⟩, -, -, -⟩ := hAd
  obtain ⟨hF2, hLF2, -, -, -, -⟩ := hRR
  obtain ⟨hF3, hLF3, hx3, hb3, hsok3, hlen3, hkept3, hfresh3, -, hmem3⟩ := hOC
  obtain ⟨Mj, ⟨hF4, hLF4⟩, -, -, Ma, Mb, zp1, zc1, zzp2, zzc2, La, Lb, ba, bb, hZ1, hZ2, hZj⟩ := hRet
  obtain ⟨-, hbuf1, -, hxa, hba, hF5, hLF5, -, -, hz1o⟩ := hZ1
  obtain ⟨-, -, -, hxb, hbb, hF6, hLF6, -, -, hz2o⟩ := hZ2
  obtain ⟨M0z, zp', zc', zzp', zzc', Mx, hPz, hF7, hLF7, -, hBufs, -, hvx, hT⟩ := hZj
  obtain ⟨M'', Mj2, p, l, c, ⟨⟨hF8, hLF8⟩, -, -⟩, hzzv, hJ, hFin⟩ := hT
  obtain ⟨L'', b'', hx9, hb9, hinv9, -, hF9, hLF9, hval9, hlc, hc40, hnl9, hor9, -⟩ := hJ
  obtain ⟨h4', h5', h14', hfs', hx15', hdf', h0', h3', h1', hn0', hF10⟩ := hFin
  have xd := hx0.trans hxd1
  have x2 := xd.trans hx3
  have x3 := x2.trans hxa
  have x4 := x3.trans hxb
  have x9 := x4.trans hx9
  have hnz : n ≤ zzc := n_le_of hzzl
  have hnz1 : n ≤ zc1 := n_le_of2 hbuf1.1
  have hzz2 := zz2_of hz2o hzzin hzzap (hxd1.trans (hx3.trans hxa))
  -- the stack header through `Md → M1`
  have hh_st : Outside st 24 R.rt ∨ InRanges st 24 L := hsok.2.1.symm
  have hw_st : Zw sp K st 24 := zw_of_ap hstw hK8
  have hzz_st := ap_fresh hzzin hzzap hx0 hh_st
  have hF2' := hF2
  simp only [List.append_assoc] at hF2'
  have eM1 : M1.readLE st 24 = Md.readLE st 24 :=
    rd_step hF2' hLF2 xd hh_st (out_S2 hw_st hK4 hzz_st hnz).1 (out_S2 hw_st hK4 hzz_st hnz).2
  have hd1 := hdr_fields eM1
  have kMd := akf_trans hkf0 hx0 hkfd
  have kM1 : (stW M1 st = stW s.mem st ∧ stCap M1 st = stCap s.mem st) ∨
      (InRanges (stW M1 st) (8 * stCap M1 st) R.rt ∧ ApartAll (stW M1 st) (8 * stCap M1 st) L) := by
    rw [hd1.1, hd1.2.2]; exact kMd
  have kM12 : (stW M2 st = stW M1 st ∧ stCap M2 st = stCap M1 st) ∨
      (InRanges (stW M2 st) (8 * stCap M2 st) R.rt ∧ ApartAll (stW M2 st) (8 * stCap M2 st) Ld) := by
    by_cases h : stLen M1 st + StackNat.rnd (17 * n) ≤ stCap M1 st
    · exact Or.inl (hkept3 h)
    · exact Or.inr (hfresh3 (Nat.lt_of_not_le h))
  have kM2 := akf_trans kM1 xd kM12
  have hlenM1 : stLen M1 st = lenM := hd1.2.1.trans hlenD
  have hl0M : stLen s.mem st ≤ stLen M st := le_of_eq_add hlen0
  have hl0L : stLen s.mem st ≤ lenM := Nat.le_trans hl0M hlM1
  have hl0M1 : stLen s.mem st ≤ stLen M1 st := hlenM1 ▸ hl0L
  have hcM2 : lenM + 17 * n ≤ stCap M2 st := lc_of (hlenM1 ▸ hlen3) hsok3.2.2.2.2.2.1
  -- the zone of the function-level frame
  have zone : ∀ a k, (Outside a k R.rt ∨ InRanges a k L) → Zw sp K a k → (a + k ≤ st ∨ st + 24 ≤ a) →
      (a + k ≤ stW s.mem st + 8 * stLen s.mem st ∨ stW s.mem st + 8 * stCap s.mem st ≤ a) →
      (2 * n ≤ zc → a + k ≤ zp ∨ zp + 8 * zc ≤ a) →
      M0z.readLE a k = s.mem.readLE a k ∧ s'.mem.readLE a k = s.mem.readLE a k := by
    intro a k hh hw hd hf hzc
    have hzz := ap_fresh hzzin hzzap hx0 hh
    have hz1 := z1_ap hz1o x2 hh hbuf1.1 hzc
    have hbb := bufs_ap hPz hz1 (ap_fresh hzz2.1 hzz2.2 hx0 hh)
    exact chainA hK4 hF0 hLF0 hx0 hF1 hLF1 xd hF2 hLF2 hF3 hLF3 x2 hF4 hLF4 hF5 hLF5 x3 hF6 hLF6 x4 hF7 hLF7
      hF8 hLF8 hF9 hLF9 hF10 hh hw hd (arr_ap hkf0 hh hf hl0M) hzz hnz (arr_ap kM1 hh hf hl0M1)
      (bp_ap (arr_ap kM2 hh hf hl0L) hcM2) hz1 hnz1 hbb.1 hbb.2
  have hacc : ∀ a k w, s'.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hF10.accessible, hF9.accessible, hF8.accessible, hF7.accessible, hF6.accessible, hF5.accessible,
      hF4.accessible, hF3.accessible, hF2.accessible, hF1.accessible, hF0.accessible]
  have hacc2 : ∀ a k w, s'.mem.accessible a k w = M2.accessible a k w := fun a k w => by
    rw [hF10.accessible, hF9.accessible, hF8.accessible, hF7.accessible, hF6.accessible, hF5.accessible,
      hF4.accessible]
  -- the header at the return
  have hf_st := free_ap hstf hlc0
  have hz1_st := z1_ap hz1o x2 hh_st hbuf1.1 (fun h => ap_of' (hz h).1.2.2.1)
  have hbb_st := bufs_ap hPz hz1_st (ap_fresh hzz2.1 hzz2.2 hx0 hh_st)
  have eHdr := chainT hK4 x2 hF4 hLF4 hF5 hLF5 x3 hF6 hLF6 x4 hF7 hLF7 hF8 hLF8 hF9 hLF9 hh_st hw_st
    (bp_ap (arr_ap kM2 hh_st hf_st hl0L) hcM2) hz1_st hnz1 hbb_st.1 hbb_st.2
  have hdj := hdr_fields eHdr
  have eW : stW s'.mem st = stW M2 st := (hF10.readLE st 8 (out10_hdr hw_st hK4).1).trans hdj.1
  have eC : stCap s'.mem st = stCap M2 st := (hF10.readLE (st + 16) 8 (out10_hdr hw_st hK4).2).trans hdj.2.2
  have eL : stLen s'.mem st = stLen s.mem st := hn0'
  -- the result array at the return
  have hout_p : Outside p (8 * c) [(sp - 16, sp), (sp + 0x77, sp + 0x78), (sp + 0x170, sp + 0x188), (st + 8, st + 16)] := by
    rcases hor9 with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
    · exact out10_p hBufs.2.1.2.2.2.2.2.1 (hBufs.2.2.2.2.2.2.2.2 _ (List.mem_cons_of_mem _
        (List.mem_singleton_self _))).2 (Nat.le_trans hK4 (Nat.le_trans (Nat.le_add_right K 8) hK8))
    · exact out10_fresh hrt hin (ap_fresh hin hap x4 hh_st).symm hK4 hK8
  have hrp : ∀ a k, p ≤ a → a + k ≤ p + 8 * c → s'.mem.readLE a k = Mj2.readLE a k := fun a k h1 h2 =>
    hF10.readLE a k (hout_p.of_sub h1 h2)
  have hl' := Expmc.normL_le Mj2 p l
  have hlc' : Expmc.normL Mj2 p l ≤ c := Nat.le_trans hl' hlc
  -- the value
  have hmp := (zone mp (8 * n) hmO.1.symm (zw_of_ap hmO.2.1 hK8) (ap_of hmO.2.2.1) (free_ap hmO.2.2.2 hlc0)
    (fun h => ap_of' (hz h).2.2.2.2.2.2.1)).1
  have hval : natVal s'.mem p (Expmc.normL Mj2 p l) =
      natVal s.mem xp xl ^ natVal s.mem yp ylen % natVal s.mem mp n := by
    simp only [natVal]
    rw [hrp _ _ (Nat.le_refl _) (Nat.add_le_add_left (Nat.mul_le_mul_left 8 hlc') p), Expmc.normL_val]
    have hv9 : Mj2.readLE p (8 * l) = _ := hval9
    rw [hv9, hzzv, hvx, hmp, Expmc.readLE_wd s.mem yp (ylen - 1) ylen (Nat.sub_lt hyl Nat.one_pos)]
    exact W4Pro.w4_value n _ _ Xv _ ylen hn hmB hMo (xv_mod hXv) (xv_lt hXv hmpos hmB) hyl
      (Expmc.readLE_lt_B _ _ _) (W4Pro.y_ge s.mem yp ylen hyl (top_ne hyN hyl))
  refine ⟨⟨h4', h5', h14', hfs', hx15', hdf'⟩, p, Expmc.normL Mj2 p l, c, h0', h3', h1', hval,
    norm_tr (Expmc.normL_norm Mj2 p l) hlc' hrp, hlc', hc40, L'', b'', x9, ?_,
    inv_fin hF10 hrt (x9.held hsok.2.1) hK4 hK8 hinv9, natLive_tr hnl9 (LiveExt.refl R L'') (fun a k w => hF10.accessible a k w),
    res_of hor9 hPz (hz1o.imp (fun h => ⟨h.1, h.2.1⟩) id) hzz2 hx0 x2 x4, ?_, ?_, ?_, ?_⟩
  · unfold W4Pro.W4Cost
    rw [hlenM1] at hb3
    exact W4Pro.bud_fin hb1 rfl hbd hb3 hba hbb hb9 (W4Pro.if_le n) (W4Pro.snc_le hlM2)
  · refine ⟨⟨⟨hsok.1, x9.held hsok.2.1, by rw [hacc]; exact hsok.2.2.1, hsok.2.2.2.1, ?_, ?_, ?_⟩, eL, ?_⟩,
      W4Pro.arrIn_chain hai0 haid hxd1 ⟨hd1.1, hd1.2.2⟩ (W4Pro.arrIn_split hsok3.2.2.2.2.2.1 hlen3 hkept3 hmem3) hx3
        ⟨eW, eC⟩ ((hxa.trans hxb).trans hx9)⟩
    · rw [eW, eC]; exact natLive_tr hsok3.2.2.2.2.1 ((hxa.trans hxb).trans hx9) hacc2
    · rw [eL, eC]; exact Nat.le_trans hl0L (Nat.le_trans (Nat.le_add_right _ _) hcM2)
    · rw [eC]; exact hsok3.2.2.2.2.2.2
    · rw [eW, eC]; exact kM2
  · refine ⟨fun a k ho => ?_, fun a k w => hacc a k w⟩
    obtain ⟨h0, hw, hd, hf, hzc⟩ := final_out ho hS hK8
    exact (zone a k (Or.inl h0) hw hd hf (fun _ => hzc)).2
  · refine ⟨fun a k hin ho => ?_⟩
    obtain ⟨hd, hf, hzc⟩ := final_outL ho
    exact (zone a k (Or.inr hin) (zw_of_sep hLs hin hK8) hd hf (fun _ => hzc)).2
  · -- `ResSep`: the result vs the final array (= that of `M2`)
    have hcap2 : 0 < stCap M2 st := cap_pos hcM2 hn
    have hA2 : Held R L2 (stW M2 st) (8 * stCap M2 st) := (hsok3.2.2.2.2.1 hcap2).2.1
    refine ResSep.congr ?_ eW eC
    rcases hor9 with ⟨rfl, rfl⟩ | ⟨hin, hap⟩
    · rcases hPz with ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
      · rcases hz2o with ⟨rfl, rfl, -⟩ | ⟨hin, hap⟩
        · exact ResSep.of_apart (apart_arr_step (by rw [hd1.1, hd1.2.2]; exact hzzA) kM12 hzzH)
        · exact ResSep.of_apart (apart_arr_of_fresh hap (hxa.held hA2) hin)
      · rcases hz1o with ⟨rfl, rfl, -⟩ | ⟨hin, hap⟩
        · exact ResSep.of_held kM2 (hz hbuf1.1).1.1
        · exact ResSep.of_apart (apart_arr_of_fresh hap hA2 hin)
    · exact ResSep.of_apart (apart_arr_of_fresh hap ((hxa.trans hxb).held hA2) hin)

end FvModexp.Amd64.ExpW4
