import FvModexp.Proofs.Amd64.NatQ.DivMBigK
import FvModexp.Proofs.Amd64.NatQ.DivMDefs
import FvModexp.Proofs.Common.StackPot

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`, `z = nil`, `z2 = u`, `u ≥ v`: the postcondition `PostM` (pure) (top s42)

Twin of Arm64/NatQ/DivMBigPost.lean. From `divLarge`'s post at its entry `X` (the new stack `st` with `NewStk`, live set
`L1`) to its return `T` (live set `L2`), the epilogue's writes (`T.mem → m2`: the closure call's return slot
`[sp - 240, sp - 232)`, the result slots, the defer bit) and the deferred `stk.free()` (`m2 → m3`: `R.rt`, the
closure's window `[sp - 4376, sp - 240)`, the header's `len` word; live set `dropAll L2 (stkRs m2 st)`): `PostM` at
the real entry `s`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool FvModexp
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem postBigM {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vl vc : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl vc s)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {X : State}
    (hN : NewStk R L L1 b b1 (s.regs 14).toNat X.mem st)
    (hF : MemFrame s.mem X.mem (R.rt ++ win s 41512 112)) (hLF : LiveFrame s.mem X.mem L [])
    (hsp : X.regs 4 = s.regs 4 - 240#64)
    {T : State} {r rl rc : Nat} {L2 : List (Nat × Nat)} {b'' : Nat}
    (hr : ExpHyp.NatOF R L1 L2 T.mem u uc 1 r rl rc (natVal X.mem u ul % natVal X.mem v vl))
    (hx : LiveExt R L1 L2)
    (hbb : b1 - (DivLarge.costQ dc ul vl + stkR (16 * ul + 64) X.mem st) + stkR (16 * ul + 64) T.mem st ≤ b'')
    (hsb : StackBackL R L1 L2 st X.mem T.mem)
    (hfr : ¬ (r = u ∧ rc = uc) → 0 < rc → 0 < stCap T.mem st →
      Apart r (8 * rc) (stW T.mem st) (8 * stCap T.mem st))
    (hmf : MemFrame X.mem T.mem (R.rt ++ win X 41272 112 ++ (ar 0 0 ++ ar u uc) ++ stkWs X.mem st))
    (hlf : LiveFrame X.mem T.mem L1 ((ar 0 0 ++ ar u uc) ++ stkWs X.mem st))
    {m2 m3 : Janus.Arm64.Memory}
    (hF2 : MemFrame T.mem m2 [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232),
      ((s.regs 4).toNat - 80, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 121, (s.regs 4).toNat - 120)])
    (hF3 : MemFrame m2 m3 (R.rt ++ [((s.regs 4).toNat - 240 - 4136, (s.regs 4).toNat - 240), (st + 8, st + 16)]))
    (hLF3 : LiveFrame m2 m3 L2 [(st + 8, st + 16)])
    (hinv3 : R.inv b'' (dropAll L2 (stkRs m2 st)) (s.regs 14).toNat (view R.rt (dropAll L2 (stkRs m2 st)) m3))
    (s' : State) (hm' : s'.mem = m3) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) {q ql qc : Nat}
    (h0 : s'.regs 0 = BitVec.ofNat 64 q) (h1 : s'.regs 3 = BitVec.ofNat 64 ql) (h2 : s'.regs 1 = BitVec.ofNat 64 qc)
    (h3 : s'.regs 7 = BitVec.ofNat 64 r) (h4 : s'.regs 6 = BitVec.ofNat 64 rl)
    (h5 : s'.regs 8 = BitVec.ofNat 64 rc) :
    PostM R b dc L u ul uc v vl s s' := by
  subst hm'
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨hL1, hrs0, -, -, -, -, hl0, -, -, -, -, -, hdis0, hbb0, -, -⟩ := id hN
  have hspn : (X.regs 4).toNat = (s.regs 4).toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hwO : Outside ((s.regs 4).toNat - 41512) (41512 + 112) R.rt := hout
  -- the held inputs keep their words at `X`
  have hrdH : ∀ a n, (InRanges a n L ∨ Outside a n R.rt) → Outside a n (win s 41512 112) →
      X.mem.readLE a n = s.mem.readLE a n := by
    intro a n hh ho
    rcases hh with hin | hr'
    · exact hLF.readLE a n hin trivial
    · exact hF.readLE a n (by rw [outside_append]; exact ⟨hr', ho⟩)
  have eU : natVal X.mem u ul = natVal s.mem u ul := by
    rcases Nat.eq_zero_or_pos ul with h | h
    · subst h; simp only [natVal, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero]
    · obtain ⟨-, -, -, huh, huw⟩ := hp.ui.2 h; exact hrdH _ _ huh huw
  have eV : natVal X.mem v vl = natVal s.mem v vl := by
    obtain ⟨-, -, -, hvh, hvw⟩ := hp.vo; exact hrdH _ _ hvh hvw
  rw [eU, eV] at hr
  obtain ⟨hv, hnm, hlc, hc40, hnl, hd⟩ := hr
  have hmH : (st, st + 24) ∈ L1 := by rw [hL1]; exact List.mem_append_right _ (List.mem_cons_self ..)
  -- the stack ranges of `m2` are those of `T`
  have hhdO := out_inR2 hwO hN.hdr.1
  have hrd2 : ∀ a n, st ≤ a → a + n ≤ st + 24 → m2.readLE a n = T.mem.readLE a n := fun a n i1 i2 =>
    hF2.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hrsE : stkRs m2 st = stkRs T.mem st :=
    stkRs_congr (hrd2 _ _ (Nat.le_refl _) (by omega)) (hrd2 _ _ (by omega) (by omega))
  rw [hrsE] at hinv3
  -- the result's range: held, outside the window and the header, apart from the final stack ranges
  have hres : 0 < rc → Held R L2 r (8 * rc) ∧ Apart r (8 * rc) ((s.regs 4).toNat - 41512) (41512 + 112) ∧
      Apart r (8 * rc) st 24 ∧ ∀ x ∈ stkRs T.mem st, Apart r (8 * rc) x.1 (x.2 - x.1) := by
    intro hc
    have key : Apart r (8 * rc) ((s.regs 4).toNat - 41512) (41512 + 112) ∧ Apart r (8 * rc) st 24 ∧
        (0 < stCap T.mem st → Apart r (8 * rc) (stW T.mem st) (8 * stCap T.mem st)) := by
      by_cases hru : r = u ∧ rc = uc
      · obtain ⟨rfl, rfl⟩ := hru
        obtain ⟨-, hheld, -, -⟩ := hp.uo.2.1 hc
        have hwu := (hp.uo.2.2 hc).1
        simp only [win, outside_cons, outside_nil, and_true] at hwu
        have hA := hN.apart hheld
        refine ⟨by unfold Apart; omega, hA.1, fun hc' => ?_⟩
        rcases hsb.1.2.2 with ⟨ew, ec⟩ | ⟨hin, hap⟩
        · rw [ew, ec]; have := hA.2; simp only [hl0, Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at this
          exact this
        · exact apart_fresh hheld (fun x hx => hap x (hN.mem hx)) hin
      · rcases hd with h | ⟨-, hin, hap⟩
        · exact absurd h hru
        · refine ⟨(hin.apart hwO).symm, ?_, fun hc' => hfr hru hc hc'⟩
          simpa only [Nat.add_sub_cancel_left] using hap _ hmH
    obtain ⟨k1, k2, k3⟩ := key
    refine ⟨(hnl hc).2.1, k1, k2, stkRs_forall (P := fun x => Apart r (8 * rc) x.1 (x.2 - x.1)) ?_ fun hc2 => ?_⟩
    · simpa only [Nat.add_sub_cancel_left] using k2
    · simpa only [Nat.add_sub_cancel_left] using k3 hc2
  -- the live set after the `Put`
  have hp0 : (stkRs X.mem st).Pairwise fun a b => Apart a.1 (a.2 - a.1) b.1 (b.2 - b.1) := by
    simp only [stkRs]
    split
    · exact List.pairwise_singleton _ _
    · refine List.Pairwise.cons (fun q hq => ?_) (List.pairwise_singleton _ _)
      simp only [List.mem_singleton] at hq; subst hq
      simpa only [Nat.add_sub_cancel_left] using hdis0
  have hFr : ∀ q ∈ stkRs T.mem st, q ∉ L := stkRs_forall (P := fun q => q ∉ L)
    (not_mem_of_apartAll (by simp only; omega) (by simpa only [Nat.add_sub_cancel_left] using hN.hdr.2))
    fun hc2 => by
      rcases hsb.1.2.2 with ⟨ew, ec⟩ | ⟨-, hap⟩
      · rw [ew, ec]
        have hc' : 0 < stCap X.mem st := by rw [← ec]; exact hc2
        exact not_mem_of_apartAll (by simp only; omega) (by simpa only [Nat.add_sub_cancel_left] using (hN.arr hc').2)
      · exact not_mem_of_apartAll (by simp only; omega)
          (by simpa only [Nat.add_sub_cancel_left] using (show ApartAll _ _ L from fun q hq => hap q (hN.mem hq)))
  have hLE : LiveExt R L (dropAll L2 (stkRs T.mem st)) := liveExt_dropAll hrs0 hp0 (by rw [← hL1]; exact hx) hFr
  -- frames `T → s'.mem`
  have hFT3 : MemFrame T.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4376, (s.regs 4).toNat - 232),
      ((s.regs 4).toNat - 121, (s.regs 4).toNat - 120), ((s.regs 4).toNat - 80, (s.regs 4).toNat - 32)] ++
      [(st + 8, st + 16)]) := hF2.trans hF3 fun a n h => by
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨⟨by omega, h.1.2.2.2, h.1.2.2.1⟩, ⟨h.1.1, by omega, h.2⟩⟩
  have hLs2 : LiveSep L2 [((s.regs 4).toNat - 41512, (s.regs 4).toNat + 112)] :=
    liveSep_ext hx (hN.liveSep hLs fun q hq => by
      simp only [win, List.mem_singleton] at hq; subst hq; simp only
      rwa [show (s.regs 4).toNat + 112 - ((s.regs 4).toNat - 41512) = 41512 + 112 by omega]) fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; simp only
      rwa [show (s.regs 4).toNat + 112 - ((s.regs 4).toNat - 41512) = 41512 + 112 by omega]
  have hF2w : MemFrame T.mem m2 [((s.regs 4).toNat - 41512, (s.regs 4).toNat + 112)] := hF2.mono fun a n h => by
    simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hLT3 : LiveFrame T.mem s'.mem L2 [(st + 8, st + 16)] := (LiveFrame.of_win hF2w hLs2).trans hLF3 fun _ _ h => h
  have hrd : ∀ a k, r ≤ a → a + k ≤ r + 8 * rc → 0 < rc → s'.mem.readLE a k = T.mem.readLE a k := by
    intro a k i1 i2 hc
    obtain ⟨hH, k1, k2, -⟩ := hres hc
    unfold Apart at k1 k2
    exact Expmc.held_readLE (hH.sub i1 i2) hFT3 hLT3
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  -- frames `s → s'.mem`
  have hFz : MemFrame s.mem s'.mem (R.rt ++ win s 41512 112 ++ [(u, u + 8 * uc)]) := by
    refine ⟨fun a k ho => ?_, fun a k w => by rw [hFT3.accessible, hmf.accessible, hF.accessible]⟩
    simp only [outside_append] at ho
    obtain ⟨⟨hrt, hwa⟩, hz⟩ := ho
    have hwa' := hwa
    simp only [win, outside_cons, outside_nil, and_true] at hwa'
    have hws := hN.outWs hrt
    have hhd : Outside a k [(st + 8, st + 16)] := by
      have := (hN.out hrt).1; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    rw [hFT3.readLE a k (by
        simp only [outside_append, outside_cons, outside_nil, and_true] at hhd ⊢
        exact ⟨⟨hrt, by omega, by omega, by omega⟩, hhd⟩),
      hmf.readLE a k (by
        have hws' := hws
        simp only [stkWs, outside_cons, outside_nil, and_true] at hws'
        simp only [outside_append, win, outside_cons, outside_nil, and_true, hspn]
        exact ⟨⟨⟨hrt, win240 hb' hwa'⟩, outside_ar (fun h => absurd h (by decide)), outside_ar_of hz⟩, hws'⟩),
      hF.readLE a k (by simp only [outside_append]; exact ⟨hrt, hwa⟩)]
  have hLz : LiveFrame s.mem s'.mem L [(u, u + 8 * uc)] := ⟨fun a k hin hz => by
    obtain ⟨hws, hhd⟩ := hN.outL hin
    have hin1 : InRanges a k L1 := hin.of_subset fun _ hr => hN.mem hr
    rw [hLT3.readLE a k (hx.inRanges_old hin1) hhd,
      hlf.readLE a k hin1 (by
        simp only [outside_append]; exact ⟨⟨outside_ar (fun h => absurd h (by decide)), outside_ar_of hz⟩, hws⟩),
      hLF.readLE_nil a k hin]⟩
  refine ⟨hfs, hdf, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, dropAll L2 (stkRs T.mem st), b'',
    ⟨?_, ?_, hlc, hc40, ?_, ?_⟩, ⟨hLE, ?_, hinv3⟩, hFz, hLz⟩
  · rcases Nat.eq_zero_or_pos rl with hl | hl
    · subst hl; simp only [natVal, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero] at hv ⊢; exact hv
    · rw [← hv]; exact hrd r (8 * rl) (Nat.le_refl _) (by omega) (by omega)
  · rcases hnm with h | h
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos rl with hl | hl
      · exact Or.inl hl
      · right; rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h
  · intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc
    exact ⟨a1, held_dropAll a2 (by omega) (hres hc).2.2.2, by rw [hFT3.accessible]; exact a3, a4⟩
  · exact hd.imp_right fun ⟨k1, hin, hap⟩ => ⟨k1, hin, fun q hq => hap q (hN.mem hq)⟩
  · have hc := hp.cost
    have hR := stkR_le (16 * ul + 64) X.mem st
    simp only [costMQ, HM, costQ, DivLarge.costQ] at hc hbb ⊢
    omega

end FvModexp.Amd64.Q.NatDiv
