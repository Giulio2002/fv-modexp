import FvModexp.Proofs.Amd64.Top.RunC2Lem3
import FvModexp.Proofs.Amd64.Top.RunC2Lem

/-! # `Run` (amd64): the state `RelV` at `V` from the `Bytes` call's post (pure; used by `c2B` on both call sites) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

open RunIface in
set_option maxRecDepth 20000 in
theorem relV_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c p len cp : BitVec 64} {s : State} {ret W stkM aboveM : Nat}
    (henvW : CallEnv R L s W 40) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144) (ha8 : 8 ≤ aboveM)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    {L1 : List (Nat × Nat)} {b1 : Nat} {T : State} (hrel : RelD R b L c p len cp s ret 3 3 (cstD 3) L1 b1 T)
    {B rs1 rs2 : Nat} {sc s1 tB V : State} {L2 : List (Nat × Nat)} {b2 : Nat}
    (hscm : sc.mem = T.mem.writeLE ((s.regs 4).toNat - 616) 8 rs1) (hsc4 : sc.regs 4 = T.regs 4 - 8#64)
    (hext2 : LiveExt R L1 L2) (hb2 : b1 - B ≤ b2)
    (hMF2 : MemFrame sc.mem s1.mem (R.rt ++ win sc stkM aboveM ++
      ((s.regs 4).toNat - 136, (s.regs 4).toNat - 136 + 32) :: arrW sc.mem ((s.regs 4).toNat - 136)))
    (hLF2 : LiveFrame sc.mem s1.mem L1
      (((s.regs 4).toNat - 136, (s.regs 4).toNat - 136 + 32) :: arrW sc.mem ((s.regs 4).toNat - 136)))
    (hrg : s1.mem.regions = sc.mem.regions)
    (harrR : 0 < sc.mem.readLE ((s.regs 4).toNat - 136 + 24) 8 →
      InRanges (sc.mem.readLE ((s.regs 4).toNat - 136 + 8) 8) (8 * sc.mem.readLE ((s.regs 4).toNat - 136 + 24) 8) R.rt)
    (harrL : 0 < sc.mem.readLE ((s.regs 4).toNat - 136 + 24) 8 →
      ApartAll (sc.mem.readLE ((s.regs 4).toNat - 136 + 8) 8) (8 * sc.mem.readLE ((s.regs 4).toNat - 136 + 24) 8) L)
    (hval : IntV (s1.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) = resV s p len)
    (hvlt : IntV (s1.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) < opV s p len 2)
    (hlb : lenW (s1.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) ≤ maxW)
    (hbfin : ∀ b2 b3 lb, lb ≤ maxW → b1 - B ≤ b2 → b2 - BytesBudget lb ≤ b3 →
      b - (3 * makeCost 4 + 3 * dCost + callB s p len) ≤ b3)
    (ht4 : tB.regs 4 = T.regs 4 - 8#64) (ht5 : tB.regs 5 = T.regs 5) (ht14 : tB.regs 14 = s.regs 14)
    (htx : tB.xmm 15 = 0) (htfs : tB.fsBase = s.fsBase) (htdf : tB.df = false)
    (htm : tB.mem = s1.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2)
    (hQ : ((V.regs 4 = tB.regs 4 + 8 ∧ V.regs 5 = tB.regs 5 ∧ V.regs 14 = tB.regs 14 ∧ V.xmm 15 = tB.xmm 15) ∧
        V.fsBase = tB.fsBase ∧ V.df = tB.df ∧
        ∃ p n c : Nat, (V.regs 0).toNat = p ∧ (V.regs 3).toNat = n ∧ (V.regs 1).toNat = c ∧ n ≤ c ∧
          beVal V.mem p n = IntV (s1.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136) ∧
          (n = 0 ∨ (V.mem.bytes p).toNat ≠ 0) ∧
          ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L2 L' ∧
            b2 - BytesBudget (lenW (s1.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) ((s.regs 4).toNat - 136)) ≤ b' ∧
            R.inv b' L' (s.regs 14).toNat (view R.rt L' V.mem) ∧ (0 < n → InRanges p n L' ∧ InRanges p n R.rt ∧
              ApartAll p n L2 ∧ V.mem.accessible p n true = true ∧ p + n ≤ 2 ^ 48) ∧
            MemFrame (s1.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) V.mem (R.rt ++ win tB stkM aboveM) ∧
            LiveFrame (s1.mem.writeLE ((s.regs 4).toNat - 616) 8 rs2) V.mem L2 []) ∧
        V.mem.regions = tB.mem.regions) :
    ∃ (Lk : List (Nat × Nat)) (bk : Nat), RelV R b L p len s ret W Lk bk V := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henvW
  simp only [regSP, Janus.Amd64.GoABI.regG] at hb' ha hw hout hal hga hgr
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, -, -, -, -, -, -, hs3, -, -, -, -, -, hl2, -, -, -,
    hdS, -, -, hext, hbud, -, hLsS, hMF, hLF, -, -⟩ := hrel
  simp only [stk] at hLsS hMF
  obtain ⟨⟨⟨h4q, h5q, h14q, hxq⟩, hfsq, hdfq, vp, vn, vc, hvp, hvn, -, -, hbe, hmin, Lb, bb, hext3, hb3, hinv3, hfr3,
    hMF3, hLF3⟩, hrg3⟩ := hQ
  have hspn : (T.regs 4).toNat = (s.regs 4).toNat - 608 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hsp0 : (T.regs 4 - 8#64).toNat = (s.regs 4).toNat - 616 := by rw [BitVec.toNat_sub, hspn]; simp; omega
  have hLsL1 : LiveSep L1 (win s W 40) := liveSep_W hext hLs hout hb'
  have hz1 : (s.regs 4).toNat - W ≤ (s.regs 4).toNat - 136 := by omega
  have hz2 : (s.regs 4).toNat - 136 + 32 ≤ (s.regs 4).toNat + 40 := by omega
  -- the frames
  have hMF3' := frame_push_call (q := (s.regs 4).toNat - 616) (by rw [ht4, hsp0]) ha8 (by omega) hMF3
  have hMF3w : MemFrame s1.mem V.mem (R.rt ++ win sc stkM aboveM) := by
    simp only [win, hsc4, hsp0]; exact hMF3'
  have hsc4n : (sc.regs 4).toNat = (s.regs 4).toNat - 616 := by rw [hsc4, hsp0]
  have hMFT : MemFrame s.mem sc.mem (R.rt ++ win s W 40) := by
    refine (memFrame_win hW1 hMF).trans ?_ fun _ _ h => ⟨h, h⟩
    rw [hscm]; simp only [win]; janus_frame
  have hMFall : MemFrame s.mem V.mem (R.rt ++ win s W 40) :=
    hMFT.trans (frame_TV (e := (s.regs 4).toNat) hW hab hb' hsc4n hsc4n hz1 hz2 harrR hMF2 hMF3w)
      fun _ _ h => ⟨h, by simpa only [win] using h⟩
  have hLsP : LiveSep L2 [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)] := by
    intro r hr
    have := liveSep_W (hext.trans hext2) hLs hout hb' r hr
    simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢; omega
  have hLF3' := liveFrame_push_call hLsP hLF3
  have hLFall : LiveFrame s.mem V.mem L [] := by
    have hLFpL : LiveFrame T.mem sc.mem L [] := by
      rw [hscm]; exact LiveFrame.of_win (by simp only [win]; janus_frame) hLs
    exact (hLF.trans hLFpL fun _ _ h => h).trans (liveFrame_TV hext hext2 hLs hz1 hz2 harrL hLF2 hLF3')
      fun _ _ h => h
  have hpushT : ∀ a, a + 8 ≤ (s.regs 4).toNat - 616 ∨ (s.regs 4).toNat - 616 + 8 ≤ a →
      sc.mem.readLE a 8 = T.mem.readLE a 8 := fun a h => by
    rw [hscm]; exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ h
  have hslot : ∀ a, (s.regs 4).toNat - 616 + aboveM ≤ a → a + 8 ≤ (s.regs 4).toNat + 40 →
      (a + 8 ≤ (s.regs 4).toNat - 136 ∨ (s.regs 4).toNat - 136 + 32 ≤ a) → V.mem.readLE a 8 = T.mem.readLE a 8 :=
    fun a h1 h2 h3 => by
      rw [slot_TV (q := (s.regs 4).toNat - 616) hsc4n hsc4n (hout.of_sub (by omega) (by omega)) h1 h3 harrR hMF2 hMF3w]
      exact hpushT a (by omega)
  have hMFTV : MemFrame T.mem V.mem (R.rt ++ win s W 40) := by
    have h1 : MemFrame T.mem sc.mem (R.rt ++ win s W 40) := by rw [hscm]; simp only [win]; janus_frame
    exact h1.trans (frame_TV (e := (s.regs 4).toNat) hW hab hb' hsc4n hsc4n hz1 hz2 harrR hMF2 hMF3w)
      fun _ _ h => ⟨h, by simpa only [win] using h⟩
  have hdV : Extracted.program.DataLoaded V.mem := by
    refine dataLoaded_frame64 hdS ?_ hro hMFTV fun r hr _ => ?_
    · rw [hrg3, htm, Janus.Arm64.Memory.regions_writeLE, hrg, hscm, Janus.Arm64.Memory.regions_writeLE]
    · simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [hMF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by dsimp only; omega)
  have hextB := (hext.trans hext2).trans hext3
  refine ⟨Lb, bb, ?_, h14q.trans ht14, h5q.trans (ht5.trans h5), hxq.trans (htx.trans hx0.symm),
    hfsq.trans htfs, hdfq.trans (htdf.trans hdf0.symm), ?_, ?_, ?_, hl2, hdV, ?_, ?_, ?_, hextB,
    hbfin b2 bb _ hlb hb2 hb3, hinv3, liveSep_W hextB hLs hout hb', hMFall, hLFall⟩
  · rw [h4q, ht4, hsp]; exact BitVec.sub_add_cancel _ _
  · rw [hslot _ (by omega) (by omega) (by omega)]; exact hm1
  · rw [hslot _ (by omega) (by omega) (by omega)]; exact hm2
  · rw [hslot _ (by omega) (by omega) (by omega)]; exact hs3
  · rw [hvn]
    exact beLen_le _ _ _ _ hmin (by rw [hbe]; exact lt_modLen s p len hvlt)
  · rw [hvp, hvn, hbe, hval]
  · rw [hvp, hvn]; intro h
    obtain ⟨a1, a2, -, a4, a5⟩ := hfr3 h
    exact ⟨a1, a2, a4, a5⟩

end FvModexp.Amd64.Run
