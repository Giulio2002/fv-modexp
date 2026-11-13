import FvModexp.Proofs.Amd64.Nat.DivLessRel
import FvModexp.Proofs.Amd64.Nat.WordTData
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `nat.div` (amd64), `u < v`, `cap z2 < len u`: `r = make(nat, len u)` = `makeslice(Word, len u, makeCap (len u))`
→ `AtS` (`len u = 1`: `(1, 1)` at `fn + 0x240`; else `(len u, len u + 4)` at `fn + 0x272`, `len u + 4` spilled at
`SP - 120`). Port of `Arm64/Nat/DivLess.lean`'s `lessA`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option janus.callRegions true in
theorem lessA (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibDiv.program.link impl) (cA "runtime.makeslice") 4096 R)
    {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) {S : State}
    (hS : AtC zp zl zc st z2 z2l z2c u ul uc v vl vc s S) (hr0 : S.regs 0 = 18446744073709551615#64)
    (hz : z2c < ul) (Q : State → Prop)
    (k : ∀ S' p c L' b', AtS R b L zp zc z2 z2c u ul s p c L' b' S' →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) S Q := by
  have hp := hpre.f
  have hce := hp.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, ⟨htg, htr, htw⟩⟩ := hp.ce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw hal
  unfold Apart at hga htw
  have hinv0 := hp.inv
  have hul := hp.ul9
  have hz40 := hp.z2o.1
  have hsv := hp.sv
  have hcost := hp.cost
  obtain ⟨hinv1, hmf1, hlf1⟩ := winOnly hce hinv0 hS.mf
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hx15 := hS.x15; have hdf := hS.df
  have hacc := hS.mf.accessible
  have hSacc : S.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by rw [hacc]; exact hw
  have hgacc : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hacc]; exact hg2
  have hgS : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hS.mf.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have htS : S.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [hS.mf.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)]; exact htg.g
  have hTt : S.mem.accessible (s.fsBase.toNat - 8) 8 false = true := by rw [hacc]; exact htg.readable
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 41512) (41512 + 112) := apart_of_data hd 1 (by decide) (by decide) hw
  unfold Apart at hwt
  have hWr : ∀ a n, wordT ≤ a → a + n ≤ wordT + 16 → S.mem.readLE a n = s.mem.readLE a n := fun a n h1 h2 =>
    hS.mf.readLE a n (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hmc : makeCost ul ≤ b := by simp only [cost] at hcost; omega
  have hok1 : R.ok (cA "runtime.makeslice") [wordT, ul, makeCap ul] := hsv.1 _ _ _ (by unfold makeCap; split <;> omega)
  have hbl := blockSize_le_allocCost (8 * makeCap ul) true
  have hbs : blockSize (8 * makeCap ul) true ≤ b := by unfold makeCost at hmc; omega
  have hLs1 : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ r.1 := fun r hr => by
    have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have m0 := hS.ra; have m1 := hS.bp; have m3 := hS.s1; have m4 := hS.s3; have m5 := hS.s5; have m6 := hS.s7
  have m7 := hS.s8; have m8 := hS.s9
  have hreg := hS.reg
  have hzp : zp < 2 ^ 64 := by rw [← hS.s1]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := by rw [← hS.s3]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  obtain ⟨hwa, hws, hwp⟩ := FvModexp.Amd64.wordT_data hd
  janus_eval_nat h_t : wordT
  rw [h_t] at hty hok1 hwt hWr
  have hT1 : S.mem.readLE 7233184 8 = 8 := (hWr _ _ (by omega) (by omega)).trans hws
  have hT2 : S.mem.readLE 7233192 8 = 0 := (hWr _ _ (by omega) (by omega)).trans hwp
  have hTa : S.mem.accessible 7233184 16 false = true := (hacc _ _ _).trans hwa
  clear hpre hp hS hce hinv0 hWr
  by_cases h1 : ul = 1
  · subst h1
    have hc1 : makeCap 1 = 1 := rfl
    rw [hc1] at hok1 hbs hbl
    janus64_run [hr0, m0, m1, m3, m4, m5, m6, m7, m8, hT1, hT2, hTa, hgS, htS, BitVec.msb_eq_decide] until [joinS]
      calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc' h8 _ _ _ _ hinv' _ _ _
    have hpo := FvModexp.Amd64.NatAdd.outside_of_inRanges hout hIn
    have hmo : ∀ a n, (s.regs 4).toNat - 208 ≤ a → a + n ≤ (s.regs 4).toNat + 112 →
        Outside a n (R.rt ++ [((s.regs 4).toNat - 240 - 4096, (s.regs 4).toNat - 240),
          ((s.regs 4).toNat - 240 + 8, (s.regs 4).toNat - 240 + 8 + 24)]) := fun a n h1 h2 => by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
    refine k _ ptr.toNat 1 (L ++ [(ptr.toNat, ptr.toNat + 8)]) (b - 8)
      { pc := rfl, sp := ?_, r5 := ?_, r14 := ?_, fs := ?_, x15 := ?_, df := ?_, r0 := ?_, r1 := ?_, r3 := ?_, r2 := ?_
        arr := Or.inr ⟨hz, Nat.le_refl _, by omega, h8, by omega, by simpa using hIn, by simpa using hAp,
          ⟨(ptr.toNat, ptr.toNat + 8), by simp, by simp only; omega, by simp only; omega⟩, ?acc⟩
        ext := LiveExt.single (by simpa using hIn) (by simpa using hAp)
        bud := by have : makeCost 1 = 40 := by unfold makeCost makeCap allocCost; rfl
                  omega
        inv := by simpa using hinv'
        mf := hmf1.trans ((by janus_frame : MemFrame S.mem _ [((s.regs 4).toNat - 240, (s.regs 4).toNat - 32)]).trans
          hMF (rs'' := R.rt ++ win s 41512 112) fun a n h => ?mf2) fun a n h => ⟨h, h⟩
        lf := ⟨fun a n hin ho => ?lf⟩
        reg := ?_, ra := ?_, bp := ?_, q0 := ?_, q1 := ?_, q2 := ?_, s8 := ?_ }
    case acc =>
      rw [hMF.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hacc]; exact hacc'
    case mf2 =>
      simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨by omega, h.1, by omega, by omega⟩
    case lf =>
      obtain ⟨r, hr, i1, i2⟩ := hin
      have := hLs1 r hr
      rw [hLF.readLE a n ⟨r, hr, i1, i2⟩ trivial,
        (by janus_frame : MemFrame S.mem _ [((s.regs 4).toNat - 240, (s.regs 4).toNat - 32)]).readLE a n
          (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact hlf1.readLE a n ⟨r, hr, i1, i2⟩ ho
    all_goals try (janus64_simp; done)
    all_goals try (rw [hrg1]; exact hreg)
    all_goals try (rw [hMF.readLE _ _ (hmo _ _ (by omega) (by omega))]
                   simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
                     FvModexp.Expmc.readLE_writeLE_same, m0, m1, m7]
                   done)
    all_goals first | exact hx15 | exact hdf | exact hfs | (janus64_simp; omega)
  · have hcN : makeCap ul = ul + 4 := by unfold makeCap; rw [if_neg h1]
    rw [hcN] at hok1 hbs hbl
    have h1' : (BitVec.ofNat 64 ul = 1#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    janus64_run [hr0, m0, m1, m3, m4, m5, m6, m7, m8, hT1, hT2, hTa, hgS, htS, h1', BitVec.msb_eq_decide] until [joinS]
      calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc' h8 _ _ hsz _ hinv' _ _ _
    have h8' : ptr.toNat % 8 = 0 := h8 (Or.inr (by omega))
    have hmc' : makeCost ul = allocCost (8 * (ul + 4)) := by unfold makeCost; rw [hcN]
    have hbl' := blockSize_le_allocCost (8 * (ul + 4)) true
    have hpo := FvModexp.Amd64.NatAdd.outside_of_inRanges hout hIn
    have hmo : ∀ a n, (s.regs 4).toNat - 208 ≤ a → a + n ≤ (s.regs 4).toNat + 112 →
        Outside a n (R.rt ++ [((s.regs 4).toNat - 240 - 4096, (s.regs 4).toNat - 240),
          ((s.regs 4).toNat - 240 + 8, (s.regs 4).toNat - 240 + 8 + 24)]) := fun a n h1 h2 => by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
    have hmo2 : ∀ a n, (s.regs 4).toNat - 120 ≤ a → a + n ≤ (s.regs 4).toNat - 112 →
        Outside a n (R.rt ++ [((s.regs 4).toNat - 240 - 4096, (s.regs 4).toNat - 240),
          ((s.regs 4).toNat - 240 + 8, (s.regs 4).toNat - 240 + 8 + 24)]) := fun a n h1 h2 => by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
    refine k _ ptr.toNat (ul + 4) (L ++ [(ptr.toNat, ptr.toNat + blockSize (8 * (ul + 4)) true)])
      (b - blockSize (8 * (ul + 4)) true)
      { pc := rfl, sp := ?_, r5 := ?_, r14 := ?_, fs := ?_, x15 := ?_, df := ?_, r0 := ?_, r1 := ?_, r3 := ?_, r2 := ?_
        arr := Or.inr ⟨hz, by omega, Nat.le_refl _, h8', by omega, hIn.sub (Nat.le_refl _) (by omega),
          fun r hr => (hAp r hr).mono hsz (Nat.le_refl _),
          ⟨(ptr.toNat, ptr.toNat + blockSize (8 * (ul + 4)) true), by simp, by simp only; omega, by simp only; omega⟩,
          ?acc⟩
        ext := LiveExt.single (by simpa using hIn) (by simpa using hAp)
        bud := by omega
        inv := hinv'
        mf := hmf1.trans ((by janus_frame : MemFrame S.mem _ [((s.regs 4).toNat - 240, (s.regs 4).toNat - 32)]).trans
          hMF (rs'' := R.rt ++ win s 41512 112) fun a n h => ?mf2) fun a n h => ⟨h, h⟩
        lf := ⟨fun a n hin ho => ?lf⟩
        reg := ?_, ra := ?_, bp := ?_, q0 := ?_, q1 := ?_, q2 := ?_, s8 := ?_ }
    case acc =>
      rw [hMF.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hacc]
      exact Janus.Arm64.Memory.accessible_mono _ hacc' (Nat.le_refl _) (by omega)
    case mf2 =>
      simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨by omega, h.1, by omega, by omega⟩
    case lf =>
      obtain ⟨r, hr, i1, i2⟩ := hin
      have := hLs1 r hr
      rw [hLF.readLE a n ⟨r, hr, i1, i2⟩ trivial,
        (by janus_frame : MemFrame S.mem _ [((s.regs 4).toNat - 240, (s.regs 4).toNat - 32)]).readLE a n
          (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact hlf1.readLE a n ⟨r, hr, i1, i2⟩ ho
    all_goals try (janus64_simp; done)
    all_goals try (rw [hrg1]; exact hreg)
    all_goals try (rw [hMF.readLE _ _ (hmo _ _ (by omega) (by omega))]
                   simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
                     FvModexp.Expmc.readLE_writeLE_same, m0, m1, m7]
                   done)
    all_goals first | exact hx15 | exact hdf | exact hfs | (janus64_simp; omega)

end FvModexp.Amd64.NatDiv
