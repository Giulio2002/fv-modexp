import FvModexp.Proofs.Arm64.Nat.DivOneB
import FvModexp.Proofs.Arm64.Nat.DivMBase
import FvModexp.Proofs.Arm64.Nat.DivG

set_option autoImplicit false

/-!
# `nat.div` (arm64), empty dividend (`ul = 0`, `u` possibly nil; `ExpSlow.DivHypLG`, asm s35), `len v = 1`: `divW`

`w_preZ`/`one2Z` = `w_pre`/`one2` (DivOneB) from `PreG` with `ul = 0`, calling `divW` through `DivW.ens0` (`wsum0`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `DivW.Pre0` at `divW`'s entry for an empty dividend (`ul = 0`, any pointer; pure) -/
theorem w_preZ {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c up ul vp : BitVec 64} {s : State}
    (hpre : PreG R b dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat up.toNat ul.toNat vp.toNat 1 s)
    (hu : ul.toNat = 0)
    (X : State) (hsp : X.sp = s.sp - 240#64) (h28 : X.regs 28 = s.regs 28) (hF : MemFrame s.mem X.mem (proW s))
    (hreg : X.mem.regions = s.mem.regions) :
    DivW.Pre0 R b L zp zc up ul (BitVec.ofNat 64 (s.mem.readLE vp.toNat 8)) X := by
  have hp := hpre.f
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hp.ce
  have hspn := sp240 hsp (by omega)
  have hFw : MemFrame s.mem X.mem (win s 41504 112) := hF.mono fun a n h => by
    simp only [win, proW, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hce : CallEnv R L X 4240 64 := CallEnv.callee hp.ce hspn h28 (by decide) (by decide) (by decide) hFw hreg
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ a) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  obtain ⟨hz40, hzl, hzw⟩ := hp.zo
  have hvn := hp.vn
  have hv0 : s.mem.readLE vp.toNat 8 ≠ 0 := by
    rcases hvn with h | h
    · omega
    · simpa using h
  have hul9 := hp.ul9
  have hcost := hp.cost
  have hsv := hp.sv
  refine ⟨hce, hro.out' 1 (by decide) (by decide), ?_, by omega, hz40, ?_, ?_, ?_, fun h => absurd h (by omega),
    Or.inl hu, ?_, fun h => absurd h (by omega), fun d sr k hk => hsv.2.1 d sr k (by omega)⟩
  · rw [tN (Memory.readLE_lt _ _ _)]; exact hv0
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzl hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · intro hc
    have := (hzw hc).1
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hspn]; omega
  · intro hc
    exact ⟨by rw [h28]; exact (hzw hc).2, fun h => absurd h (by omega)⟩
  · rw [h28]
    refine RtInv.inv_frame' hF (fun r hr => ?_) hp.inv
    simp only [proW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- at `divW`'s entry, `ul = 0` (`u` possibly nil): the call (`DivW.ens0`), then `AtW` -/
theorem one2Z (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c up ul uc vp : BitVec 64) (s : State)
    (hpre : PreG R b dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat up.toNat ul.toNat vp.toNat 1 s)
    (hu : ul.toNat = 0) (X : State) (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program DivW.fn)) (hsp : X.sp = s.sp - 240#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 248#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 retW) (hr0 : X.regs 0 = zp) (hr1 : X.regs 1 = zl) (hr2 : X.regs 2 = zc)
    (hr3 : X.regs 3 = up) (hr4 : X.regs 4 = ul) (hr5 : X.regs 5 = uc)
    (hr6 : X.regs 6 = BitVec.ofNat 64 (s.mem.readLE vp.toNat 8))
    (hF : MemFrame s.mem X.mem (proW s)) (hreg : X.mem.regions = s.mem.regions)
    (hlr : X.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat)
    (hfp : X.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat)
    (hs5 : X.mem.readLE (s.sp.toNat + 40) 8 = z2.toNat) (hs7 : X.mem.readLE (s.sp.toNat + 56) 8 = z2c.toNat)
    (Q : State → Prop)
    (k : ∀ q ql qc L' b' T, AtW R b L zp.toNat zc.toNat z2.toNat z2c.toNat up.toNat ul.toNat vp.toNat 1 s q ql qc L' b' T →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q := by
  have hp := hpre.f
  have hspn := sp240 hsp (by have := hp.ce.2.1.2.1; omega)
  have hb' := hp.ce.2.1.2.1
  have hout := hp.ce.2.2.2.1
  have hLs := hp.ce.2.2.2.2.2.2.1
  have hzw := hp.zo.2.2
  have hW := w_preZ hpre hu X hsp h28 hF hreg
  have hsum := wsum0 impl hap R hmk hmv hmz b L zp zl zc up ul uc (BitVec.ofNat 64 (s.mem.readLE vp.toNat 8))
  have e30 : (X.regs 30).toNat = retW := by rw [h30]; decide
  refine ReachesRet.call_regions hsum hpc ⟨?ra, ?args, hW⟩ (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [e30]; exact raD impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom]
    exact ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, trivial⟩
  obtain ⟨p', n', c', e0, e1, e2, e3, hv, hn, hnc, hnx, L', b', hext, hbud, hinv, hlive, hror, hMF, hLF⟩ := hq
  -- reads at `X.mem` outside the window are those of the entry
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 41504 ∨ s.sp.toNat + 112 ≤ a) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  have hU : natVal X.mem up.toNat ul.toNat = natVal s.mem up.toNat ul.toNat := by
    simp only [natVal, hu, Nat.mul_zero, Memory.readLE_zero]
  have hV : (BitVec.ofNat 64 (s.mem.readLE vp.toNat 8)).toNat = natVal s.mem vp.toNat 1 := by
    rw [tN (Memory.readLE_lt _ _ _)]
  rw [hU, hV] at hv e3
  -- the callee's frame inside ours
  have hcw : ∀ a n, Outside a n (R.rt ++ winA s 41504 112 ++ ar zp.toNat zc.toNat) →
      Outside a n (R.rt ++ winA X 4240 64 ++ DivW.zr zp zc) := by
    intro a n h
    rw [← ar_zr]
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
    rw [hspn]
    exact ⟨⟨h.1.1, by omega, by omega⟩, h.2⟩
  have hfw : ∀ a n, Outside a n (R.rt ++ winA s 41504 112 ++ ar zp.toNat zc.toNat) → Outside a n (proW s) := by
    intro a n h
    simp only [outside_append, winA, proW, outside_cons, outside_nil, and_true] at h ⊢
    omega
  have hslot : ∀ a, (s.sp.toNat - 248 ≤ a ∧ a + 8 ≤ s.sp.toNat - 232) ∨ (s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 112) →
      T.mem.readLE a 8 = X.mem.readLE a 8 := by
    intro a ha'
    refine hMF.readLE a 8 ?_
    rw [← ar_zr]
    simp only [outside_append, winA, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by rw [hspn]; omega, by rw [hspn]; omega⟩,
      outside_ar fun hc => ?_⟩
    have := (hzw hc).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  refine k p' n' c' L' b' T
    { pc := by rw [hT, h30]
      sp := by rw [f1, hsp]
      r28 := by rw [f2, h28]
      r29 := by rw [f3, h29]
      r18 := by rw [f4, h18]
      r0 := by rw [← e0]; simp
      r1 := by rw [← e1]; simp
      r2 := by rw [← e2]; simp
      r3 := e3
      hq := ⟨hv, hn, hnc, ?c40, hlive, ?ror⟩
      ext := hext
      bud := hbud
      inv := by rw [← h28]; exact hinv
      mf := hF.trans hMF fun a n h => ⟨hfw a n h, hcw a n h⟩
      lf := ⟨fun a n hin ho => ?lf⟩
      reg := by rw [hrg, hreg]
      lr := by rw [hslot _ (Or.inl ⟨by omega, by omega⟩)]; exact hlr
      fp := by rw [hslot _ (Or.inl ⟨by omega, by omega⟩)]; exact hfp
      s5 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact hs5
      s7 := by rw [hslot _ (Or.inr ⟨by omega, by omega⟩)]; exact hs7 }
  case c40 =>
    rcases hror with ⟨rfl, rfl⟩ | ⟨-, -, h2, -⟩
    · exact hp.zo.1
    · have := hp.ul9; omega
  case ror =>
    rcases hror with ⟨rfl, rfl⟩ | ⟨h1, h2, -, hin, hap'⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨by omega, hin, hap'⟩
  case lf =>
    rw [hLF.readLE a n hin (by rw [← ar_zr]; exact ho)]
    refine hF.readLE a n ?_
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs r hr
    simp only [win, proW, outside_cons, outside_nil, and_true] at this ⊢
    omega

end FvModexp.Arm64.NatDiv
