import FvModexp.Proofs.Amd64.NatQ.DivOneB
import FvModexp.Proofs.Amd64.Nat.DivW0
import FvModexp.Proofs.Amd64.NatQ.DivG

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivZOne.lean, TIGHT COSTS, top s38)
# `nat.div` (amd64), empty dividend (`ul = 0`, `u` possibly nil; `ExpSlow.DivHypLG`), `len v = 1`: `divW`

Twin of `Arm64/Nat/DivZOne.lean`: `wsum0` (`DivW.ens0` as a summary in `LibDiv`), `w_preZ`/`one2Z` = `w_pre`/`one2`
(DivOneB) from `PreG` with `ul = 0`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv
variable {H : Nat}

set_option linter.defProp false in
/-- `nat.divW` (`DivW.ens0`) as a summary in `LibDiv.program.link impl` -/
def wsum0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :=
  Ensures.toSummaryIn (DivW.ens0 impl hap R hmk hmv hmz b L zp zl zc xp xl xc y) (A64.noExit_restrict64 hap DivW.names)
    (by simp [numIntRegs])
    (show CodeIn64 ((Extracted.program.onlySegments DivW.names).link impl) (LibDiv.program.link impl) by
      rw [LibDiv.eq_only]; exact A64.codeIn_restrict_mono64 hap (Callees.sub_of_all (by decide)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `DivW.Pre0` at `divW`'s entry for an empty dividend (`ul = 0`, any pointer; pure) -/
theorem w_preZ {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c : BitVec 64} {u ul uc v vc : Nat} {s : State}
    (hpre : PreG R b H dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v 1 vc s)
    (hu : ul = 0) (X : State) (hX : AtV zp.toNat zl.toNat zc.toNat z2.toNat z2c.toNat u ul uc v s X) :
    DivW.Pre0 R b L zp zc (BitVec.ofNat 64 u) (BitVec.ofNat 64 ul) (BitVec.ofNat 64 (s.mem.readLE v 8)) X := by
  have hp := hpre.f
  have hce0 := hp.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, hro, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hF := hX.mf
  have hspn := sp240 hX.sp (by omega)
  have hFw : MemFrame s.mem X.mem (win s 41512 112) := hF.mono fun a n h => by
    simp only [win, proW, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hce : CallEnv R L X 4232 64 :=
    CallEnv.callee hce0 hspn hX.r14 hX.fs (by decide) (by decide) (by decide) hFw hX.reg
  obtain ⟨hz40, hzl, hzw⟩ := hp.zo
  have hv0 : s.mem.readLE v 8 ≠ 0 := by
    rcases hp.vn with h | h
    · omega
    · simpa using h
  have hsv := hp.sv
  have tul : (BitVec.ofNat 64 ul).toNat = ul := by rw [hu]; rfl
  have ty : (BitVec.ofNat 64 (s.mem.readLE v 8)).toNat = s.mem.readLE v 8 :=
    tN64 (Janus.Arm64.Memory.readLE_lt _ _ _)
  unfold DivW.Pre0
  rw [tul, ty]
  refine ⟨hce, hro.out' 1 (by decide) (by decide), hv0, by omega, hz40, ?_, ?_, ?_, fun h => absurd h (by omega),
    Or.inl hu, ?_, fun h => absurd h (by omega), fun d sr k hk => hsv.2.1 d sr k (by omega)⟩
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzl hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · intro hc
    have := (hzw hc).1
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hspn]; omega
  · intro hc
    exact ⟨by rw [hX.r14]; exact (hzw hc).2.1, by rw [hX.fs]; exact (hzw hc).2.2, fun h => absurd h (by omega)⟩
  · rw [hX.r14]
    refine RtInv.inv_frame' hF (fun r hr => ?_) hp.inv
    simp only [proW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- at `divW`'s entry, `ul = 0` (`u` possibly nil): the call (`DivW.ens0`), then `AtW` -/
theorem one2Z (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c : BitVec 64) (u ul uc v vc : Nat) (s : State)
    (hpre : PreG R b H dc L zp.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u ul uc v 1 vc s)
    (hu : ul = 0) (X : State) (hX : AtV zp.toNat zl.toNat zc.toNat z2.toNat z2c.toNat u ul uc v s X)
    (Q : State → Prop)
    (k : ∀ q ql qc L' b' T, AtW R b L zp.toNat zc.toNat z2.toNat z2c.toNat u ul v 1 s q ql qc L' b' T →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) X Q := by
  have hp := hpre.f
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hspn := sp240 hX.sp (by omega)
  have hzw := hp.zo.2.2
  have hW := w_preZ hpre hu X hX
  have hsum := wsum0 impl hap R hmk hmv hmz b L zp zl zc (BitVec.ofNat 64 u) (BitVec.ofNat 64 ul) (BitVec.ofNat 64 uc)
    (BitVec.ofNat 64 (s.mem.readLE v 8))
  have hF := hX.mf
  have tu : (BitVec.ofNat 64 u).toNat = u := tN64 (by rw [← hp.ru]; exact Janus.Arm64.Memory.readLE_lt _ _ _)
  have tul : (BitVec.ofNat 64 ul).toNat = ul := by rw [hu]; rfl
  have ty : (BitVec.ofNat 64 (s.mem.readLE v 8)).toNat = s.mem.readLE v 8 :=
    tN64 (Janus.Arm64.Memory.readLE_lt _ _ _)
  have hra : RetAddr ((Extracted.program.onlySegments DivW.names).link impl) (X.mem.readLE (X.regs 4).toNat 8) := by
    rw [hspn, hX.rc]
    have := raD hap (ns := DivW.names) (by decide) 0xb6 (by decide)
    rw [segA] at this; exact this
  refine ReachesRet.call_regions hsum (by rw [divWE_eq]; exact hX.pc)
    ⟨hra, hX.x15, ?args, hX.df, hW⟩ (fun T hT ⟨⟨f4, f5, f14, f15⟩, hq⟩ hrg => ?_)
  case args =>
    show X.regs 0 = zp ∧ X.regs 3 = zl ∧ X.regs 1 = zc ∧ X.regs 7 = _ ∧ X.regs 6 = _ ∧ X.regs 8 = _ ∧
      X.regs 9 = _ ∧ True
    refine ⟨by rw [hX.a0]; simp, by rw [hX.a3]; simp, by rw [hX.a1]; simp, hX.a7, hX.a6, hX.a8, hX.a9, trivial⟩
  obtain ⟨hfs, hdf, p', n', c', e0, e3, e1, e7, hv, hn, hnc, hnx, L', b', hext, hbud, hinv, hlive, hror, hMF, hLF⟩ := hq
  simp only [tu, tul, ty] at hv e7 hnx hror hbud
  -- reads at `X.mem` outside the window are those of the entry
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ a) →
      X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  have hU : natVal X.mem u ul = natVal s.mem u ul := by
    simp only [natVal, hu, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero]
  have hV : s.mem.readLE v 8 = natVal s.mem v 1 := rfl
  rw [hU, hV] at hv e7
  have hMF' := mf_ar hMF
  have hLF' := lf_ar hLF
  have hcw : ∀ a n, Outside a n (R.rt ++ win s 41512 112 ++ ar zp.toNat zc.toNat) →
      Outside a n (R.rt ++ win X 4232 64 ++ ar zp.toNat zc.toNat) := by
    intro a n h
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢
    rw [hspn]
    exact ⟨⟨h.1.1, by omega⟩, h.2⟩
  have hfw : ∀ a n, Outside a n (R.rt ++ win s 41512 112 ++ ar zp.toNat zc.toNat) → Outside a n (proW s) := by
    intro a n h
    simp only [outside_append, win, proW, outside_cons, outside_nil, and_true] at h ⊢
    omega
  have hslot : ∀ a, (s.regs 4).toNat - 176 ≤ a → a + 8 ≤ (s.regs 4).toNat + 112 →
      T.mem.readLE a 8 = X.mem.readLE a 8 := by
    intro a ha1 ha2
    refine hMF'.readLE a 8 ?_
    simp only [outside_append, win, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by rw [hspn]; omega⟩, outside_ar fun hc => ?_⟩
    have := (hzw hc).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  refine k p' n' c' L' b' T
    { pc := by rw [hT, retAddrOf, hspn, hX.rc]
      sp := by rw [f4, hX.sp]; bv_omega
      r5 := by rw [f5, hX.r5]
      r14 := by rw [f14, hX.r14]
      fs := by rw [hfs, hX.fs]
      x15 := by rw [f15, hX.x15]
      df := by rw [hdf, hX.df]
      r0 := by rw [← e0]; simp
      r3 := by rw [← e3]; simp
      r1 := by rw [← e1]; simp
      r7 := e7
      hq := ⟨hv, hn, hnc, ?c40, hlive, ?ror⟩
      ext := hext
      bud := hbud
      inv := by rw [← hX.r14]; exact hinv
      mf := hF.trans hMF' fun a n h => ⟨hfw a n h, hcw a n h⟩
      lf := ⟨fun a n hin ho => ?lf⟩
      reg := by rw [hrg, hX.reg]
      ra := by rw [hslot _ (by omega) (by omega)]; exact hF.readLE _ _ (by
        simp only [proW, outside_cons, outside_nil, and_true]; omega)
      bp := by rw [hslot _ (by omega) (by omega)]; exact hX.bp
      s5 := by rw [hslot _ (by omega) (by omega)]; exact hX.s5
      s7 := by rw [hslot _ (by omega) (by omega)]; exact hX.s7 }
  case c40 =>
    rcases hror with ⟨rfl, rfl⟩ | ⟨-, -, h2, -⟩
    · exact hp.zo.1
    · have := hp.ul9; omega
  case ror =>
    rcases hror with ⟨rfl, rfl⟩ | ⟨h1, h2, -, hin, hap'⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨by omega, hin, hap'⟩
  case lf =>
    rw [hLF'.readLE a n hin ho]
    refine hF.readLE a n ?_
    obtain ⟨r, hr, i1, i2⟩ := hin
    have := hLs r hr
    simp only [win, proW, outside_cons, outside_nil, and_true] at this ⊢
    omega

end FvModexp.Amd64.Q.NatDiv
