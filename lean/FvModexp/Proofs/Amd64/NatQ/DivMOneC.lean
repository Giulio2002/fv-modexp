import FvModexp.Proofs.Amd64.NatQ.DivMOneB

set_option autoImplicit false

/-!
# `nat.div` (amd64), `z = nil`, `z2 = u` (`(*Int).Mod`'s call), `len v = 1`: the `divW` call (top s39)

Twin of Arm64/NatQ/DivMOneA.lean's `one2M`: `one2Z` (DivZOne) for `z = nil` and any `len u` (`w_preM`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- at `divW`'s entry (`z = nil`, `z2 = u`, `(*Int).Mod`'s call): the call (`DivW.ens0`), then `AtW` -/
theorem one2M (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (u ul uc v vc : Nat) (s : State)
    (hp : PFM R b dc L u ul uc v 1 vc s) (X : State) (hX : AtV 0 0 0 u uc u ul uc v s X)
    (Q : State → Prop)
    (k : ∀ q ql qc L' b' T, AtW R b L 0 0 u uc u ul v 1 s q ql qc L' b' T →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) X Q := by
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hspn := sp240 hX.sp (by omega)
  have hW := w_preM hp X hX
  have hsum := wsum0 impl hap R hmk hmv hmz b L 0#64 0#64 0#64 (BitVec.ofNat 64 u) (BitVec.ofNat 64 ul) (BitVec.ofNat 64 uc)
    (BitVec.ofNat 64 (s.mem.readLE v 8))
  have hF := hX.mf
  have tu : (BitVec.ofNat 64 u).toNat = u := tN64 (by rw [← hp.su]; exact Janus.Arm64.Memory.readLE_lt _ _ _)
  have tul : (BitVec.ofNat 64 ul).toNat = ul := tN64 (by have := hp.ul9; omega)
  have ty : (BitVec.ofNat 64 (s.mem.readLE v 8)).toNat = s.mem.readLE v 8 :=
    tN64 (Janus.Arm64.Memory.readLE_lt _ _ _)
  have hra : RetAddr ((Extracted.program.onlySegments DivW.names).link impl) (X.mem.readLE (X.regs 4).toNat 8) := by
    rw [hspn, hX.rc]
    have := raD hap (ns := DivW.names) (by decide) 0xb6 (by decide)
    rw [segA] at this; exact this
  refine ReachesRet.call_regions hsum (by rw [divWE_eq]; exact hX.pc)
    ⟨hra, hX.x15, ?args, hX.df, hW⟩ (fun T hT ⟨⟨f4, f5, f14, f15⟩, hq⟩ hrg => ?_)
  case args =>
    show X.regs 0 = 0#64 ∧ X.regs 3 = 0#64 ∧ X.regs 1 = 0#64 ∧ X.regs 7 = _ ∧ X.regs 6 = _ ∧ X.regs 8 = _ ∧
      X.regs 9 = _ ∧ True
    refine ⟨by rw [hX.a0], by rw [hX.a3], by rw [hX.a1], hX.a7, hX.a6, hX.a8, hX.a9, trivial⟩
  obtain ⟨hfs, hdf, p', n', c', e0, e3, e1, e7, hv, hn, hnc, hnx, L', b', hext, hbud, hinv, hlive, hror, hMF, hLF⟩ := hq
  simp only [tu, tul, ty] at hv e7 hnx hror hbud
  -- reads at `X.mem` outside the window are those of the entry
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ a) →
      X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  have hU : natVal X.mem u ul = natVal s.mem u ul := by
    by_cases h0 : ul = 0
    · simp only [natVal, h0, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero]
    · obtain ⟨-, -, -, -, huw⟩ := hp.ui.2 (by omega)
      simp only [win, outside_cons, outside_nil, and_true] at huw
      exact hrd _ _ (by omega)
  have hV : s.mem.readLE v 8 = natVal s.mem v 1 := rfl
  rw [hU, hV] at hv e7
  have hMF' := mf_ar hMF
  have hLF' := lf_ar hLF
  have hcw : ∀ a n, Outside a n (R.rt ++ win s 41512 112 ++ ar (0#64).toNat (0#64).toNat) →
      Outside a n (R.rt ++ win X 4232 64 ++ ar (0#64).toNat (0#64).toNat) := by
    intro a n h
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢
    rw [hspn]
    exact ⟨⟨h.1.1, by omega⟩, h.2⟩
  have hfw : ∀ a n, Outside a n (R.rt ++ win s 41512 112 ++ ar (0#64).toNat (0#64).toNat) → Outside a n (proW s) := by
    intro a n h
    simp only [outside_append, win, proW, outside_cons, outside_nil, and_true] at h ⊢
    omega
  have hslot : ∀ a, (s.regs 4).toNat - 176 ≤ a → a + 8 ≤ (s.regs 4).toNat + 112 →
      T.mem.readLE a 8 = X.mem.readLE a 8 := by
    intro a ha1 ha2
    refine hMF'.readLE a 8 ?_
    simp only [outside_append, win, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by rw [hspn]; omega⟩, outside_ar fun hc => absurd hc (by decide)⟩
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
    · decide
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
