import FvModexp.Proofs.Amd64.Nat.DivBigRel
import FvModexp.Proofs.Amd64.Nat.DivOneB
import FvModexp.Proofs.Amd64.Nat.DivG

set_option autoImplicit false

/-!
# `nat.div` (amd64), `u ≥ v`: the postcondition from `divLarge`'s (pure)

`X` = `divLarge`'s entry state (`RSP - 240`, memory = the entry's with window writes), `T` = its return state, `s'` =
`T` with the result slots `RSP - 80 … RSP - 32` written. Port of `Arm64/Nat/DivBigF.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges held_apart_fresh)

namespace FvModexp.Amd64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem bigFin {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s)
    {X : State} (hsp : X.regs 4 = s.regs 4 - 240#64) (h14 : X.regs 14 = s.regs 14)
    (hF : MemFrame s.mem X.mem (win s 41512 112)) {T : State}
    {q ql qc r rl rc : Nat} {L' : List (Nat × Nat)} {b'' : Nat}
    (hq : ExpHyp.NatOF R L L' T.mem zp zc 1 q ql qc (natVal X.mem u ul / natVal X.mem v vl))
    (hr : ExpHyp.NatOF R L L' T.mem z2 z2c 1 r rl rc (natVal X.mem u ul % natVal X.mem v vl))
    (hrt : EvenHyp.RtPost R b (DivLarge.cost dc (stLen X.mem st) ul vl) L L' b'' X T)
    (hsb : StackBackL R L L' st X.mem T.mem)
    (hfr : ¬ (r = z2 ∧ rc = z2c) → 0 < rc → 0 < stCap T.mem st →
      Apart r (8 * rc) (stW T.mem st) (8 * stCap T.mem st))
    (hmf : MemFrame X.mem T.mem (R.rt ++ win X 41272 112 ++ (ar zp zc ++ ar z2 z2c) ++ stkWs X.mem st))
    (hlf : LiveFrame X.mem T.mem L ((ar zp zc ++ ar z2 z2c) ++ stkWs X.mem st))
    (s' : State) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hW : MemFrame T.mem s'.mem [((s.regs 4).toNat - 80, (s.regs 4).toNat - 32)])
    (h0 : s'.regs 0 = BitVec.ofNat 64 q) (h1 : s'.regs 3 = BitVec.ofNat 64 ql) (h2 : s'.regs 1 = BitVec.ofNat 64 qc)
    (h3 : s'.regs 7 = BitVec.ofNat 64 r) (h4 : s'.regs 6 = BitVec.ofNat 64 rl) (h5 : s'.regs 8 = BitVec.ofNat 64 rc)
    (hqr : 0 < qc → 0 < rc → Apart q (8 * qc) r (8 * rc))
    (hqf : ¬ (q = zp ∧ qc = zc) → 0 < qc → 0 < stCap T.mem st →
      Apart q (8 * qc) (stW T.mem st) (8 * stCap T.mem st)) :
    PostLG R b dc L zp zc st z2 z2c u ul v vl s s' := by
  have hp := hpre.f
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hspn := sp240 hsp (by omega)
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ a) →
      X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hsw := hp.sw
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have ew : stW X.mem st = stW s.mem st := hrd _ _ (by omega)
  have el : stLen X.mem st = stLen s.mem st := hrd _ _ (by omega)
  have ec : stCap X.mem st = stCap s.mem st := hrd _ _ (by omega)
  have ews : stkWs X.mem st = stkWs s.mem st := by simp only [stkWs, ew, el, ec]
  -- the final slots are inside the window: header reads at `s'.mem` are `T.mem`'s
  have hWr : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ a) →
      s'.mem.readLE a n = T.mem.readLE a n :=
    fun a n h => hW.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
  have tw : stW s'.mem st = stW T.mem st := hWr _ _ (by omega)
  have tl : stLen s'.mem st = stLen T.mem st := hWr _ _ (by omega)
  have tc : stCap s'.mem st = stCap T.mem st := hWr _ _ (by omega)
  have hU : natVal X.mem u ul = natVal s.mem u ul := by
    by_cases h0 : ul = 0
    · simp [natVal, h0]
    · have := hp.uo.2.2.2.2; simp only [win, outside_cons, outside_nil, and_true] at this; exact hrd _ _ (by omega)
  have hV : natVal X.mem v vl = natVal s.mem v vl := by
    have := hp.vo.2.2.2.2; simp only [win, outside_cons, outside_nil, and_true] at this; exact hrd _ _ (by omega)
  rw [hU, hV] at hq hr
  -- an array of a result: inside `R.rt` (fresh) or a non-empty input array outside the window
  have nof : ∀ (p c p' l' c' : Nat) (val : Nat), EvenHyp.WrOut R L s 41512 112 p c →
      ExpHyp.NatOF R L L' T.mem p c 1 p' l' c' val → ExpHyp.NatOF R L L' s'.mem p c 1 p' l' c' val := by
    intro p c p' l' c' val hwo ⟨a1, a2, a3, a4, a5, a6⟩
    have hk : ∀ a n, p' ≤ a → a + n ≤ p' + 8 * c' → 0 < c' → s'.mem.readLE a n = T.mem.readLE a n := by
      intro a n i1 i2 hc
      refine hWr a n ?_
      rcases a6 with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
      · have := (hwo.2.2 hc).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
      · have := outside_of_inRanges hout hin; omega
    refine ⟨?_, ?_, a3, a4, fun hc => ?_, a6⟩
    · by_cases h0 : l' = 0
      · subst h0; simpa [natVal] using a1
      · rw [← a1]; exact hk _ _ (Nat.le_refl _) (by omega) (by omega)
    · by_cases h0 : l' = 0
      · exact Or.inl h0
      · rcases a2 with h | h
        · exact absurd h h0
        · exact Or.inr (by rw [hk _ _ (by omega) (by omega) (by omega)]; exact h)
    · obtain ⟨b1, b2, b3, b4⟩ := a5 hc; exact ⟨b1, b2, by rw [hW.accessible]; exact b3, b4⟩
  obtain ⟨hext, hbud, hinv⟩ := hrt
  obtain ⟨⟨⟨hs8, hsh, hsacc, hs48, hsnl, hslc, hsc40⟩, hslen, hsor⟩, harr⟩ := hsb
  refine ⟨hfs, hdf, q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b'', nof _ _ _ _ _ _ hp.zo hq,
    nof _ _ _ _ _ _ hp.z2o hr,
    ⟨hext, ?bud, ?inv⟩, ⟨⟨⟨hs8, hsh, by rw [hW.accessible]; exact hsacc, hs48, ?nl, by rw [tl, tc]; exact hslc,
      by rw [tc]; exact hsc40⟩, by rw [tl, hslen, el], ?or⟩, ?arrL⟩, ?fr, ?mf, ?lf, hqr, ?qf⟩
  case bud => have := hp.cost; simp only [cost] at this ⊢; rw [el] at hbud; omega
  case inv =>
    rw [h14] at hinv
    refine RtInv.inv_frame' hW (fun r hr => ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    left; exact hout.of_sub (by simp only; omega) (by simp only; omega)
  case nl =>
    rw [tw, tc]; intro hc
    obtain ⟨b1, b2, b3, b4⟩ := hsnl hc; exact ⟨b1, b2, by rw [hW.accessible]; exact b3, b4⟩
  case or => rw [tw, tc, ← ew, ← ec]; exact hsor
  case arrL =>
    show ¬(stW s'.mem st = stW s.mem st ∧ stCap s'.mem st = stCap s.mem st) →
      (stW s'.mem st, stW s'.mem st + 8 * stCap s'.mem st) ∈ L' ∧ 0 < stCap s'.mem st
    rw [tw, tc, ← ew, ← ec]; exact harr
  case fr => rw [tw, tc]; exact hfr
  case qf => rw [tw, tc]; exact hqf
  case mf =>
    rw [ews] at hmf
    refine (hF.trans hmf fun a n h => ⟨?_, ?_⟩).trans hW fun a n h => ⟨h, ?_⟩
    · simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢; omega
    · simp only [outside_append] at h ⊢
      refine ⟨⟨⟨h.1.1.1, ?_⟩, outside_ar_of ?_, outside_ar_of ?_⟩, h.2⟩
      · exact winX hspn hb' h.1.1.2
      · have := h.1.2; simp only [outside_cons, outside_nil, and_true] at this ⊢; exact this.1
      · have := h.1.2; simp only [outside_cons, outside_nil, and_true] at this ⊢; exact this.2
    · simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢; omega
  case lf =>
    refine ⟨fun a n hin ho => ?_⟩
    obtain ⟨rr, hr', i1, i2⟩ := hin
    have := hLs rr hr'
    simp only [win, outside_cons, outside_nil, and_true] at this
    rw [hWr a n (by omega), hlf.readLE a n ⟨rr, hr', i1, i2⟩ ?_]
    · exact hF.readLE a n (by simp only [win, outside_cons, outside_nil, and_true]; omega)
    · rw [ews]
      simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      exact ⟨⟨outside_ar_of (by simp only [outside_cons, outside_nil, and_true]; exact ho.1.1),
        outside_ar_of (by simp only [outside_cons, outside_nil, and_true]; exact ho.1.2)⟩, ho.2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `divLarge` keeps `nat.div`'s return address, saved `RBP`, defer bit -/
theorem slots_keep {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s)
    {X : State} (hsp : X.regs 4 = s.regs 4 - 240#64) (hF : MemFrame s.mem X.mem (win s 41512 112)) {T : State}
    (hmf : MemFrame X.mem T.mem (R.rt ++ win X 41272 112 ++ (ar zp zc ++ ar z2 z2c) ++ stkWs X.mem st))
    (a n : Nat) (ha : (s.regs 4).toNat - 122 ≤ a ∧ a + n ≤ (s.regs 4).toNat + 8) :
    T.mem.readLE a n = X.mem.readLE a n := by
  have hp := hpre.f
  obtain ⟨-, ⟨hb', ha', hw⟩, -, -, hout, -⟩ := hp.ce
  simp only [regSP] at hb' ha' hw
  have hspn := sp240 hsp (by omega)
  have hsw := hp.sw
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hrd : ∀ a' n', (a' + n' ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ a') →
      X.mem.readLE a' n' = s.mem.readLE a' n' :=
    fun a' n' h => hF.readLE a' n' (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have ew : stW X.mem st = stW s.mem st := hrd _ _ (by omega)
  have el : stLen X.mem st = stLen s.mem st := hrd _ _ (by omega)
  have ec : stCap X.mem st = stCap s.mem st := hrd _ _ (by omega)
  have hfree : a + n ≤ stW s.mem st + 8 * stLen s.mem st ∨ stW s.mem st + 8 * stCap s.mem st ≤ a := by
    by_cases hc : 0 < stCap s.mem st
    · have := (hp.sa hc).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · have := hp.w0 (by omega); rw [this]; omega
  have hz1 : 0 < zc → a + n ≤ zp ∨ zp + 8 * zc ≤ a := fun hc => by
    have := (hp.zo.2.2 hc).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have hz2 : 0 < z2c → a + n ≤ z2 ∨ z2 + 8 * z2c ≤ a := fun hc => by
    have := (hp.z2o.2.2 hc).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have hrt : Outside a n R.rt := hout.of_sub (by omega) (by omega)
  refine hmf.readLE a n ?_
  simp only [outside_append, stkWs, win, outside_cons, outside_nil, and_true, ew, el, ec, hspn]
  exact ⟨⟨⟨hrt, by omega⟩, outside_ar hz1, outside_ar hz2⟩, by omega, hfree⟩

end FvModexp.Amd64.NatDiv
