import FvModexp.Proofs.Amd64.Exp.P2DRecH

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): `z.lsh(z, lo)`'s exit facts are ours (agent asm s70; port of infra's arm64
`P2DRet.cpostR_lsh`)

`cpostR_lsh`: the recursive call's `CPostR` (result `(p2, l2, c2)`, memory `M3`) followed by `lsh`'s result
(`NatRes`, memory `M4`, `z = x = (p2, c2)`) give our `NHyp.CPostR`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp FvModexp.Amd64.EvenHyp

/-- a held read through a frame whose written ranges are each empty or apart from the read (per byte) -/
theorem held_rd {R : RtInv} {L ws : List (Nat × Nat)} {m m' : Memory} {a k : Nat} (hh : Held R L a k)
    (hf : MemFrame m m' (R.rt ++ ws)) (hl : LiveFrame m m' L ws)
    (ho : ∀ r ∈ ws, r.2 ≤ r.1 ∨ a + k ≤ r.1 ∨ r.2 ≤ a) : m'.readLE a k = m.readLE a k := by
  refine Janus.Arm64.Memory.readLE_congr fun j hj => ?_
  have h1 := (hh.sub (a := a + j) (n := 1) (by omega) (by omega)).readLE hf hl (outside_of_forall fun r hr => by
    rcases ho r hr with q | q | q <;> omega)
  simp only [Janus.Arm64.Memory.readLE_one] at h1
  exact BitVec.eq_of_toNat_eq h1

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the exit composition** (see the module doc) -/
theorem cpostR_lsh (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s)
    {M3 M4 : Memory} {p2 l2 c2 : Nat} {L2 : List (Nat × Nat)} {b2 v cst1 : Nat}
    (hr : NatOF R L L2 M3 zp zc 1 p2 l2 c2 v) (hx2 : LiveExt R L L2) (hb2 : b - cst1 ≤ b2)
    (hsb : StackBackL R L L2 st s.mem M3)
    (hF1 : MemFrame s.mem M3 (R.rt ++ win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st))
    (hLF1 : LiveFrame s.mem M3 L ([(zp, zp + 8 * zc)] ++ stWs s.mem st)) (hrs : ResSep s.mem M3 st p2 c2)
    {cw : List (Nat × Nat)} (hcw : ∀ a k, Outside a k (win s stk A) → Outside a k cw)
    {nd p' l' c' w : Nat} {L3 : List (Nat × Nat)} {b3 : Nat}
    (hr' : NatRes R L2 L3 M4 p2 c2 nd p' l' c' w) (hcap : c2 < nd → nd ≤ c') (hnd : 1 ≤ nd)
    (hx3 : LiveExt R L2 L3) (hb3 : b2 - makeCost nd ≤ b3)
    (hinv : R.inv b3 L3 (s.regs 14).toNat (view R.rt L3 M4))
    (hF2 : MemFrame M3 M4 (R.rt ++ cw ++ [(p2, p2 + 8 * c2)])) (hLF2 : LiveFrame M3 M4 L2 [(p2, p2 + 8 * c2)])
    {cst2 : Nat} (hc : cst1 + makeCost nd ≤ cst2)
    {s' : State} (hm : s'.mem = M4) (e0 : s'.regs 0 = BitVec.ofNat 64 p') (e1 : s'.regs 3 = BitVec.ofNat 64 l')
    (e2 : s'.regs 1 = BitVec.ofNat 64 c') (efs : s'.fsBase = s.fsBase) (edf : s'.df = s.df) :
    NHyp.CPostR R b L stk A zp zc st w cst2 s s' := by
  have hsok := hP.2.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.1
  have hzst := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨hok2, hl2, hkf2⟩, hai2⟩ := hsb
  obtain ⟨hv, hn, hlc, hc40, hlive, hloc⟩ := hr
  obtain ⟨hv', hn', hlc', hc40', hlive', hke', hfr'⟩ := hr'
  -- the stack header is kept by `lsh`
  have hstcw : Outside st 24 cw := hcw _ _ (by
    simp only [win, outside_cons, outside_nil, and_true] at hstw ⊢; omega)
  have hst2 : (p2 + 8 * c2) ≤ p2 ∨ st + 24 ≤ p2 ∨ p2 + 8 * c2 ≤ st := by
    rcases hloc with ⟨q1, q2⟩ | ⟨h1, hin, hap⟩
    · rw [q1, q2]
      rcases Nat.eq_zero_or_pos zc with h0 | h0
      · left; omega
      · have := (hzst h0).1; unfold Apart at this; omega
    · have := apF hin hap hsok.2.1; unfold Apart at this; omega
  have hF2a : MemFrame M3 M4 (R.rt ++ (cw ++ [(p2, p2 + 8 * c2)])) := by rw [← List.append_assoc]; exact hF2
  have hLF2a : LiveFrame M3 M4 L2 (cw ++ [(p2, p2 + 8 * c2)]) :=
    Expmc.liveFrame_widen hLF2 fun a k ho => by rw [outside_append] at ho; exact ho.2
  have rdh : ∀ o, o + 8 ≤ 24 → M4.readLE (st + o) 8 = M3.readLE (st + o) 8 := fun o ho =>
    held_rd (hok2.2.1.sub (by omega) (by omega)) hF2a hLF2a fun r hr => by
      rcases List.mem_append.1 hr with h | h
      · have := MemFrame.outside_mem hstcw h; omega
      · simp only [List.mem_singleton] at h; subst h; simp only; omega
  have ew : stW M4 st = stW M3 st := by have := rdh 0 (by omega); simpa using this
  have el : stLen M4 st = stLen M3 st := rdh 8 (by omega)
  have ec : stCap M4 st = stCap M3 st := rdh 16 (by omega)
  have hok3 : StkOK M4 R L3 st := stkOK_hdr hok2 hF2 ew el ec hx3
  have hsub : ∀ {a k : Nat}, ApartAll a k L2 → ApartAll a k L := fun h r hr => h r (hx2.mem_old hr)
  -- the `lsh` result's location
  have hloc' : (p' = p2 ∧ c' = c2) ∨ (1 ≤ c' ∧ InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L2) := by
    rcases Nat.lt_or_ge c2 nd with hlt | hge
    · have := hcap hlt
      exact Or.inr ⟨by omega, hfr' hlt (by omega)⟩
    · exact Or.inl (hke' hge)
  refine ⟨efs, edf, p', l', c', e0, e1, e2, L3, b3, ⟨?_, ?_, hlc', hc40', ?_, ?_⟩, ⟨hx2.trans hx3, by omega, by rw [hm]; exact hinv⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact hv'
  · rw [hm]; exact hn'
  · rw [hm]; exact hlive'
  · rcases hloc' with ⟨q1, q2⟩ | ⟨h1, hin, hap⟩
    · rw [q1, q2]
      rcases hloc with h | ⟨h1, hin, hap⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, hin, hap⟩
    · exact Or.inr ⟨h1, hin, hsub hap⟩
  · -- StackBackL
    rw [hm]
    refine ⟨⟨hok3, by rw [el, hl2], ?_⟩, ?_⟩
    · rw [ew, ec]; exact hkf2.imp id fun h => h
    · exact ArrIn.trans hai2 (fun hn => absurd ⟨ew, ec⟩ hn) hx3
  · -- MemFrame
    rw [hm]
    refine hF1.trans hF2 fun a k ho => ⟨ho, ?_⟩
    simp only [outside_append] at ho ⊢
    refine ⟨⟨ho.1.1.1, hcw _ _ ho.1.1.2⟩, ?_⟩
    rcases hloc with ⟨q1, q2⟩ | ⟨h1, hin, hap⟩
    · rw [q1, q2]; exact ho.1.2
    · have := hin.apart ho.1.1.1
      simp only [outside_cons, outside_nil, and_true]; unfold Apart at this; omega
  · -- LiveFrame
    rw [hm]
    refine ⟨fun a k hin ho => (hLF2.readLE a k (hx2.inRanges_old hin) ?_).trans (hLF1.readLE a k hin ho)⟩
    rcases hloc with ⟨q1, q2⟩ | ⟨h1, hin', hap⟩
    · rw [q1, q2]; simp only [outside_append] at ho; exact ho.1
    · have := hap.apart_of_inRanges hin
      simp only [outside_cons, outside_nil, and_true]; omega
  · -- ResSep
    rw [hm]
    intro hc0 hne
    rw [ew, ec] at hne ⊢
    rcases hloc' with ⟨q1, q2⟩ | ⟨h1, hin, hap⟩
    · rw [q1, q2]; rw [q2] at hc0; exact hrs hc0 hne
    · rcases Nat.eq_zero_or_pos (stCap M3 st) with h0 | h0
      · rw [h0]; unfold Apart; omega
      · exact apart_arr_of_fresh hap (hok2.2.2.2.2.1 h0).2.1 hin

end

end FvModexp.Amd64.P2D
