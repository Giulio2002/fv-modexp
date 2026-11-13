import FvModexp.Proofs.Amd64.Nat.DivG
import FvModexp.Proofs.Amd64.Nat.DivLessRel

set_option autoImplicit false

/-!
# `nat.div` (amd64), `u < v`: the postcondition from `AtS` and the copy's facts (pure)

Port of `Arm64/Nat/DivLessF.lean` (`lessFin`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges held_apart_fresh)

namespace FvModexp.Amd64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem lessFin {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (hpre : PreG R b dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat}
    {S : State} (hS : AtS R b L zp zc z2 z2c u ul s p c L' b' S) (hU : natVal s.mem u ul < natVal s.mem v vl)
    (s' : State) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 3 = BitVec.ofNat 64 0) (h2 : s'.regs 1 = BitVec.ofNat 64 zc)
    (h3 : s'.regs 7 = BitVec.ofNat 64 p) (h4 : s'.regs 6 = BitVec.ofNat 64 ul) (h5 : s'.regs 8 = BitVec.ofNat 64 c)
    (hM : MemFrame S.mem s'.mem (R.rt ++ win s 41512 112 ++ ar p ul)) (hLF2 : LiveFrame S.mem s'.mem L' (ar p ul))
    (hinv : R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem))
    (hval : s'.mem.readLE p (8 * ul) = S.mem.readLE u (8 * ul))
    (htop : 0 < ul → s'.mem.readLE (p + 8 * (ul - 1)) 8 = S.mem.readLE (u + 8 * (ul - 1)) 8) :
    PostLG R b dc L zp zc st z2 z2c u ul v vl s s' := by
  have hp := hpre.f
  have hout := hp.ce.2.2.2.2.1
  -- `u`'s words at `S.mem` are the entry's (`u` non-empty)
  have hku : 0 < ul → ∀ a n, u ≤ a → a + n ≤ u + 8 * ul → 0 < n → S.mem.readLE a n = s.mem.readLE a n := by
    intro hu0 a n h1 h2 hn
    obtain ⟨hu40, huacc, hu48, huh, huw⟩ := hp.ui.2 hu0
    simp only [win, outside_cons, outside_nil, and_true] at huw
    rcases huh.sub h1 h2 with hin | ho
    · exact hS.lf.readLE a n hin trivial
    · exact hS.mf.readLE a n (by
        simp only [outside_append, win, outside_cons, outside_nil, and_true]; exact ⟨ho, by omega⟩)
  have hval' : natVal s'.mem p ul = natVal s.mem u ul := by
    by_cases h0 : ul = 0
    · simp [natVal, h0]
    · show s'.mem.readLE p (8 * ul) = s.mem.readLE u (8 * ul)
      rw [hval, hku (by omega) _ _ (Nat.le_refl _) (Nat.le_refl _) (by omega)]
  have harr := hS.arr
  -- `p`'s array (first `ul` words) is `z2`'s (reused) or fresh
  have hpo : ∀ a n, Outside a n (R.rt ++ win s 41512 112 ++ ar zp zc ++ ar z2 z2c) → Outside a n (ar p ul) := by
    intro a n h
    simp only [outside_append] at h
    refine outside_ar fun hc => ?_
    rcases harr with ⟨rfl, rfl, hz⟩ | ⟨-, hc1, -, -, -, hin, -, -, -⟩
    · have := ar_out h.2 (by omega); omega
    · have := outside_of_inRanges h.1.1.1 hin; omega
  refine post_keptG hpre s' hfs hdf h0 h1 h2 h3 h4 h5 ?q ?r hS.ext
    (by have := hS.bud; have := hp.cost; simp only [cost] at *; omega)
    hinv (hS.mf.trans hM fun a n h => ⟨?mf1, ?mf⟩)
    ⟨fun a n hin ho => ?lf⟩ (fun h _ _ _ => absurd ⟨rfl, rfl⟩ h)
  case q =>
    refine ⟨?_, Or.inl rfl, Nat.zero_le _, hp.zo.1, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · simp only [natVal, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero]; exact (Nat.div_eq_of_lt hU).symm
    · intro hc
      obtain ⟨a1, a2, a3, a4⟩ := hp.zo.2.1 hc
      exact ⟨a1, hS.ext.held a2, by rw [hM.accessible, hS.mf.accessible]; exact a3, a4⟩
  case r =>
    refine ⟨by rw [hval', Nat.mod_eq_of_lt hU], ?_, ?_, ?_, ?_, ?_⟩
    · by_cases h0 : ul = 0
      · exact Or.inl h0
      · rcases hp.un with h | h
        · exact absurd h h0
        · refine Or.inr ?_
          rw [htop (by omega), hku (by omega) _ _ (by omega) (by omega) (by omega)]; exact h
    · rcases harr with ⟨rfl, rfl, hz⟩ | ⟨-, hc1, -⟩ <;> omega
    · rcases harr with ⟨rfl, rfl, hz⟩ | ⟨-, hc1, hc2, -⟩
      · exact hp.z2o.1
      · have := hp.ul9; omega
    · intro hc
      rcases harr with ⟨rfl, rfl, hz⟩ | ⟨-, hc1, hc2, h8, h48, -, -, hinL, hacc⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hp.z2o.2.1 hc
        exact ⟨a1, hS.ext.held a2, by rw [hM.accessible, hS.mf.accessible]; exact a3, a4⟩
      · exact ⟨h8, Or.inl hinL, by rw [hM.accessible]; exact hacc, h48⟩
    · rcases harr with ⟨rfl, rfl, hz⟩ | ⟨hz, hc1, -, -, -, hin, hap, -, -⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨by omega, hin, hap⟩
  case mf1 => simp only [outside_append] at h ⊢; exact h.1.1
  case mf =>
    rw [outside_append]
    exact ⟨by simp only [outside_append] at h ⊢; exact h.1.1, hpo a n h⟩
  case lf =>
    simp only [outside_append] at ho
    rw [hLF2.readLE a n (hS.ext.inRanges_old hin) ?_]
    · exact hS.lf.readLE a n hin trivial
    · refine outside_ar fun hc => ?_
      rcases harr with ⟨rfl, rfl, hz⟩ | ⟨-, hc1, -, -, -, -, hap, -, -⟩
      · have := ar_out ho.2 (by omega); omega
      · obtain ⟨r, hr, i1, i2⟩ := hin
        have := hap r hr; unfold Apart at this; omega

end FvModexp.Amd64.NatDiv
