import FvModexp.Proofs.Amd64.NatQ.DivMOneA
import FvModexp.Proofs.Amd64.NatQ.DivZOne

set_option autoImplicit false

/-!
# `nat.div` (amd64), `z = nil`, `z2 = u` (`(*Int).Mod`'s call), `len v = 1`: `divW`'s precondition (top s39)

Twin of Arm64/NatQ/DivMOneA.lean's `w_preM`: `DivW.Pre0` at `divW`'s entry for `z = nil` and a possibly empty dividend
with any pointer (`RdIn0`), from `PFM` and the prologue relation `AtV`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
/-- `divW`'s precondition at its entry (`z = nil`, `z2 = u`, any `len u ≤ 2^9`) -/
theorem w_preM {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vc : Nat} {s : State}
    (hp : PFM R b dc L u ul uc v 1 vc s) (X : State) (hX : AtV 0 0 0 u uc u ul uc v s X) :
    DivW.Pre0 R b L 0#64 0#64 (BitVec.ofNat 64 u) (BitVec.ofNat 64 ul) (BitVec.ofNat 64 (s.mem.readLE v 8)) X := by
  have hce0 := hp.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, hro, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hF := hX.mf
  have hspn := sp240 hX.sp (by omega)
  have hFw : MemFrame s.mem X.mem (win s 41512 112) := hF.mono fun a n h => by
    simp only [win, proW, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hce : CallEnv R L X 4232 64 :=
    CallEnv.callee hce0 hspn hX.r14 hX.fs (by decide) (by decide) (by decide) hFw hX.reg
  have hv0 : s.mem.readLE v 8 ≠ 0 := by
    rcases hp.vn with h | h
    · omega
    · simpa using h
  have hsv := hp.srv
  have hul9 := hp.ul9
  have hcost := hp.cost
  have hui := hp.ui
  have tul : (BitVec.ofNat 64 ul).toNat = ul := tN64 (by omega)
  have ty : (BitVec.ofNat 64 (s.mem.readLE v 8)).toNat = s.mem.readLE v 8 :=
    tN64 (Janus.Arm64.Memory.readLE_lt _ _ _)
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 41512 ∨ (s.regs 4).toNat + 112 ≤ a) →
      X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (by simp only [proW, outside_cons, outside_nil, and_true]; omega)
  unfold DivW.Pre0
  rw [tul, ty]
  refine ⟨hce, hro.out' 1 (by decide) (by decide), hv0, by omega, by simp, by simp, fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun hu => ?_, ?_, ?_, ?_, fun d sr k hk => hsv.2.1 d sr k (by omega)⟩
  · obtain ⟨-, huacc, hu48, huh, huw⟩ := hui.2 hu
    have tu : (BitVec.ofNat 64 u).toNat = u := tN64 (by omega)
    rw [tu]
    simp only [win, outside_cons, outside_nil, and_true] at huw
    refine ⟨by rw [hF.accessible]; exact huacc, hu48, huh, ?_⟩
    simp only [win, outside_cons, outside_nil, and_true]; rw [hspn]; omega
  · by_cases h0 : ul = 0
    · exact Or.inl h0
    · obtain ⟨-, -, hu48, -, huw⟩ := hui.2 (by omega)
      have tu : (BitVec.ofNat 64 u).toNat = u := tN64 (by omega)
      simp only [win, outside_cons, outside_nil, and_true] at huw
      try rw [tu]
      rcases hp.un with h | h
      · exact absurd h h0
      · exact Or.inr (by rw [hrd _ _ (by omega)]; exact h)
  · rw [hX.r14]
    refine RtInv.inv_frame' hF (fun r hr => ?_) hp.inv
    simp only [proW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))
  · intro hc
    refine ⟨hsv.1 _ _ _ (by unfold makeCap; split <;> omega), ?_⟩
    simp only [costMQ, costQ, DivLarge.costQ] at hcost; omega

end FvModexp.Amd64.Q.NatDiv
