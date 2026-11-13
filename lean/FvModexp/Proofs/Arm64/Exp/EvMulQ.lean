import FvModexp.Proofs.Arm64.Exp.EvMulD
import FvModexp.Proofs.Arm64.ExpQ.Bridge
import FvModexp.Proofs.Arm64.ExpQ.SlowMuGQ

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): its two `nat.mul` calls on divmc's Q-form `nat.mul`, bridged (agent infra s46, TIGHT COSTS)

`mulG_of_Q`: the empty-tolerant Q-form premise `Q.ExpSlow.MulHypGQ … C` (expmc's `Q.ExpSlow.mulGQ` from divmc's
`Q.NatMul.ens`) gives `expNNEven`'s level-cost premise `ExpEven.MulHypG … (mulBrE C)` with the bridged cost
`mulBrE C ℓ a c = C a c + stkRes (ℓ + 4·(a + c) + 64)` (`Q.brC`; reserve level `H := stLen + 4·(xl + yl) + 64` per call,
expmc's `Q.ens_param`). `expNNEven` calls `nat.mul` twice (O(1) per exponentiation), so the per-call reserve is cheap;
this replaces the old level cost `mulC ℓ ml ml` (whose `stackNatCost` chains are ~2.6e3 W at `ml = 128`, NOTES-conventions
"[divmc s41] BLOCKER").
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the bridged cost of one empty-tolerant `nat.mul` (level `ℓ`, operand lengths `a`, `c`) -/
@[reducible] def mulBrE (C : Nat → Nat → Nat) : Nat → Nat → Nat → Nat :=
  Q.brC C (fun a c => 4 * (a + c) + 64)

theorem mulBrE_mono {C : Nat → Nat → Nat} (hC : ∀ a a' c c', a ≤ a' → c ≤ c' → C a c ≤ C a' c')
    {ℓ ℓ' a a' c c' : Nat} (h1 : ℓ ≤ ℓ') (h2 : a ≤ a') (h3 : c ≤ c') : mulBrE C ℓ a c ≤ mulBrE C ℓ' a' c' := by
  have := hC a a' c c' h2 h3
  simp only [mulBrE, Q.brC, stkRes_eq]
  omega

/-- **the bridge**: Q-form empty-tolerant `nat.mul` → `expNNEven`'s level-cost premise -/
theorem mulG_of_Q {impl : List Segment} {R : RtInv} {ns : List String} {stk above : Nat} {C : Nat → Nat → Nat}
    (h : Q.ExpSlow.MulHypGQ impl R ns stk above C) : MulHypG impl R ns stk above (mulBrE C) := by
  intro b L z zl zc st x xl xc y yl yc
  refine Q.ens_param (fun H => h H b L z zl zc st x xl xc y yl yc)
    (fun s => stLen s.mem st.toNat + (4 * (xl.toNat + yl.toNat) + 64)) (fun s hp => ?_) (fun s s' hq => ?_)
  · obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hc, hinv⟩, hx, hy, hX⟩ := hp
    have hc' : C xl.toNat yl.toNat + stkRes (stLen s.mem st.toNat + (4 * (xl.toNat + yl.toNat) + 64)) ≤ b := hc
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, Q.cost_br hc', hinv⟩, hx, hy, hX,
      by omega⟩
  · obtain ⟨⟨p', l', c', e0, e1, e2, L', b', hof, ⟨hLE, hb, hinv⟩, rest⟩, hreu⟩ := hq
    have hb' : b - (C xl.toNat yl.toNat + stkRes (stLen s.mem st.toNat + (4 * (xl.toNat + yl.toNat) + 64))) ≤ b' :=
      Q.bud_br (stkR_le _ _ _) hb
    exact ⟨⟨p', l', c', e0, e1, e2, L', b', hof, ⟨hLE, hb', hinv⟩, rest⟩, hreu⟩

end FvModexp.Arm64.ExpEven
