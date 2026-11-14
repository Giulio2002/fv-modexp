import FvModexp.Proofs.Amd64.Exp.EvMulP

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): small shared lemmas of the two `nat.mul` segments `segM1` / `segM2` (asm s63)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

open FvModexp.Amd64.EvenHyp

/-- adapted from divmc's arm64 `EvenHyp.resSep_of_fa` (Arm64/Nat/SqrMulXR.lean) -/
theorem resSep_faE {R : RtInv} {L L' : List (Nat × Nat)} {st zp zc p c : Nat} {m0 m : Memory}
    (hz : 0 < zc → Held R L zp (8 * zc)) (hsb : StackBackL R L L' st m0 m)
    (hfa : ¬ (p = zp ∧ c = zc) → 0 < c → 0 < stCap m st → Apart p (8 * c) (stW m st) (8 * stCap m st)) :
    ResSep m0 m st p c := by
  intro hc hn
  by_cases hk : p = zp ∧ c = zc
  · obtain ⟨rfl, rfl⟩ := hk
    exact ResSep.of_held hsb.1.2.2 (hz hc) hc hn
  · exact hfa hk hc (hsb.2 hn).2

/-- a value below `2^n` (`n < 64 ml`) has at most `ml` limbs -/
theorem len_mlE {M : Memory} {p l v n : Nat} (hN : NatNorm M p l) (hv : natVal M p l = v) (hlt : v < 2 ^ n)
    {ml : Nat} (hn : n < 64 * ml) : l ≤ ml :=
  nlen_bd' hN (by rw [hv]; exact Nat.lt_trans hlt (Nat.pow_lt_pow_right (by decide) hn))

theorem m16 {ℓ a c ml : Nat} (ha : a ≤ ml) (hc : c ≤ ml) (h : ℓ + 8 * ml + 64 ≤ 2 ^ 16) :
    ℓ + 4 * (a + c) + 64 ≤ 2 ^ 16 := by omega

theorem m16H {ℓ a c ml : Nat} (ha : a ≤ ml) (hc : c ≤ ml) : ℓ + 4 * (a + c) + 64 ≤ ℓ + 8 * ml + 64 := by omega

theorem bud_qE {rk b1 c sr rk' x y b2 : Nat} (h1 : rk ≤ b1) (h2 : c + sr + rk' ≤ rk) (h3 : x ≤ sr)
    (h4 : b1 - (c + x) + y ≤ b2) : rk' ≤ b2 := by omega

theorem bud_q1 {rk b1 c sr x rk' : Nat} (h1 : rk ≤ b1) (h2 : c + sr + rk' ≤ rk) (h3 : x ≤ sr) : c + x ≤ b1 := by
  omega

/-- the keep range through the push + three stack-argument words and a callee with `above = 88` -/
theorem kk_push4 {sp : Nat} {M0 M M' : Memory} (hsp : 8 ≤ sp) (hF : MemFrame M0 M [(sp - 8, sp + 0x18)])
    (hkc : ∀ a k, sp - 8 + 88 ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M.readLE a k) :
    ∀ a k, sp + 0x77 ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M0.readLE a k := fun a k h1 h2 => by
  rw [hkc a k (by omega) h2, hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]

/-- a slot read through `kk_push4` -/
theorem m_slot {sp : Nat} {M0 M' : Memory}
    (hk : ∀ a k, sp + 0x77 ≤ a → a + k ≤ sp + 0x1b8 → M'.readLE a k = M0.readLE a k) (o : Nat) (h1 : 0x77 ≤ o)
    (h2 : o + 8 ≤ 0x1b8) {v : Nat} (h : M0.readLE (sp + o) 8 = v) : M'.readLE (sp + o) 8 = v := by
  rw [hk _ _ (by omega) (by omega)]; exact h

theorem own4 (sp K : Nat) (hsp : 8 ≤ sp) : ∀ r ∈ [(sp - 8, sp + 0x18)], OwnR sp K r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; simp only [OwnR]; omega

end FvModexp.Amd64.ExpEven
