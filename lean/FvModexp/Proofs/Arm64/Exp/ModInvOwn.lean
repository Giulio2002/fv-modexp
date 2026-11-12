import FvModexp.Proofs.Arm64.Exp.ModInvKeep
import FvModexp.Proofs.Arm64.Exp.ModInvKeep2
import FvModexp.Proofs.Arm64.Exp.ModInvPre

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): a callee's result is owned; the round facts after a call (agent infra)

`own_new`: the result array of a callee (the old owned array, or a fresh runtime object apart from the old live set and
from a re-allocated stack array) is owned. `after_zz` / `after_z`: the round facts `Mid` after a callee that writes
`zz` / `z` (with or without the stack object), `z`'s / `zz`'s words and the spill slots unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

section
variable {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the result array of a callee is owned -/
theorem own_new (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M M' : Memory} {L1 L2 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) (hsb : StackBack R L1 L2 st M M')
    {t tc p' c' : Nat} (ht : Own R kc L L1 s zp zc st xp xl M t tc) (hlive : NatLive M' R L2 p' c')
    (hc40 : c' < 2 ^ 40) (hp : p' < 2 ^ 64)
    (hof : (p' = t ∧ c' = tc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L1))
    (hstk : ¬ (p' = t ∧ c' = tc) → 0 < c' → 0 < stCap M' st →
      ¬ (stW M' st = stW M st ∧ stCap M' st = stCap M st) → Apart p' (8 * c') (stW M' st) (8 * stCap M' st)) :
    Own R kc L L2 s zp zc st xp xl M' p' c' := by
  rcases hof with ⟨rfl, rfl⟩ | ⟨hIn, hAp⟩
  · exact own_back ht hlive hsb
  by_cases hold : p' = t ∧ c' = tc
  · obtain ⟨rfl, rfl⟩ := hold; exact own_back ht hlive hsb
  have hwa := wa_new hsb hrt.2.2.2.2.2.1 ht.2.2.2.2.2.2.2.2 (fun hc => (ht.2.2.1 hc).2.1) (Or.inr ⟨hIn, hAp⟩) hstk
  obtain ⟨⟨-, -, -, hout, -, hgrt, -, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hxh, -⟩, -⟩ := hpre
  obtain ⟨-, -, -, LE0, -, ⟨-, hsth, -, -, hstl, hlc, -⟩, -, -⟩ := hrt
  have hApL : ApartAll p' (8 * c') L := apartAll_old LE0 hAp
  simp only [K, A] at hout
  refine ⟨hc40, hp, hlive, Or.inr ⟨hIn, hApL⟩, ?_, fresh_out hIn hgrt, fresh_apart hIn hApL hxh, fun hc => ?_, hwa⟩
  · have := fresh_out hIn hout
    unfold Apart at this
    simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
  · refine ⟨fresh_apart hIn hAp hsth, fun hlt => ?_⟩
    obtain ⟨hok, hlen, hor⟩ := hsb
    have hcap : 0 < stCap M' st := by omega
    have hfull : Apart p' (8 * c') (stW M' st) (8 * stCap M' st) := by
      by_cases hsame : stW M' st = stW M st ∧ stCap M' st = stCap M st
      · obtain ⟨e0, e2⟩ := hsame
        rw [e2] at hcap; rw [e0, e2]
        exact fresh_apart hIn hAp (hstl hcap).2.1
      · exact hstk hold (by omega) hcap hsame
    unfold Apart at hfull ⊢
    have : 8 * stLen M' st + 8 * (stCap M' st - stLen M' st) = 8 * stCap M' st := by omega
    omega

/-- an owned array apart from a range the entry holds, when the caller's array is -/
theorem own_apart {M : Memory} {L1 : List (Nat × Nat)} {p c a k : Nat} (h : Own R kc L L1 s zp zc st xp xl M p c)
    (hh : Held R L a k) (hz : Apart zp (8 * zc) a k) : Apart p (8 * c) a k := by
  rcases h.2.2.2.1 with ⟨rfl, rfl⟩ | ⟨hIn, hAp⟩
  · exact hz
  · exact fresh_apart hIn hAp hh

end

end FvModexp.Arm64.ModInv
