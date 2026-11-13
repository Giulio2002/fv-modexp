import FvModexp.Proofs.Arm64.Exp.P2DFull
import FvModexp.Proofs.Arm64.Exp.ModInvDefs
import FvModexp.Proofs.Arm64.Exp.SubMod2NG
import FvModexp.Proofs.Common.MulCostB2

set_option autoImplicit false

/-!
# Closed `(*Int).exp` budget, part 1: `nat.expNNPowerOfTwo` (`P2D.cP`), `modularInverse` and `subMod2N` (divmc s33)

Crude uniform bounds for `Run.Closed.BudOK` (NOTES-conventions "[divmc s33] FINDING"): stack length `ℓ0 ≤ 1024`,
modulus bits `lm ≤ 8192` (`W lm ≤ 128` words). The window costs are generic in the `sqr`/`mul` budgets `sqC`/`mlC`
(bounded by `S`/`M` on `ℓ ≤ 2^14`, `≤ 129` words) and come out linear in `S`, `M`; `cP_le` instantiates them with
`sqrC_le`/`mulC_le2`. The loop multiplicities (`32·((lm-2)/64+1) ≤ 4096`, `16·… ≤ 2048`, `pl/2 - 1 ≤ 7`) are
`Nat.mul_le_mul` steps.
-/

open Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpBud

/-- `max_{j ≤ n} f j ≤ C` from a pointwise bound (`P2D.supTo`) -/
theorem supTo_le {f : Nat → Nat} {C : Nat} : ∀ n, (∀ j, j ≤ n → f j ≤ C) → P2D.supTo f n ≤ C := by
  intro n
  induction n with
  | zero => intro h; exact h 0 (Nat.le_refl _)
  | succ n ih =>
    intro h
    exact Nat.max_le.2 ⟨ih (fun j hj => h j (by omega)), h (n + 1) (Nat.le_refl _)⟩

theorem tC_le {lm : Nat} (hlm : lm ≤ 8192) : P2Pre.tC lm ≤ 2200 := by
  have := makeCost_le_makeB (P2Pre.W lm + 4)
  have hW : P2Pre.W lm ≤ 128 := by unfold P2Pre.W; omega
  unfold makeB allocCost at this; unfold P2Pre.tC; omega

section
variable (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (S M : Nat)
  (hS : ∀ ℓ n, ℓ ≤ 16384 → n ≤ 129 → sqC ℓ n ≤ S)
  (hM : ∀ ℓ x y, ℓ ≤ 16384 → x ≤ 129 → y ≤ 129 → mlC ℓ x y ≤ M)
include hS hM

/-- the table loop of `nat.expNNPowerOfTwo`'s windows (`P2Pre.cost`, `pl ≤ 16` powers) -/
theorem p2pre_le {ℓ pl lm : Nat} (hl : ℓ ≤ 8192) (hpl : pl ≤ 16) (hlm : lm ≤ 8192) :
    P2Pre.cost sqC mlC ℓ pl lm ≤ 32 * ℓ + 72016 + 7 * (S + M + 4400) := by
  have hW : P2Pre.W lm ≤ 128 := by unfold P2Pre.W; omega
  have hl1 : P2Pre.lvl1 ℓ pl lm ≤ 16384 := by
    unfold P2Pre.lvl1 P2Pre.NB; simp only [StackNat.rnd]
    have := Nat.mul_le_mul (show pl + 1 ≤ 17 by omega) hW; omega
  have h1 := hS (P2Pre.lvl1 ℓ pl lm) (P2Pre.W lm) hl1 (by omega)
  have h2 := hM (P2Pre.lvl1 ℓ pl lm) (P2Pre.W lm) (P2Pre.W lm) hl1 (by omega) (by omega)
  have ht := tC_le hlm
  have hrc : P2Pre.rc sqC mlC ℓ pl lm ≤ S + M + 4400 := by unfold P2Pre.rc; omega
  have hQ := Nat.mul_le_mul (show pl / 2 - 1 ≤ 7 by omega) hrc
  have hc0 : P2Pre.c0 ℓ pl lm ≤ 32 * ℓ + 72016 := by
    have := Nat.mul_le_mul (show pl + 1 ≤ 17 by omega) hW
    unfold P2Pre.c0 P2Pre.NB stackNatCost allocCost; omega
  unfold P2Pre.cost; omega

/-- window 2 of `nat.expNNPowerOfTwo` (`P2W2.cost`) -/
theorem p2w2_le {ℓ0 lm : Nat} (hl : ℓ0 ≤ 1024) (hlm : lm ≤ 8192) :
    P2W2.cost sqC mlC ℓ0 lm ≤ 400000 + 7 * (S + M + 4400) + 4096 * (2 * S + M + 6600) := by
  have hW : P2W2.W lm ≤ 128 := by unfold P2W2.W; omega
  have hW' : P2Pre.W lm = P2W2.W lm := rfl
  have hZ : P2W2.ℓZ ℓ0 lm ≤ 2304 := by unfold P2W2.ℓZ P2W2.ℓR; simp only [StackNat.rnd]; omega
  have hL : P2W2.ℓL ℓ0 lm ≤ 16384 := by
    unfold P2W2.ℓL P2Pre.NB; simp only [StackNat.rnd]; rw [hW']; omega
  have hP := p2pre_le sqC mlC S M hS hM (ℓ := P2W2.ℓZ ℓ0 lm) (pl := 4) (by omega) (by omega) hlm
  have h1 := hS (P2W2.ℓL ℓ0 lm) (P2W2.W lm) hL (by omega)
  have h2 := hM (P2W2.ℓL ℓ0 lm) (P2W2.W lm) (P2W2.W lm) hL (by omega) (by omega)
  have ht := tC_le hlm
  have hbc : P2W2.bc sqC mlC (P2W2.ℓL ℓ0 lm) lm ≤ 2 * S + M + 6600 := by unfold P2W2.bc; omega
  have hQ := Nat.mul_le_mul (show 32 * ((lm - 2) / 64 + 1) ≤ 4096 by omega) hbc
  have hc0 : P2W2.cost0 sqC mlC ℓ0 lm ≤ 300000 + 7 * (S + M + 4400) := by
    unfold P2W2.cost0 P2W2.ℓR stackNatCost allocCost; omega
  unfold P2W2.cost allocCost; omega

/-- window 4 of `nat.expNNPowerOfTwo` (`P2W4.cost`) -/
theorem p2w4_le {ℓ0 lm : Nat} (hl : ℓ0 ≤ 1024) (hlm : lm ≤ 8192) :
    P2W4.cost sqC mlC ℓ0 lm ≤ 600000 + 7 * (S + M + 4400) + 2048 * (4 * S + M + 11000) := by
  have hW : P2W4.W lm ≤ 128 := by unfold P2W4.W; omega
  have hW' : P2Pre.W lm = P2W4.W lm := rfl
  have hZ : P2W4.ℓZ ℓ0 lm ≤ 3840 := by unfold P2W4.ℓZ P2W4.ℓR; simp only [StackNat.rnd]; omega
  have hL : P2W4.ℓL ℓ0 lm ≤ 16384 := by
    unfold P2W4.ℓL P2Pre.NB; simp only [StackNat.rnd]; rw [hW']; omega
  have hP := p2pre_le sqC mlC S M hS hM (ℓ := P2W4.ℓZ ℓ0 lm) (pl := 16) (by omega) (by omega) hlm
  have h1 := hS (P2W4.ℓL ℓ0 lm) (P2W4.W lm) hL (by omega)
  have h2 := hM (P2W4.ℓL ℓ0 lm) (P2W4.W lm) (P2W4.W lm) hL (by omega) (by omega)
  have ht := tC_le hlm
  have hbc : P2W4.bc sqC mlC (P2W4.ℓL ℓ0 lm) lm ≤ 4 * S + M + 11000 := by unfold P2W4.bc; omega
  have hQ := Nat.mul_le_mul (show 16 * ((lm - 2) / 64 + 1) ≤ 2048 by omega) hbc
  have hc0 : P2W4.cost0 sqC mlC ℓ0 lm ≤ 500000 + 7 * (S + M + 4400) := by
    unfold P2W4.cost0 P2W4.ℓR stackNatCost allocCost; omega
  unfold P2W4.cost allocCost; omega

/-- `nat.expNNPowerOfTwo`'s budget `P2D.cP` (any positive base) -/
theorem cP_gen {ℓ xl yl lm : Nat} (hl : ℓ ≤ 1024) (hx : xl ≤ 128) (hlm : lm ≤ 8192) :
    P2D.cP sqC mlC ℓ xl yl lm ≤ 1020000 + 14 * (S + M + 4400) + 4096 * (2 * S + M + 6600) +
      2048 * (4 * S + M + 11000) := by
  unfold P2D.cP P2D.costP
  have hs := supTo_le (f := P2D.costO (P2W2.cost sqC mlC) (P2W4.cost sqC mlC) ℓ)
    (C := 1010000 + 14 * (S + M + 4400) + 4096 * (2 * S + M + 6600) + 2048 * (4 * S + M + 11000)) lm
    (fun j hj => by
      have := p2w2_le sqC mlC S M hS hM (ℓ0 := ℓ) (lm := j) hl (by omega)
      have := p2w4_le sqC mlC S M hS hM (ℓ0 := ℓ) (lm := j) hl (by omega)
      unfold P2D.costO allocCost; omega)
  have h1 := makeCost_le_makeB (xl + 2)
  have h2 := makeCost_le_makeB (lm / 64 + 2)
  unfold makeB allocCost at h1 h2
  omega

end

/-- **`P2D.cP sqrC mulC`** at `ℓ ≤ 1024`, `lm ≤ 8192` -/
theorem cP_le {ℓ xl yl lm : Nat} (hl : ℓ ≤ 1024) (hx : xl ≤ 128) (hlm : lm ≤ 8192) :
    P2D.cP sqrC mulC ℓ xl yl lm ≤ 135000000000000 := by
  have := cP_gen sqrC mulC 2700000 21620929512 (fun _ _ h1 h2 => sqrC_le h1 h2)
    (fun _ _ _ h1 h2 h3 => mulC_le2 h1 h2 h3) (yl := yl) hl hx hlm
  omega

/-- `modularInverse`'s budget (`ModInv.cost`) at stack length `L ≤ 2^14`, `n ≤ 8192` bits -/
theorem modInv_le {L n : Nat} (hL : L ≤ 16384) (hn : n ≤ 8192) :
    ModInv.cost (sqrC L) (mulC L) n ≤ 17000000000000 := by
  have hW : ModInv.NW n ≤ 128 := by unfold ModInv.NW; omega
  have h1 := sqrC_le (ℓ := L) (n := ModInv.NW n + 1) hL (by omega)
  have h2 := mulC_le3 (ℓ := L) (x := 2 * ModInv.NW n + 2) (y := ModInv.NW n) hL (by omega) (by omega)
  have m1 := makeCost_le_makeB (2 * ModInv.NW n + 2)
  have m2 := makeCost_le_makeB (ModInv.NW n + 2)
  have m3 := makeCost_le_makeB (ModInv.NW n + 1)
  have m4 := makeCost_le_makeB (2 * ModInv.NW n)
  unfold makeB allocCost at m1 m2 m3 m4
  have hr : ModInv.roundCost (sqrC L) (mulC L) n ≤ 130002800000 := by
    unfold ModInv.roundCost SubMod2N.cost SubMod2N.wCost SubMod2N.W allocCost
    unfold ModInv.NW at *; omega
  have hQ := Nat.mul_le_mul (show ModInv.NW n + 1 ≤ 129 by omega) hr
  unfold ModInv.cost; omega

/-- `subMod2N`'s general budget (`SubMod2N.costG`), `n ≤ 8192` bits -/
theorem costG_le {n : Nat} (hn : n ≤ 8192) : SubMod2N.costG n ≤ 600000 := by
  have hW : SubMod2N.W n ≤ 128 := by unfold SubMod2N.W; omega
  have hg : SubMod2N.gA n ≤ 4152 := by unfold SubMod2N.gA allocCost; omega
  have hQ := Nat.mul_le_mul hW hg
  unfold SubMod2N.costG SubMod2N.cost SubMod2N.wCost allocCost; omega

end FvModexp.Arm64.ExpBud
