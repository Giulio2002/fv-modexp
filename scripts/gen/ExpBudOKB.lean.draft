import FvModexp.Proofs.Arm64.Top.ExpBudP2
import FvModexp.Proofs.Arm64.Top.ExpBudW
import FvModexp.Proofs.Arm64.Nat.DivCostB
import FvModexp.Proofs.Arm64.Nat.RemDefs
import FvModexp.Proofs.Arm64.Exp.NDefs
import FvModexp.Proofs.Arm64.Exp.EvE1
import FvModexp.Proofs.Arm64.Exp.EvCost
import FvModexp.Proofs.Arm64.Exp.NFunNE
import FvModexp.Proofs.Arm64.Exp.SlowStmt
import FvModexp.Proofs.Common.NCostU

set_option autoImplicit false

/-!
# Closed `(*Int).exp` budget, part 3: the composition (divmc s33)

The closed cost of `(*Int).exp` (the two inequalities of `Run.Closed.BudOK`, Arm64/Top/RunOkRowC.lean) is at most
`7·10^14 + 4.2·10^13 · yl` for `xl, yl ≤ 128`, `0 < n ≤ 128`, `lm < 64 n` (`ExpBud.main`). Ingredients (all crude
uniform bounds): `nat.div` `≤ D = 8.25·10^8` (`NatDiv.costF_le`), `nat.rem` `≤ D + 3·10^5`, `expNNSlow`
`≤ 6000 + 8.4·10^12 · yl` (its per-bit boxes), `expNNPowerOfTwo` `≤ 1.35·10^14` (`cP_le`), the windows
`≤ 2·10^7 + 60 D` (`oBud_le`/`oCost_le`), hence `NBudE`/`NCost` (and their box maxima `Exp.supU`) `≤ 1.351·10^14 +
8.4·10^12 · yl`, and `expNNEven` (`costE`: two `nat.expNN` budget+cost pairs, `modularInverse`, `subMod2N`, two `mul`s)
`≤ 5.6·10^14 + 3.36·10^13 · yl`.
-/

open Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpBud

/-- `nat.div`'s cost (as `Run.Closed.cF`) -/
abbrev cF : Nat → Nat → Nat → Nat := NatDiv.cost DivRec.drsC
/-- `nat.rem`'s cost (as `Run.Closed.cR`) -/
abbrev cR : Nat → Nat → Nat → Nat := NatRem.cost cF
/-- `nat.expNNSlow`'s cost (as `Run.Closed.cS`) -/
abbrev cS : Nat → Nat → Nat → Nat → Nat := ExpSlow.cost sqrC mulC cF
/-- `nat.expNNPowerOfTwo`'s cost (as `Run.Closed.cP`) -/
abbrev cP : Nat → Nat → Nat → Nat → Nat := P2D.cP sqrC mulC
/-- as `Run.Closed.bUC` -/
abbrev bUC : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpEven.NBudE cF cR cS cP)
/-- as `Run.Closed.cUC` -/
abbrev cUC : Nat → Nat → Nat → Nat → Nat → Nat := Exp.supU (ExpN.NCost cF cR cS cP)
/-- as `Run.Closed.cE` -/
abbrev cE : Nat → Nat → Nat → Nat → Nat := ExpEven.costE cF cR cS cP bUC cUC sqrC mulC mulC

/-- `max_{j ≤ n} f j ≤ C` from a pointwise bound -/
theorem supN_le {f : Nat → Nat} {C : Nat} : ∀ n, (∀ j, j ≤ n → f j ≤ C) → Exp.supN f n ≤ C := by
  intro n
  induction n with
  | zero => intro h; exact h 0 (Nat.le_refl _)
  | succ n ih =>
    intro h
    exact Nat.max_le.2 ⟨ih (fun j hj => h j (by omega)), h (n + 1) (Nat.le_refl _)⟩

/-- the box maximum `Exp.supU f x y a l k ≤ C` from a bound on the box -/
theorem supU_le {f : Nat → Nat → Nat → Nat → Nat → Nat} {C x y a l k : Nat}
    (h : ∀ a0 l0 k0, a0 ≤ a → l0 ≤ l → k0 ≤ k → f x y a0 l0 k0 ≤ C) : Exp.supU f x y a l k ≤ C := by
  unfold Exp.supU
  exact supN_le a (fun a0 ha => supN_le l (fun l0 hl => supN_le k (fun k0 hk => h a0 l0 k0 ha hl hk)))

theorem cF_le {ℓ ul vl : Nat} (hl : ℓ ≤ 8192) (hu : ul ≤ 385) (hv : vl ≤ 129) : cF ℓ ul vl ≤ 825000000 :=
  NatDiv.costF_le hl hu hv

theorem cR_le {ℓ ul vl : Nat} (hl : ℓ ≤ 1024) (hu : ul ≤ 128) (hv : vl ≤ 128) : cR ℓ ul vl ≤ 825300000 := by
  have := cF_le (ℓ := ℓ + StackNat.rnd (NatRem.kq ul vl)) (ul := ul) (vl := vl)
    (by unfold NatRem.kq; simp only [StackNat.rnd]; omega) (by omega) (by omega)
  unfold cR NatRem.cost NatRem.kq stackNatCost allocCost at *
  omega

theorem cS_le {ℓ xl yl ml : Nat} (hl : ℓ ≤ 1024) (hx : xl ≤ 128) (hm : ml ≤ 128) :
    cS ℓ xl yl ml ≤ 6000 + 8400000000000 * yl := by
  have h1 := supN_le (f := sqrC ℓ) (C := 2700000) (max xl ml) (fun j hj => sqrC_le (by omega) (by omega))
  have h2 := supN_le (f := fun n => mulC ℓ n xl) (C := 130000000000) (2 * max xl ml)
    (fun j hj => mulC_le3 (by omega) (by omega) (by omega))
  have h3 := supN_le (f := fun n => cF ℓ n ml) (C := 825000000) (3 * max xl ml)
    (fun j hj => cF_le (by omega) (by omega) (by omega))
  have hT : Exp.supN (sqrC ℓ) (max xl ml) + Exp.supN (fun n => mulC ℓ n xl) (2 * max xl ml) +
      Exp.supN (fun n => cF ℓ n ml) (3 * max xl ml) ≤ 130827700000 := by omega
  have hQ := Nat.mul_le_mul_left (64 * yl) hT
  rw [Nat.mul_comm (64 * yl) 130827700000] at hQ
  have hm := makeCost_le_makeB xl
  unfold makeB allocCost at hm
  unfold cS ExpSlow.cost
  omega

theorem cP_le' {ℓ xl yl lm : Nat} (hl : ℓ ≤ 1024) (hx : xl ≤ 128) (hlm : lm ≤ 8192) :
    cP ℓ xl yl lm ≤ 135000000000000 := cP_le hl hx hlm

theorem oBud_le' {n xl yl l : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (hl : l ≤ 1024) :
    ExpOdd.OBud cF n xl yl l ≤ 49520000000 := by
  have := oBud_le cF 825000000 (fun _ _ _ h1 h2 h3 => cF_le h1 h2 h3) (yl := yl) hn hx hl; omega

theorem oCost_le' {n xl yl l : Nat} (hn : n ≤ 128) (hx : xl ≤ 128) (hl : l ≤ 1024) :
    ExpOdd.OCost cF n xl yl l ≤ 24770000000 := by
  have := oCost_le cF 825000000 (fun _ _ _ h1 h2 h3 => cF_le h1 h2 h3) (yl := yl) hn hx hl; omega

theorem mk_le128 {n : Nat} (hn : n ≤ 128) : makeCost n ≤ 2136 := by
  have := makeCost_le_makeB n; unfold makeB allocCost at this; omega

/-- `nat.expNN`'s budget (`NBudE`) on the box -/
theorem nb_le {xl yl lm l k : Nat} (hx : xl ≤ 128) (hm : lm ≤ 128) (hl : l ≤ 1024) (hk : k ≤ 8192) :
    ExpEven.NBudE cF cR cS cP xl yl lm l k ≤ 135100000000000 + 8400000000000 * yl := by
  have := cR_le (ℓ := l) hl hx hm
  have := cS_le (yl := yl) hl hx hm
  have := cP_le' (yl := yl) hl hx hk
  have := oBud_le' (yl := yl) hm hx hl
  have := mk_le128 hm
  have := mk_le128 (n := 1) (by omega)
  unfold ExpEven.NBudE; omega

/-- `nat.expNN`'s charged cost (`NCost`) on the box -/
theorem nc_le {xl yl lm l k : Nat} (hx : xl ≤ 128) (hm : lm ≤ 128) (hl : l ≤ 1024) (hk : k ≤ 8192) :
    ExpN.NCost cF cR cS cP xl yl lm l k ≤ 135100000000000 + 8400000000000 * yl := by
  have := cR_le (ℓ := l) hl hx hm
  have := cS_le (yl := yl) hl hx hm
  have := cP_le' (yl := yl) hl hx hk
  have := oCost_le' (yl := yl) hm hx hl
  have := mk_le128 hm
  have := mk_le128 (n := 1) (by omega)
  unfold ExpN.NCost; omega

/-- one `eC` (budget + cost box maxima of a `nat.expNN` call of `expNNEven`) -/
theorem eC_le {xl yl ml l : Nat} (hx : xl ≤ 128) (hm : ml ≤ 128) (hl : l ≤ 1024) :
    ExpEven.eC cF cR cS cP bUC cUC xl yl ml l ≤ 270200000000000 + 16800000000000 * yl := by
  have h1 : bUC xl yl ml l (64 * ml) ≤ 135100000000000 + 8400000000000 * yl :=
    supU_le (fun a0 l0 k0 ha hl0 hk => nb_le hx (by omega) (by omega) (by omega))
  have h2 : cUC xl yl ml l (64 * ml) ≤ 135100000000000 + 8400000000000 * yl :=
    supU_le (fun a0 l0 k0 ha hl0 hk => nc_le hx (by omega) (by omega) (by omega))
  unfold ExpEven.eC; omega

/-- **`nat.expNNEven`'s budget** at entry level 0 -/
theorem cE_le {xl yl ml : Nat} (hx : xl ≤ 128) (hm : ml ≤ 128) :
    cE 0 xl yl ml ≤ 560000000000000 + 33600000000000 * yl := by
  have e3 := eC_le (yl := yl) (l := ExpEven.wL3 0 ml) hx hm (by simp only [StackNat.rnd]; omega)
  have e4 := eC_le (yl := yl) (l := ExpEven.wL4 0 ml) hx hm (by simp only [StackNat.rnd]; omega)
  have hmi := modInv_le (L := ExpEven.wL4 0 ml) (n := 64 * ml) (by simp only [StackNat.rnd]; omega) (by omega)
  have hg := costG_le (n := 64 * ml) (by omega)
  have hml := mulC_le2 (ℓ := ExpEven.wL4 0 ml) (x := ml) (y := ml) (by simp only [StackNat.rnd]; omega)
    (by omega) (by omega)
  unfold cE ExpEven.costE
  unfold makeB stackNatCost allocCost
  simp only [StackNat.rnd] at *
  omega

/-- **the closed budget of `(*Int).exp`** (the two inequalities of `Run.Closed.BudOK`, budget-independent form) -/
theorem main : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
    24 + (makeCost 1 + makeCost n + cR 0 xl n + ExpN.addC cS cE 0 xl yl n + cP 0 xl yl lm +
      ExpOdd.OBud cF n xl yl 0) ≤ 700000000000000 + 42000000000000 * yl ∧
    24 + ExpN.NCost cF cR (ExpN.addC cS cE) cP xl yl n 0 lm ≤ 700000000000000 + 42000000000000 * yl := by
  intro xl yl n lm hx _ _ hn hlm
  have := cR_le (ℓ := 0) (by omega) hx hn
  have := cS_le (ℓ := 0) (yl := yl) (by omega) hx hn
  have := cE_le (yl := yl) hx hn
  have := cP_le' (ℓ := 0) (yl := yl) (by omega) hx (show lm ≤ 8192 by omega)
  have := oBud_le' (yl := yl) hn hx (show 0 ≤ 1024 by omega)
  have := oCost_le' (yl := yl) hn hx (show 0 ≤ 1024 by omega)
  have := mk_le128 hn
  have := mk_le128 (n := 1) (by omega)
  unfold ExpN.NCost ExpN.addC
  omega

end FvModexp.Arm64.ExpBud
