import FvModexp.Proofs.Common.DivRec
import FvModexp.Proofs.Common.IntDiv
import FvModexp.Proofs.Common.MulClosed
/-!
# Closed division models

The division models are parametric in their recursive callees (`DivContract.lean`); here they are instantiated with the
concrete models: `divRecursive divBasic natMul` (natdiv.go:740, divBasic natdiv.go:646, nat.mul natmul.go:16), and
`nat.div` / `nat.rem` / `Int.QuoRem` / `Int.Div` / `Int.Mod` on top of it.  The quotient storage `qs` (`z.make(m+1)` /
`stk.nat(...)` contents) does not matter for the values; the closed versions pass zeros of the Go length.
-/
namespace FvModexp.Mdl

/-- `(z nat) divRecursive(stk, u, v)` with the concrete callees. -/
def divRecursiveC : List Nat → List Nat → List Nat → List Nat × List Nat := divRecursive divBasic natMul

theorem divRecursiveC_contract : DivRecursiveContract divRecursiveC :=
  divRecursive_contract divBasic divBasic_contract natMul natMul_spec

/-- `z.div(stk, z2, u, v)` (natdiv.go:518), closed: `(q, r)`. -/
def natDivC (u v : List Nat) : List Nat × List Nat :=
  natDiv divRecursiveC (List.replicate (u.length - v.length + 1) 0) u v

theorem natDivC_spec (u v : List Nat) (hu : Wd u) (hv : Wd v) (hnu : Normed u) (hnv : Normed v) (hve : v ≠ []) :
    Wd (natDivC u v).1 ∧ Wd (natDivC u v).2 ∧ Normed (natDivC u v).1 ∧ Normed (natDivC u v).2 ∧
    val (natDivC u v).1 = val u / val v ∧ val (natDivC u v).2 = val u % val v ∧
    (natDivC u v).1.length ≤ u.length - v.length + 1 ∧ (natDivC u v).2.length ≤ v.length :=
  natDiv_spec divRecursiveC divRecursiveC_contract _ u v hu hv hnu hnv hve (Wd_replicate_zero _)
    (fun _ _ => by simp)

/-- `z.rem(stk, u, v)` (natdiv.go:505), closed. -/
def natRemC (u v : List Nat) : List Nat :=
  natRem divRecursiveC (List.replicate (max 1 (u.length - (v.length - 1))) 0) u v

theorem natRemC_spec (u v : List Nat) (hu : Wd u) (hv : Wd v) (hnu : Normed u) (hnv : Normed v) (hve : v ≠ []) :
    Wd (natRemC u v) ∧ Normed (natRemC u v) ∧ val (natRemC u v) = val u % val v ∧ (natRemC u v).length ≤ v.length :=
  natRem_spec divRecursiveC divRecursiveC_contract _ u v hu hv hnu hnv hve (Wd_replicate_zero _) (by simp)

/-- Quotient storage handed to `nat.div` by `Int.QuoRem` (`z.abs`, made to length `m+1` inside `divLarge`). -/
def qsOf (x y : GInt) : List Nat := List.replicate (x.abs.length - y.abs.length + 1) 0

/-- `(*Int).QuoRem` (int.go:299), closed. -/
def intQuoRemC (x y : GInt) : GInt × GInt := intQuoRem divRecursiveC (qsOf x y) x y
/-- `(*Int).Div` (int.go:308), closed. -/
def intDivC (x y : GInt) : GInt := intDiv divRecursiveC (qsOf x y) x y
/-- `(*Int).Mod` (int.go:325), closed. -/
def intModC (x y : GInt) : GInt := intMod divRecursiveC (qsOf x y) x y

theorem intQuoRemC_spec (x y : GInt) (hx : x.Ok) (hy : y.Ok) (hy0 : y.abs ≠ []) :
    (intQuoRemC x y).1.Ok ∧ (intQuoRemC x y).2.Ok ∧ (intQuoRemC x y).1.Canon ∧ (intQuoRemC x y).2.Canon ∧
    (intQuoRemC x y).1.ival = x.ival.tdiv y.ival ∧ (intQuoRemC x y).2.ival = x.ival.tmod y.ival :=
  intQuoRem_spec divRecursiveC divRecursiveC_contract _ x y hx hy hy0 (Wd_replicate_zero _) (fun _ _ => by simp [qsOf])

theorem intDivC_spec (x y : GInt) (hx : x.Ok) (hy : y.Ok) (hy0 : y.abs ≠ []) :
    (intDivC x y).Ok ∧ (intDivC x y).Canon ∧ (intDivC x y).ival = x.ival / y.ival :=
  intDiv_spec divRecursiveC divRecursiveC_contract _ x y hx hy hy0 (Wd_replicate_zero _) (fun _ _ => by simp [qsOf])

theorem intModC_spec (x y : GInt) (hx : x.Ok) (hy : y.Ok) (hy0 : y.abs ≠ []) :
    (intModC x y).Ok ∧ (intModC x y).Canon ∧ (intModC x y).ival = x.ival % y.ival :=
  intMod_spec divRecursiveC divRecursiveC_contract _ x y hx hy hy0 (Wd_replicate_zero _) (fun _ _ => by simp [qsOf])

end FvModexp.Mdl
