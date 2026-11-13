import FvModexp.Proofs.Amd64.NatQ.DrsDV
import FvModexp.Proofs.Amd64.NatQ.DrsFRel4

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFV.lean; ISA-free model glue)
# `divRecursiveStep` (amd64), final block: the model glue (pure)

`Cx.sTF` (`u -= qhatv` with the borrow at the end of the final correction loop), `finM_eq`, `fstep`
(`Mdl.finalBlock_spec` instance), `e_leF` / `c_zeroF` (the two `panic`s excluded), `q_fitF`, `fin_eq`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- `u -= qhatv` (with the borrow into `u[len(qhatv):]`) at the final loop's exit -/
@[reducible] def Cx.sTF (c : Cx) (s : State) (U : List Nat) : List Nat × Nat :=
  Mdl.subToC (c.sFF s U).w ((c.sFF s U).buf.take (c.PF s U).length)

theorem finM_eq {c : Cx} {s : State} {U : List Nat} :
    Mdl.finM Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) U =
      { q := (c.sFF s U).qhat, w := (c.sTF s U).1, c := (c.sTF s U).2,
        e := Mdl.cmpQ (c.PF s U).length (c.sFF s U) } := rfl

/-- `Mdl.finalBlock_spec` for the final block -/
theorem fstep {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} (hcr : Cr R c s) (hli : c.LI s j Z U)
    (hjB : j ≤ c.vl / 2) :
    (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).1.length = c.ql ∧
    (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).2.length = c.u1 - c.vl + c.vl ∧
    Mdl.Wd (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).1 ∧
    Mdl.Wd (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).2 ∧
    Mdl.val (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).1 =
      natVal s.mem c.up c.u1 / Mdl.val (c.V s) ∧
    Mdl.val (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).2 =
      natVal s.mem c.up c.u1 % Mdl.val (c.V s) ∧
    (∀ d ∈ (Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U).2.drop c.vl, d = 0) ∧
    (Mdl.finM Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) U).c = 0 ∧
    (Mdl.finM Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) U).e ≤ 0 ∧
    (Mdl.norm (Mdl.finR Mdl.recI (c.V s) (c.vl / 2) U).1).length + (c.vl / 2 - 1) ≤ 3 * c.vl ∧
    (Mdl.norm (Mdl.finM Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) U).q).length ≤ c.ql := by
  obtain ⟨r1, r2, r3⟩ := room hcr
  have h40 := hcr.h40
  exact Mdl.finalBlock_spec Mdl.recI c.vl (Mdl.recI_ok _) Mdl.mulI Mdl.mulI_ok (c.V s) c.vl (c.vl / 2) (c.u1 - c.vl)
    c.ql (natVal s.mem c.up c.u1) j Z U (Asm.Wd_limbs _ _ _) (Asm.length_limbs _ _ _) (topV hcr) (by omega)
    (by omega) (by omega) hli hjB r2

/-- the `panic("impossible")` after the final correction loop is unreachable -/
theorem e_leF {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} (hcr : Cr R c s) (hli : c.LI s j Z U)
    (hjB : j ≤ c.vl / 2) : Mdl.cmpQ (c.PF s U).length (c.sFF s U) ≤ 0 :=
  (fstep hcr hli hjB).2.2.2.2.2.2.2.2.1

/-- the last borrow is `0` (the `panic` on `c != 0` is unreachable) -/
theorem c_zeroF {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} (hcr : Cr R c s) (hli : c.LI s j Z U)
    (hjB : j ≤ c.vl / 2) : (c.sTF s U).2 = 0 :=
  (fstep hcr hli hjB).2.2.2.2.2.2.2.1

/-- `qhat.norm()` fits `z` -/
theorem q_fitF {R : RtInv} {c : Cx} {s : State} {j : Nat} {Z U : List Nat} (hcr : Cr R c s) (hli : c.LI s j Z U)
    (hjB : j ≤ c.vl / 2) : (Mdl.norm (c.sFF s U).qhat).length ≤ c.ql :=
  (fstep hcr hli hjB).2.2.2.2.2.2.2.2.2.2

/-- the results of the final block, in terms of the loop's model state -/
theorem fin_eq {c : Cx} {s : State} {Z U : List Nat} :
    Mdl.finalBlock Mdl.recI Mdl.mulI (c.V s) c.vl (c.vl / 2) Z U =
      (Mdl.addTo Z (Mdl.norm (c.sFF s U).qhat), (c.sTF s U).1) := rfl

end FvModexp.Amd64.Q.DivRec
