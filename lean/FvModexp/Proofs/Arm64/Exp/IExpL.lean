import FvModexp.Proofs.Arm64.Exp.LibExp
import FvModexp.Proofs.Arm64.Exp.LibNE
import FvModexp.Proofs.Arm64.Top.RunIface

/-!
# `(*Int).exp` (arm64): the program facts (one kernel decision each, in their own module)

`ne_sub`: `nat.expNN`'s program `LibNE` is part of `LibExp` (`(*Int).exp`'s); `namesExp_eq`: `RunIface.namesExp` is
`LibExp.names` (the same list).
-/

open Janus FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IExp

theorem ne_all : LibNE.names.all (fun x => LibExp.names.contains x) = true := by decide +kernel

theorem ne_sub : ∀ x, LibNE.names.contains x = true → LibExp.names.contains x = true := by
  intro x hx
  exact List.all_eq_true.1 ne_all x (List.elem_iff.1 hx)

theorem namesExp_eq : RunIface.namesExp = LibExp.names := rfl

end FvModexp.Arm64.IExp
