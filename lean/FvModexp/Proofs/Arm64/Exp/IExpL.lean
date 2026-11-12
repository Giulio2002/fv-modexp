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

/-- the position in `LibExp.names` of each name of `LibNE.names` (generated; checked by `ne_idx`) -/
def neIdx : List Nat := [4, 6, 8, 0, 5, 7, 43, 71, 34, 32, 33, 3, 1, 68, 65, 57, 47, 52, 45, 76, 77, 42, 38, 15, 16, 10, 12, 69, 61, 50, 48, 55, 53, 67, 58, 72, 59, 73, 21, 30, 40, 36, 75, 28, 29, 23, 11, 2, 64, 17, 18, 26, 24, 14, 60, 20, 74, 78, 22, 31, 13, 44, 35, 66, 46, 39, 70, 62, 63, 51, 49, 56, 54, 41, 37, 19, 27, 25]

/-- one string equality per name (instead of the quadratic `contains` sweep: 6.7 GB → small) -/
theorem ne_idx : LibNE.names.map some = neIdx.map (fun i => LibExp.names[i]?) := by decide +kernel

theorem ne_sub : ∀ x, LibNE.names.contains x = true → LibExp.names.contains x = true := by
  intro x hx
  have h1 : some x ∈ LibNE.names.map some := List.mem_map_of_mem (List.elem_iff.1 hx)
  rw [ne_idx] at h1
  obtain ⟨i, -, hi⟩ := List.mem_map.1 h1
  exact List.elem_iff.2 (List.mem_of_getElem? hi)

theorem namesExp_eq : RunIface.namesExp = LibExp.names := rfl

end FvModexp.Arm64.IExp
