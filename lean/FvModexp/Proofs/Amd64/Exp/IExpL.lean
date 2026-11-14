import FvModexp.Proofs.Amd64.Exp.LibExpI
import FvModexp.Proofs.Amd64.Exp.LibNE
import FvModexp.Proofs.Amd64.Top.RunIface

set_option autoImplicit false

/-!
# `(*Int).exp` (amd64): `LibNE.names ⊆ LibExpI.names`, `RunIface.namesExp = LibExpI.names` (agent expmc s76; twin of
`Arm64.IExp` IExpL)
-/

namespace FvModexp.Amd64.IExp

/-- the position in `LibExpI.names` of each name of `LibNE.names` in `LibExpI.names` (generated; checked by `ne_idx`) -/
def neIdx : List Nat := [4, 6, 8, 0, 5, 7, 43, 71, 34, 32, 33, 3, 1, 68, 65, 57, 47, 52, 45, 75, 76, 42, 38, 15, 16, 10, 12, 69, 61, 50, 48, 55, 53, 67, 58, 72, 59, 73, 21, 30, 40, 36, 74, 28, 29, 23, 11, 2, 64, 17, 18, 26, 24, 14, 60, 20, 22, 31, 13, 44, 35, 66, 46, 39, 70, 62, 63, 51, 49, 56, 54, 41, 37, 19, 27, 25]

theorem ne_idx : LibNE.names.map some = neIdx.map (fun i => LibExpI.names[i]?) := by decide +kernel

theorem ne_sub : ∀ x, LibNE.names.contains x = true → LibExpI.names.contains x = true := by
  intro x hx
  have h1 : some x ∈ LibNE.names.map some := List.mem_map_of_mem (List.elem_iff.1 hx)
  rw [ne_idx] at h1
  obtain ⟨i, -, hi⟩ := List.mem_map.1 h1
  exact List.elem_iff.2 (List.mem_of_getElem? hi)

theorem namesExp_eq : RunIface.namesExp = LibExpI.names := rfl

end FvModexp.Amd64.IExp
