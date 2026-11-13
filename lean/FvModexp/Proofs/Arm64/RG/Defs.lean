import Extracted
import FvModexp.Proofs.Common.Core

/-! Callee contracts used by the `RequiredGas` proof (arm64): `(*uint256.Int).SetBytes` for slices of at most 32 bytes and
`runtime.memmove` for at most 32 bytes, both as `Summary`s of the extracted program, returning in the canonical `retStateX` shape. -/

namespace FvModexp.Arm64.RG

/-- `DataLoaded` across a chain of stores into writable ranges (from the `DataLoaded` hypothesis about the base memory). -/
macro "dl_close" : tactic => `(tactic| (dsimp only; repeat (first | with_reducible assumption | (apply Janus.Program.DataLoaded.writeLE <;> first | with_reducible assumption | janus_disch | skip))))

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

abbrev sbA : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetBytes"
abbrev mvA : Nat := segAddr Extracted.program "runtime.memmove"

/-- A well-formed return address in `X30`. -/
abbrev LR (s : State) : Prop := (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56

/-- `z.SetBytes(buf)` with `z = X0`, `buf = (X1, X2 = len, X3)`, `len ≤ 32`. -/
abbrev SbPre (len : Nat) (s : State) : Prop :=
  LR s ∧ GuardOK s 48 ∧ StackOK s 88 72 ∧ Extracted.program.DataLoaded s.mem ∧ (s.regs 2).toNat = len ∧
    len ≤ (s.regs 3).toNat ∧ (s.regs 3).toNat < 2 ^ 48 ∧ Ptr32 s.mem (s.regs 0) true ∧ Ptr s.mem (s.regs 1) len false ∧
    Disjoint (s.regs 0).toNat 32 (s.regs 1).toNat len ∧ Disjoint (s.regs 0).toNat 32 (s.sp.toNat - 88) 160 ∧
    Disjoint (s.regs 1).toNat len (s.sp.toNat - 88) 160 ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 160

abbrev SbPost (len : Nat) (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
    s' = retStateX s junk [s.regs 0] f v m ex ep ∧
    MemFrame s.mem m [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 88, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)] ∧
    val256 m (s.regs 0).toNat = FvModexp.Aux.fromBE (fun i => s.mem.readLE ((s.regs 1).toNat + i) 1) len ∧
    Extracted.program.DataLoaded m

/-- `memmove(dst = X0, src = X1, n = X2)` with `n ≤ 32`, disjoint operands, `dst` writable and `src` readable. -/
abbrev MvPre (n : Nat) (s : State) : Prop :=
  LR s ∧ (s.regs 2).toNat = n ∧ (s.regs 0).toNat + n ≤ 2 ^ 48 ∧ (s.regs 1).toNat + n ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 0).toNat n true = true ∧ s.mem.accessible (s.regs 1).toNat n false = true ∧
    Disjoint (s.regs 0).toNat n (s.regs 1).toNat n ∧ Extracted.program.DataLoaded s.mem

abbrev MvPost (n : Nat) (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat)) (ep : Nat → Bool),
    s' = retStateX s junk [] f v m ex ep ∧ MemFrame s.mem m [((s.regs 0).toNat, (s.regs 0).toNat + n)] ∧
    (∀ i, i < n → m.bytes ((s.regs 0).toNat + i) = s.mem.bytes ((s.regs 1).toNat + i)) ∧ Extracted.program.DataLoaded m

end FvModexp.Arm64.RG
