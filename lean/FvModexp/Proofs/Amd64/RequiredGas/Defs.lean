import Extracted
import FvModexp.Proofs.Common.Core
import FvModexp.Proofs.Common.Ret64

/-! Callee contracts used by the `RequiredGas` proof (amd64): `(*uint256.Int).SetBytes` for slices of at most 32 bytes and
`runtime.memmove` for at most 32 bytes, both as `Summary`s of the extracted program, returning in the canonical `retState64` shape. -/

namespace FvModexp.Amd64.RG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

/-- `DataLoaded` across a chain of stores into writable ranges (from the `DataLoaded` hypothesis about the base memory). -/
macro "dl_close" : tactic => `(tactic| (dsimp only; repeat (first | with_reducible assumption | (apply Janus.Amd64.Program.DataLoaded.writeLE <;> first | with_reducible assumption | janus64_disch | skip))))

abbrev sbA : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetBytes"
abbrev mvA : Nat := segAddr Extracted.program "runtime.memmove"

/-- The return address slot `[RSP, RSP + 8)` is readable and holds a canonical user address. -/
abbrev RA (s : State) : Prop :=
  s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ (s.regs 4).toNat + 8 ≤ 2 ^ 48

/-- `z.SetBytes(buf)` with `z = RAX`, `buf = (RBX, RCX = len, RDI = cap)`, `len ≤ 32`; the stack window `[RSP - 88, RSP + 24)`
(the frame, `SetBytesN`'s frame, the return address and the two spill slots). -/
abbrev SbPre (len : Nat) (s : State) : Prop :=
  RA s ∧ StackGuardOK s 48 ∧ StackWritable s 88 24 ∧ s.xmm 15 = 0 ∧ Extracted.program.DataLoaded s.mem ∧ (s.regs 1).toNat = len ∧
    len ≤ (s.regs 7).toNat ∧ (s.regs 7).toNat < 2 ^ 48 ∧ Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) len false ∧
    Janus.Spec.Disjoint (s.regs 0).toNat 32 (s.regs 3).toNat len ∧ Janus.Spec.Disjoint (s.regs 0).toNat 32 ((s.regs 4).toNat - 88) 112 ∧
    Janus.Spec.Disjoint (s.regs 3).toNat len ((s.regs 4).toNat - 88) 112 ∧ ((s.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 88 ∨ (s.regs 4).toNat + 24 ≤ (s.regs 14).toNat + 16)

abbrev SbPost (len : Nat) (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk [s.regs 0] f x yh m zh kr ∧
    MemFrame s.mem m [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 88, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24)] ∧
    (val256 m (s.regs 0).toNat = FvModexp.Aux.fromBE (fun i => s.mem.readLE ((s.regs 3).toNat + i) 1) len ∧
    Extracted.program.DataLoaded m)

/-- `memmove(dst = RAX, src = RBX, n = RCX)` with `n ≤ 32`, disjoint operands, `dst` writable (and apart from the return-address
slot) and `src` readable. -/
abbrev MvPre (n : Nat) (s : State) : Prop :=
  RA s ∧ (s.regs 1).toNat = n ∧ (s.regs 0).toNat + n ≤ 2 ^ 48 ∧ (s.regs 3).toNat + n ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 0).toNat n true = true ∧ s.mem.accessible (s.regs 3).toNat n false = true ∧
    Janus.Spec.Disjoint (s.regs 0).toNat n (s.regs 3).toNat n ∧ Janus.Spec.Disjoint (s.regs 0).toNat n (s.regs 4).toNat 8 ∧
    Extracted.program.DataLoaded s.mem

abbrev MvPost (n : Nat) (s s' : State) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory) (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk [] f x yh m zh kr ∧ MemFrame s.mem m [((s.regs 0).toNat, (s.regs 0).toNat + n)] ∧
    ((∀ i, i < n → m.bytes ((s.regs 0).toNat + i) = s.mem.bytes ((s.regs 3).toNat + i)) ∧ Extracted.program.DataLoaded m)

end FvModexp.Amd64.RG
