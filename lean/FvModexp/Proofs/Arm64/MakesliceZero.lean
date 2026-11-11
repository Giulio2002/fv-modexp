import Janus

/-! # `makeslice` with a zero-byte result (arm64) — local premise = Janus PR #2 definition (byte-identical body)

`MakesliceLiveContract` (Janus v0.2.0) appends the result range `[ptr, ptr + blockSize 0 _) = [ptr, ptr)` to the live
set also when `et.size · cap = 0`, while its post says nothing about `ptr` in that case (`Q` only under `0 < size`).
The invariant after such a call is therefore about `L ++ [(ptr, ptr)]` with an arbitrary `ptr`, and a caller can no
longer establish `LiveExt R L L'` (`InRanges ptr 0 R.rt`) nor `LiveSep` of a later call (`Outside ptr 0 win`).
`(*Int).Bytes` of a zero `*Int` calls `makeslice(uint8, 0, 0)` (`int.go:531`), reachable from `Run` (result `0`).

Real runtime (go1.26.x `runtime.makeslice` → `mallocgc(0, …)`): `if size == 0 { return unsafe.Pointer(&zerobase) }`
(malloc.go `mallocgc`, first statement after the GC-assist checks) — nothing is allocated, no runtime state changes.
This contract states exactly that: for a zero-byte request the call returns (retState shape of the live contracts), the
memory changes only in `R.rt` and the callee's window, the live set and the budget are unchanged.

It is a PREMISE of the theorems that use it, exactly like `MakesliceLiveContract` (JANUS-ISSUES.md, top s8); once a
Janus release pins an equivalent contract, this file is deleted and the premise is replaced by the pinned one. -/

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64

/-- The return of a zero-byte allocation: like `LiveAllocRet` without the object (live set and budget kept). -/
@[reducible] def ZeroAllocRet (R : RtInv) (stack nargs : Nat) (L : List (Nat × Nat)) (b : Nat) (s s' : State) : Prop :=
  ∃ (ptr : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
    (ex : Option (Nat × Nat)) (ep : Nat → Bool),
    s' = retStateX s junk [ptr] f v m ex ep ∧
      MemFrame s.mem m (R.rt ++ calleeStack s stack nargs) ∧ LiveFrame s.mem m L [] ∧
      R.inv b L (s.regs 28).toNat (view R.rt L m)

/-- **`runtime.makeslice(et, len, cap)` with `et.size · cap = 0`, live** (arm64). -/
def MakesliceZeroLive (p : Program) (addr : Nat) (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => (MakeslicePre stack s ∧ StackRoom s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b 0
        (s.regs 28).toNat s.mem (calleeStack s stack 3)) ∧
      typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat = 0 ∧
      Outside (s.regs 0).toNat 16 (calleeStack s stack 3))
    (fun s s' => ZeroAllocRet R stack 3 L b s s')

theorem MakesliceZeroLive.of_codeIn {p P : Program} (hc : CodeIn p P) {a st : Nat} {R : RtInv}
    (h : MakesliceZeroLive p a st R) : MakesliceZeroLive P a st R :=
  fun L b => Summary.of_codeIn hc (h L b)

end FvModexp.Arm64
