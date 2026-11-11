import Janus

/-! # `makeslice` with a zero-byte result (amd64) — PROPOSED Janus contract, local premise

The amd64 twin of `FvModexp.Arm64.MakesliceZeroLive` (see `Proofs/Arm64/MakesliceZero.lean` and JANUS-ISSUES.md, top
s8): for `et.size · cap = 0` the call returns (`retState64` shape of the live contracts), memory changes only in `R.rt`
and the callee's window, the live set and the budget are unchanged (go1.26.x `mallocgc`: `if size == 0 { return
unsafe.Pointer(&zerobase) }`). A PREMISE like `MakesliceLiveContract64`; replaced by the pinned contract once Janus has
one. -/

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Amd64

/-- The return of a zero-byte allocation (amd64): like `LiveAllocRet64` without the object. -/
@[reducible] def ZeroAllocRet64 (R : RtInv) (stack nargs : Nat) (L : List (Nat × Nat)) (b : Nat) (s s' : State) : Prop :=
  ∃ (ptr : W64) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Janus.Arm64.Memory)
    (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk [ptr] f x yh m zh kr ∧
      MemFrame s.mem m (R.rt ++ calleeStack64 s stack nargs) ∧ LiveFrame s.mem m L [] ∧
      R.inv b L (s.regs 14).toNat (view R.rt L m)

/-- **`runtime.makeslice(et, len, cap)` with `et.size · cap = 0`, live** (amd64; `RAX = et`, `RBX = len`, `RCX = cap`). -/
def MakesliceZeroLive64 (p : Janus.Amd64.Program) (addr : Nat) (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => (MakeslicePre64 stack s ∧ StackRoom64 s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b 0 (s.regs 14).toNat s.mem
        (liveWin64 s stack 3)) ∧
      typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat = 0)
    (fun s s' => ZeroAllocRet64 R stack 3 L b s s')

theorem MakesliceZeroLive64.of_codeIn {p P : Janus.Amd64.Program} (hc : CodeIn64 p P) {a st : Nat} {R : RtInv}
    (h : MakesliceZeroLive64 p a st R) : MakesliceZeroLive64 P a st R :=
  fun L b => Summary.of_codeIn64 hc (h L b)

end FvModexp.Amd64
