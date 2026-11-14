import FvModexp.Proofs.Amd64.Exp.LibN
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): the two `z.make(len m)` return points → `J5` (agent expmc s69)

nat.go:694-699 after `runtime.makeslice` returned (`RSP = t - 0x108`): both return points (`0x5e743c`, `n = 1`, and
`0x5e74b2`, `n ≠ 1`) reload the spilled registers and jump / fall to `J5` = `0x5e750b` (`TESTB R10, R10`, the
`slow` test of nat.go:699): `DX = [t + 0x18]`, `BX = [t + 0x28]`, `SI = [t + 0x58]`, `DI = [t - 0x18]`,
`R8 = [t + 0x60]`, `R9 = [t + 0x68]`, `R10 = zero-extended byte [t + 0x70]`, `R12 = [t + 0x8]`, `R13 = [t + 0x20]`,
`R15 = [t + 0x10]`; `CX = 1`, `R11 = 1` (first) / `CX = [t - 0x90]`, `R11 = [t + 0x28]` (second). `AX` (the block),
`RSP`, `R14`, the memory, `DF` and `X15` are unchanged. Continuation form; no semantic facts (pure register moves).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- `J5` (`0x5e750b`) -/
abbrev j5A : Nat := 6190347

/-- the continuation at `J5`: the reloaded registers (`cx`, `r11` per return point) -/
@[reducible] def J5K (impl : List Amd64.Segment) (ret0 : Nat) (Q : Amd64.Outcome → Prop) (S : State) (t cx r11 : Nat) :
    Prop :=
  ∀ S' : State, S'.rip = BitVec.ofNat 64 j5A → S'.regs 0 = S.regs 0 → S'.regs 1 = BitVec.ofNat 64 cx →
    S'.regs 2 = BitVec.ofNat 64 (S.mem.readLE (t + 0x18) 8) → S'.regs 3 = BitVec.ofNat 64 (S.mem.readLE (t + 0x28) 8) →
    S'.regs 4 = S.regs 4 → S'.regs 6 = BitVec.ofNat 64 (S.mem.readLE (t + 0x58) 8) →
    S'.regs 7 = BitVec.ofNat 64 (S.mem.readLE (t - 0x18) 8) → S'.regs 8 = BitVec.ofNat 64 (S.mem.readLE (t + 0x60) 8) →
    S'.regs 9 = BitVec.ofNat 64 (S.mem.readLE (t + 0x68) 8) → S'.regs 10 = BitVec.ofNat 64 (S.mem.readLE (t + 0x70) 1) →
    S'.regs 11 = BitVec.ofNat 64 r11 → S'.regs 12 = BitVec.ofNat 64 (S.mem.readLE (t + 0x8) 8) →
    S'.regs 13 = BitVec.ofNat 64 (S.mem.readLE (t + 0x20) 8) → S'.regs 15 = BitVec.ofNat 64 (S.mem.readLE (t + 0x10) 8) →
    S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = S.mem →
    Reaches ((LibN.program.link impl).withExit ret0) S' Q

/-- `MOVBLZX` then the 32-bit write's zero extension: the register holds the byte -/
theorem byte_ext (v : Nat) (h : v < 2 ^ (8 * 1)) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 v)) = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the `n = 1` return point (`0x5e743c`) -/
theorem mkp1 (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Amd64.Outcome → Prop) (t : Nat)
    (ht1 : 0x108 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48)
    (S : State) (hacc : S.mem.accessible (t - 0x108) 0x180 false = true)
    (hpc : S.rip = BitVec.ofNat 64 6190140) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (K : J5K impl ret0 Q S t 1 1) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have a1 : t - 0x108 + 0x120 = t + 0x18 := by omega
  have a2 : t - 0x108 + 0x130 = t + 0x28 := by omega
  have a3 : t - 0x108 + 0x160 = t + 0x58 := by omega
  have a4 : t - 0x108 + 0xf0 = t - 0x18 := by omega
  have a5 : t - 0x108 + 0x168 = t + 0x60 := by omega
  have a6 : t - 0x108 + 0x170 = t + 0x68 := by omega
  have a7 : t - 0x108 + 0x178 = t + 0x70 := by omega
  have a8 : t - 0x108 + 0x110 = t + 0x8 := by omega
  have a9 : t - 0x108 + 0x128 = t + 0x20 := by omega
  have a10 : t - 0x108 + 0x118 = t + 0x10 := by omega
  janus64_run [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10] until [j5A]
  refine K _ ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 ?r19
  case r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15 | r16 | r17 | r18 | r19 =>
    first | (janus64_simp; done) | (janus64_simp; exact byte_ext _ (Janus.Arm64.Memory.readLE_lt _ _ _)) | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the `n ≠ 1` return point (`0x5e74b2`) -/
theorem mkp2 (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Amd64.Outcome → Prop) (t : Nat)
    (ht1 : 0x108 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48)
    (S : State) (hacc : S.mem.accessible (t - 0x108) 0x180 false = true)
    (hpc : S.rip = BitVec.ofNat 64 6190258) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (K : J5K impl ret0 Q S t (S.mem.readLE (t - 0x90) 8) (S.mem.readLE (t + 0x28) 8)) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have a1 : t - 0x108 + 0x120 = t + 0x18 := by omega
  have a2 : t - 0x108 + 0x130 = t + 0x28 := by omega
  have a3 : t - 0x108 + 0x160 = t + 0x58 := by omega
  have a4 : t - 0x108 + 0xf0 = t - 0x18 := by omega
  have a5 : t - 0x108 + 0x168 = t + 0x60 := by omega
  have a6 : t - 0x108 + 0x170 = t + 0x68 := by omega
  have a7 : t - 0x108 + 0x178 = t + 0x70 := by omega
  have a8 : t - 0x108 + 0x110 = t + 0x8 := by omega
  have a9 : t - 0x108 + 0x128 = t + 0x20 := by omega
  have a10 : t - 0x108 + 0x118 = t + 0x10 := by omega
  have a11 : t - 0x108 + 0x78 = t - 0x90 := by omega
  janus64_run [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] until [j5A]
  refine K _ ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 ?r19
  case r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15 | r16 | r17 | r18 | r19 =>
    first | (janus64_simp; done) | (janus64_simp; exact byte_ext _ (Janus.Arm64.Memory.readLE_lt _ _ _)) | rfl

end FvModexp.Amd64.ExpN
