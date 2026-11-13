import FvModexp.Proofs.Amd64.NatQ.DrsPro

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): `u.norm()`'s exit → `v.norm()`'s head, and `v.norm()`'s exit → the dispatch

Code `0x5ef8d1 … 0x5ef8ef`: the slice bound check of `u = u.norm()` (`CMPQ R8, R9; JB panicSliceAcap`, refuted by
`len ≤ cap`), then `v`'s pointer and length are loaded from the caller's argument slots (`0x190(SP) = r + 8`,
`0x198(SP) = r + 16`, `r` = entry `RSP`) and control jumps to `v.norm()`'s head. Code `0x5ef8ff … 0x5ef90f`: `v`'s cap
(`0x1a0(SP) = r + 24`) is loaded into `R12` and the bound check of `v = v.norm()` (`CMPQ R11, R12; JB`) passes. Twin of
the corresponding steps of Arm64/Nat/DrsPro.lean.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

/-- the dispatch point after both normalisations (`TESTQ R8, R8`) -/
abbrev dTest : Nat := 0x5ef910

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `u.norm()`'s exit → `v.norm()`'s head: `DX = [SP + 0x190]`, `R11 = [SP + 0x198]`, everything else kept -/
theorem pro1 (impl : List Amd64.Segment) (r : Nat) (P : State) (Q : State → Prop)
    (hpc : P.rip = BitVec.ofNat 64 nExit1) (hle : (P.regs 8).toNat ≤ (P.regs 9).toNat)
    (hacc : P.mem.accessible ((P.regs 4).toNat + 0x190) 16 false = true)
    (hsp : (P.regs 4).toNat + 0x1a0 ≤ 2 ^ 48)
    (k : ∀ P', P'.rip = BitVec.ofNat 64 nHead2 → P'.mem = P.mem →
      P'.regs 2 = BitVec.ofNat 64 (P.mem.readLE ((P.regs 4).toNat + 0x190) 8) →
      P'.regs 11 = BitVec.ofNat 64 (P.mem.readLE ((P.regs 4).toNat + 0x198) 8) →
      (∀ j, j ≠ 2 → j ≠ 11 → P'.regs j = P.regs j) → P'.fsBase = P.fsBase → P'.df = P.df →
      P'.xmm 15 = P.xmm 15 → ReachesRet (LibDrs.program.link impl) r P' Q) :
    ReachesRet (LibDrs.program.link impl) r P Q := by
  have hnb : ¬ (P.regs 9 < P.regs 8) := by rw [BitVec.lt_def]; omega
  janus64_run [hnb, BitVec.msb_eq_decide] until [nHead2]
  refine k _ rfl rfl ?_ ?_ ?_ rfl rfl rfl
  all_goals try (janus64_simp; done)
  · intro j h2 h11; simp only [Janus.Amd64.Tactic.setRegF_apply, h2, h11, ite_false]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `v.norm()`'s exit → the dispatch: `R12 = [SP + 0x1a0]`, the bound check `R11 ≤ R12` passes -/
theorem pro2 (impl : List Amd64.Segment) (r : Nat) (P : State) (Q : State → Prop)
    (hpc : P.rip = BitVec.ofNat 64 nExit2)
    (hle : (P.regs 11).toNat ≤ P.mem.readLE ((P.regs 4).toNat + 0x1a0) 8)
    (hacc : P.mem.accessible ((P.regs 4).toNat + 0x1a0) 8 false = true)
    (hsp : (P.regs 4).toNat + 0x1a8 ≤ 2 ^ 48)
    (k : ∀ P', P'.rip = BitVec.ofNat 64 dTest → P'.mem = P.mem →
      P'.regs 12 = BitVec.ofNat 64 (P.mem.readLE ((P.regs 4).toNat + 0x1a0) 8) →
      (∀ j, j ≠ 12 → P'.regs j = P.regs j) → P'.fsBase = P.fsBase → P'.df = P.df →
      P'.xmm 15 = P.xmm 15 → ReachesRet (LibDrs.program.link impl) r P' Q) :
    ReachesRet (LibDrs.program.link impl) r P Q := by
  have hrd : P.mem.readLE ((P.regs 4).toNat + 0x1a0) 8 < 2 ^ 64 := Janus.Amd64.Tactic.readLE_lt_8 _ _
  have hnb : ¬ (BitVec.ofNat 64 (P.mem.readLE ((P.regs 4).toNat + 0x1a0) 8) < P.regs 11) := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrd]; omega
  janus64_run [hnb, BitVec.msb_eq_decide] until [dTest]
  refine k _ rfl rfl ?_ ?_ rfl rfl rfl
  all_goals try (janus64_simp; done)
  · intro j h12; simp only [Janus.Amd64.Tactic.setRegF_apply, h12, ite_false]

end FvModexp.Amd64.Q.DivRec
