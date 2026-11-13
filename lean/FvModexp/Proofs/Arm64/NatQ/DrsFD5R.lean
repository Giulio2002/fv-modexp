import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsFD4
import FvModexp.Proofs.Arm64.NatQ.DrsD6R
import FvModexp.Proofs.Common.MaskWord

/-! (Q-form copy of Arm64/Nat/DrsFD5R.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final block: `if c > 0 { c = subVW(u[ql:], u[ql:], c) }` test (natdiv.go:885-887)

`d5rF`: from `subVV.abi0`'s return `0x1bac4c`: borrow `0` → `0x1bac98` (through the `CBNZ`, memory unchanged);
borrow `1` → `CALL subVW(u[ql:], u[ql:], 1)` (`0x1bac8c`, return `0x1bac90`). Adapted from DrsD5R.
-/

set_option autoImplicit false

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

/-- after the final borrow test (`0x1bac98`: `qhat.norm()` for `addTo(z, qhat.norm())`) -/
abbrev rFD5 : Nat := 0x1bac98

/-- `subVW(u[ql:], u[ql:], c)`'s return address -/
abbrev rFD5W : Nat := 0x1bac90

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d5rF (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (st : Mdl.St) (Q : State → Prop) (b : Nat) (hb1 : b ≤ 1)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rFD4) (hsp : T.sp = s.sp - 400#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 408#64) (h18 : T.regs 18 = s.regs 18)
    (hmc : McF R c s Lk bk T.mem j Z U qv st) (hv3 : V3F c s T.mem qv (c.PF s U).length) (hcy : T.mem.readLE (s.sp.toNat - 320) 8 = b)
    (hlt : b = 1 → (c.PF s U).length < c.u1)
    (k0 : ∀ X : State, X.pc = BitVec.ofNat 64 rFD5 → X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 →
      X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 → X.mem = T.mem → b = 0 →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q)
    (kW : ∀ Y : State, Y.pc = BitVec.ofNat 64 SubVW.entry → Y.regs 30 = BitVec.ofNat 64 rFD5W →
      Y.sp = s.sp - 400#64 → Y.regs 28 = s.regs 28 → Y.regs 29 = s.sp - 408#64 → Y.regs 18 = s.regs 18 →
      Y.regs 0 = BitVec.ofNat 64 (c.up + 8 * (c.PF s U).length) →
      Y.regs 1 = BitVec.ofNat 64 (c.u1 - (c.PF s U).length) →
      Y.regs 2 = BitVec.ofNat 64 (c.uc - (c.PF s U).length) →
      Y.regs 3 = BitVec.ofNat 64 (c.up + 8 * (c.PF s U).length) →
      Y.regs 4 = BitVec.ofNat 64 (c.u1 - (c.PF s U).length) →
      Y.regs 5 = BitVec.ofNat 64 (c.uc - (c.PF s U).length) → Y.regs 6 = 1#64 → Y.mem = T.mem → b = 1 →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) Y Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, hulc, huc40, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, hu48, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hvu := hcr.vu1
  have hjB := hmc.jB
  have hu1 := hcr.u1ul
  have hPl := PF_len_le2 (c := c) (s := s) (U := U) (by omega)
  have hle' : BitVec.ofNat 64 (c.PF s U).length ≤ BitVec.ofNat 64 c.u1 := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  have r1 := hmc.bd.sl.ul'; have r4 := hmc.bd.sl.s7; have r5 := hmc.bd.sl.s5; have r6 := hv3.s144
  have hB : Box (McF R c s Lk bk T.mem j Z U qv st) := ⟨hmc⟩
  clear hmc hv3
  rcases (by omega : b = 0 ∨ b = 1) with hb | hb
  · subst hb
    janus_run [hcy] until [rFD5]
    refine k0 _ rfl rfl ?_ ?_ ?_ rfl rfl
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h28
    · exact h29
    · exact h18
  · subst hb
    have hlt' := hlt rfl
    have e1 := bvS1 (b := (c.PF s U).length) (u := c.u1) (by omega) (by omega)
    have e2 := bvS1 (b := (c.PF s U).length) (u := c.uc) (by omega) (by omega)
    have e3 := bvM1 (q := c.up) (a := (c.PF s U).length) (x := c.uc) (by omega) (by omega) (by omega)
    janus_run [hcy, r1, r4, r5, r6] until [SubVW.entry]
    refine kW _ rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals first | exact h28 | exact h29 | exact h18 | exact e3 | exact e1 | exact e2 | rfl
end FvModexp.Arm64.Q.DivRec
