import FvModexp.Proofs.Amd64.NatQ.DrsFD4
import FvModexp.Proofs.Amd64.NatQ.DrsD5R
import FvModexp.Proofs.Common.MaskWord

set_option autoImplicit false

/-! (amd64 twin (asm s54) of Arm64/NatQ/DrsFD5R.lean; adapted from Amd64/NatQ/DrsD5R.lean)
# `divRecursiveStep` (amd64), final block: `if c > 0 { subVW(u[ql:], u[ql:], 1) }` test (natdiv.go:883-884)

`d5rF`: from `0x5f05cc` (`rFD5`, the borrow `b ≤ 1` at `r - 320`): `MOVQ 0x48(SP), R9; TESTQ R9, R9; JBE 0x5f062b`.
* `b = 0`: the join `0x5f062b`, `TESTQ R9, R9; JA` (gopanic) not taken → `0x5f0630` (`rJF6`), memory unchanged.
* `b = 1`: `CMPQ DX, SI; JA` (`ql ≤ len u`), `DI = up + (mask & 8 ql)`, `CALL subVW` (`0x5f0623`, return `0x5f0628`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- after the `if c > 0 { panic }` test (natdiv.go:886-887): `0x5f0630` -/
abbrev rJF6 : Nat := 0x5f0630

/-- the return address of the final block's `subVW(u[ql:], u[ql:], 1)` (`MOVQ AX, R9`) -/
abbrev rFD5W : Nat := 0x5f0628

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d5rF (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (st : Mdl.St) (Q : State → Prop) (b : Nat) (hb1 : b ≤ 1)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rFD5) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false) (hx15 : T.xmm 15 = 0#128)
    (hmc : McF R c s Lk bk T.mem j Z U qv st) (hv4 : V3F c s T.mem qv (c.PF s U).length)
    (hcy : T.mem.readLE ((s.regs 4).toNat - 320) 8 = b) (hlt : b = 1 → (c.PF s U).length < c.u1)
    (k0 : ∀ X : State, X.rip = BitVec.ofNat 64 rJF6 → X.regs 4 = s.regs 4 - 392#64 → X.regs 5 = s.regs 4 - 8#64 →
      X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false → X.xmm 15 = 0#128 → X.mem = T.mem → b = 0 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q)
    (kW : ∀ Y : State, Y.rip = BitVec.ofNat 64 SubVW.entry → Y.regs 4 = s.regs 4 - 400#64 →
      Y.regs 5 = s.regs 4 - 8#64 → Y.regs 14 = s.regs 14 → Y.fsBase = s.fsBase → Y.df = false →
      Y.xmm 15 = 0#128 →
      Y.regs 0 = BitVec.ofNat 64 (c.up + 8 * (c.PF s U).length) →
      Y.regs 3 = BitVec.ofNat 64 (c.u1 - (c.PF s U).length) →
      Y.regs 1 = BitVec.ofNat 64 (c.uc - (c.PF s U).length) →
      Y.regs 7 = BitVec.ofNat 64 (c.up + 8 * (c.PF s U).length) →
      Y.regs 6 = BitVec.ofNat 64 (c.u1 - (c.PF s U).length) →
      Y.regs 8 = BitVec.ofNat 64 (c.uc - (c.PF s U).length) → Y.regs 9 = 1#64 →
      MemFrame T.mem Y.mem (isR s) → Y.mem.regions = T.mem.regions →
      Y.mem.readLE ((s.regs 4).toNat - 400) 8 = rFD5W → b = 1 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) Y Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hulc := hpre.ulc; have huc40 := hpre.uc40; have hv9 := hpre.v9.1
  have hu48 := hpre.ua.2.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hPl := PF_len_le2 (c := c) (s := s) (U := U) (by omega)
  have r1 := hv4.s144; have r2 := hmc.bd.sl.ul'; have r3 := hmc.bd.sl.s7; have r4 := hmc.bd.sl.s5
  have hgt : (BitVec.ofNat 64 c.u1 < BitVec.ofNat 64 (c.PF s U).length) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]
    rw [Nat.mod_eq_of_lt (show c.u1 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (c.PF s U).length < 2 ^ 64 by omega)]
    omega
  have e1 := bvS2 (a := (c.PF s U).length) (u := c.u1) (by omega) (by omega)
  have e2 := bvS2 (a := (c.PF s U).length) (u := c.uc) (by omega) (by omega)
  have hB : Box (McF R c s Lk bk T.mem j Z U qv st) := ⟨hmc⟩
  clear hmc hv4 hpre hcr
  rcases (by omega : b = 0 ∨ b = 1) with hb | hb
  · subst hb
    janus64_run [hcy] until [rJF6]
    refine k0 _ rfl ?sp ?r5 ?r14 hfs (by dsimp only) ?x15 rfl rfl
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    case sp => exact hsp
    case r5 => exact h5
    case r14 => exact h14
    case x15 => exact hx15
  · subst hb
    have hlt' := hlt rfl
    have e3 := bvM2 (q := c.up) (a := (c.PF s U).length) (x := c.uc)
      (by omega) (by omega) (by omega)
    janus64_run [hcy, r1, r2, r3, r4, hgt, e1, e2, e3] until [SubVW.entry]
    refine kW _ rfl ?wsp ?wr5 ?wr14 hfs (by dsimp only) ?wx15 ?a0 ?a3 ?a1 ?a7 ?a6 ?a8 ?a9
      (by unfold isR; janus_frame) (by janus64_simp) ?wra rfl
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    case wr5 => exact h5
    case wr14 => exact h14
    case wx15 => exact hx15
    case wra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
