import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsD4
import FvModexp.Proofs.Common.MaskWord

/-! (Q-form copy of Arm64/Nat/DrsD5R.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), after the correction loop: `if c > 0 { subVW(uu[ql:], uu[ql:], c) }` test (natdiv.go:848-849)

`d5r`: from `subVV.abi0`'s return (`0x1ba884`): borrow `0` → `0x1ba8d4` (the `addTo(z[j-B:], qhat)` preparation);
borrow `1` → `uu[len(qhatv):]` (bounds check `BHI` excluded; the `cap = 0` pointer mask is all ones) → the
`CALL subVW(uu[ql:], uu[ql:], 1)` state (`0x1ba8d0`, return `0x1ba8d4`). No stores.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

/-- the return address of the borrow `subVW` (and the `addTo` preparation) -/
abbrev rD5 : Nat := 0x1ba8d4

theorem bvS2 {a b u : Nat} (h : a + b ≤ u) (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u - (BitVec.ofNat 64 a + BitVec.ofNat 64 b) = BitVec.ofNat 64 (u - b - a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem bvM2 {q a b x : Nat} (h : a + b < x) (hx : x < 2 ^ 63) (hq : q + 8 * a < 2 ^ 64) :
    BitVec.ofNat 64 q + (BitVec.ofNat 64 a &&& (BitVec.ofNat 64 a + BitVec.ofNat 64 b - BitVec.ofNat 64 x).sshiftRight 63)
      <<< 3 = BitVec.ofNat 64 (q + 8 * a) := by
  rw [FvModexp.sshr63_allOnes _ (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega),
    BitVec.and_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d5r (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (st : Mdl.St) (Q : State → Prop) (b : Nat) (hb1 : b ≤ 1)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 0x1ba884) (hsp : T.sp = s.sp - 400#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 408#64) (h18 : T.regs 18 = s.regs 18)
    (hmc : Mc R c s Lk bk T.mem j Z U qv st) (hv4 : V4 c s T.mem qv (c.P s j U).length) (hcy : T.mem.readLE (s.sp.toNat - 320) 8 = b)
    (k0 : ∀ X : State, X.pc = BitVec.ofNat 64 rD5 → X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 →
      X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 → X.mem = T.mem → b = 0 →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q)
    (kW : ∀ Y : State, Y.pc = BitVec.ofNat 64 SubVW.entry → Y.regs 30 = BitVec.ofNat 64 rD5 →
      Y.sp = s.sp - 400#64 → Y.regs 28 = s.regs 28 → Y.regs 29 = s.sp - 408#64 → Y.regs 18 = s.regs 18 →
      Y.regs 0 = BitVec.ofNat 64 (c.uuP j + 8 * (c.P s j U).length) →
      Y.regs 1 = BitVec.ofNat 64 (c.uuL j - (c.P s j U).length) →
      Y.regs 2 = BitVec.ofNat 64 (c.uuC j - (c.P s j U).length) →
      Y.regs 3 = BitVec.ofNat 64 (c.uuP j + 8 * (c.P s j U).length) →
      Y.regs 4 = BitVec.ofNat 64 (c.uuL j - (c.P s j U).length) →
      Y.regs 5 = BitVec.ofNat 64 (c.uuC j - (c.P s j U).length) → Y.regs 6 = 1#64 → Y.mem = T.mem → b = 1 →
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
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have hu1 := hcr.u1ul
  have hPl := P_len_le2 (c := c) (s := s) (j := j) (U := U) (by omega)
  have hle' : BitVec.ofNat 64 (c.P s j U).length ≤ BitVec.ofNat 64 (c.u1 - (j - c.vl / 2)) := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  have r1 := hmc.bd.sl.ul'; have r2 := hmc.bd.sul; have r3 := hmc.bd.sj; have r4 := hmc.bd.sl.s7
  have r5 := hmc.bd.sup; have r6 := hv4.s152
  have e1 := bvS2 (a := (c.P s j U).length) (b := j - c.vl / 2) (u := c.u1) (by omega) (by omega)
  have e2 := bvS2 (a := (c.P s j U).length) (b := j - c.vl / 2) (u := c.uc) (by omega) (by omega)
  have e3 := bvM2 (q := c.up + 8 * (j - c.vl / 2)) (a := (c.P s j U).length) (b := j - c.vl / 2) (x := c.uc)
    (by omega) (by omega) (by omega)
  have hB : Box (Mc R c s Lk bk T.mem j Z U qv st) := ⟨hmc⟩
  clear hmc hv4
  rcases (by omega : b = 0 ∨ b = 1) with hb | hb
  · subst hb
    janus_run [hcy] until [rD5]
    refine k0 _ rfl rfl ?_ ?_ ?_ rfl rfl
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h28
    · exact h29
    · exact h18
  · subst hb
    janus_run [hcy, r1, r2, r3, r4, r5, r6] until [SubVW.entry]
    refine kW _ rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals first | exact h28 | exact h29 | exact h18 | exact e3 | exact e1 | exact e2 | rfl
end FvModexp.Arm64.Q.DivRec
