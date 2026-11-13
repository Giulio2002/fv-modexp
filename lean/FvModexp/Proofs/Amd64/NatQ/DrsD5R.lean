import FvModexp.Proofs.Amd64.NatQ.DrsD4
import FvModexp.Proofs.Amd64.NatQ.DrsC5R
import FvModexp.Proofs.Common.MaskWord

set_option autoImplicit false

/-! (amd64 twin (asm s51) of Arm64/NatQ/DrsD5R.lean)
# `divRecursiveStep` (amd64), after the correction loop: `if c > 0 { subVW(uu[ql:], uu[ql:], 1) }` test (natdiv.go:848-849)

`d5r`: from `0x5effe6` (`rD5`, the borrow `b ≤ 1` at `r - 320`): `MOVQ 0x48(SP), R9; TESTQ R9, R9; JBE 0x5f003f`.
* `b = 0`: the join `0x5f003f` (`rJ6`) with the memory unchanged.
* `b = 1`: `CMPQ DX, SI; JA` (`ql ≤ len uu`), `DI = uuP + (mask & 8 ql)`, `CALL subVW` (`0x5f003a`, return `0x5f003f`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the join after `subVW(uu[ql:], uu[ql:], 1)` (natdiv.go:851) -/
abbrev rJ6 : Nat := 0x5f003f

theorem bvS2 {a u : Nat} (h : a ≤ u) (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u - BitVec.ofNat 64 a = BitVec.ofNat 64 (u - a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem bvM2 {q a x : Nat} (h : a < x) (hx : x < 2 ^ 63) (hq : q + 8 * a < 2 ^ 64) :
    BitVec.ofNat 64 q + ((0#64 - BitVec.ofNat 64 (x - a)).sshiftRight 63 &&& BitVec.ofNat 64 a <<< 3) =
      BitVec.ofNat 64 (q + 8 * a) := by
  have hsh : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft]; simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  rw [hsh]
  exact bvM (by omega) (by omega) (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d5r (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (st : Mdl.St) (Q : State → Prop) (b : Nat) (hb1 : b ≤ 1)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rD5) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false) (hx15 : T.xmm 15 = 0#128)
    (hmc : Mc R c s Lk bk T.mem j Z U qv st) (hv4 : V4 c s T.mem qv (c.P s j U).length)
    (hcy : T.mem.readLE ((s.regs 4).toNat - 320) 8 = b)
    (k0 : ∀ X : State, X.rip = BitVec.ofNat 64 rJ6 → X.regs 4 = s.regs 4 - 392#64 → X.regs 5 = s.regs 4 - 8#64 →
      X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false → X.xmm 15 = 0#128 → X.mem = T.mem → b = 0 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q)
    (kW : ∀ Y : State, Y.rip = BitVec.ofNat 64 SubVW.entry → Y.regs 4 = s.regs 4 - 400#64 →
      Y.regs 5 = s.regs 4 - 8#64 → Y.regs 14 = s.regs 14 → Y.fsBase = s.fsBase → Y.df = false →
      Y.xmm 15 = 0#128 →
      Y.regs 0 = BitVec.ofNat 64 (c.uuP j + 8 * (c.P s j U).length) →
      Y.regs 3 = BitVec.ofNat 64 (c.uuL j - (c.P s j U).length) →
      Y.regs 1 = BitVec.ofNat 64 (c.uuC j - (c.P s j U).length) →
      Y.regs 7 = BitVec.ofNat 64 (c.uuP j + 8 * (c.P s j U).length) →
      Y.regs 6 = BitVec.ofNat 64 (c.uuL j - (c.P s j U).length) →
      Y.regs 8 = BitVec.ofNat 64 (c.uuC j - (c.P s j U).length) → Y.regs 9 = 1#64 →
      MemFrame T.mem Y.mem (isR s) → Y.mem.regions = T.mem.regions →
      Y.mem.readLE ((s.regs 4).toNat - 400) 8 = rJ6 → b = 1 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) Y Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hulc := hpre.ulc; have huc40 := hpre.uc40; have hv9 := hpre.v9.1
  have hu48 := hpre.ua.2.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hPl := P_len_le2 (c := c) (s := s) (j := j) (U := U) (by omega)
  have r1 := hv4.s152; have r2 := hmc.bd.sul; have r3 := hmc.bd.suc; have r4 := hmc.bd.sup
  have hgt : (BitVec.ofNat 64 (c.uuL j) < BitVec.ofNat 64 (c.P s j U).length) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]
    rw [Nat.mod_eq_of_lt (show c.uuL j < 2 ^ 64 by simp only [Cx.uuL]; omega),
      Nat.mod_eq_of_lt (show (c.P s j U).length < 2 ^ 64 by omega)]
    simp only [Cx.uuL]; omega
  have e1 := bvS2 (a := (c.P s j U).length) (u := c.u1 - (j - c.vl / 2)) (by omega) (by omega)
  have e2 := bvS2 (a := (c.P s j U).length) (u := c.uc - (j - c.vl / 2)) (by omega) (by omega)
  have e3 := bvM2 (q := c.up + 8 * (j - c.vl / 2)) (a := (c.P s j U).length) (x := c.uc - (j - c.vl / 2))
    (by omega) (by omega) (by omega)
  have hB : Box (Mc R c s Lk bk T.mem j Z U qv st) := ⟨hmc⟩
  clear hmc hv4 hpre hcr
  rcases (by omega : b = 0 ∨ b = 1) with hb | hb
  · subst hb
    janus64_run [hcy] until [rJ6]
    refine k0 _ rfl ?sp ?r5 ?r14 hfs (by dsimp only) ?x15 rfl rfl
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    case sp => exact hsp
    case r5 => exact h5
    case r14 => exact h14
    case x15 => exact hx15
  · subst hb
    janus64_run [hcy, r1, r2, r3, r4, hgt, e1, e2, e3] until [SubVW.entry]
    refine kW _ rfl ?wsp ?wr5 ?wr14 hfs (by dsimp only) ?wx15 ?a0 ?a3 ?a1 ?a7 ?a6 ?a8 ?a9
      (by unfold isR; janus_frame) (by janus64_simp) ?wra rfl
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    case wr5 => exact h5
    case wr14 => exact h14
    case wx15 => exact hx15
    case wra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
