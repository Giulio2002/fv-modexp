import FvModexp.Proofs.Amd64.Nat.DivBigRel
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `nat.div` (amd64), `u ≥ v` (`len v ≥ 2`): from `AtC` (`cmp ≥ 0`, `stk ≠ nil`) to `divLarge`'s entry (natdiv.go:538-543)

Port of `Arm64/Nat/DivBig.lean` (`big1`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem big1 (impl : List Amd64.Segment) {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State} {S : State}
    (hS : AtC zp zl zc st z2 z2l z2c u ul uc v vl vc s S) (c : Nat) (hc : c ≤ 1)
    (hr0 : S.regs 0 = BitVec.ofNat 64 c) (hst : st ≠ 0)
    (hb' : 41512 ≤ (s.regs 4).toNat) (ha : (s.regs 4).toNat + 112 ≤ 2 ^ 48)
    (hw : s.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true) (Q : State → Prop)
    (k : ∀ X, AtL zp zl zc st z2 z2l z2c u ul uc v vl vc s X →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) S Q := by
  have hpc := hS.pc; have hsp := hS.sp; have h5 := hS.r5; have h14 := hS.r14; have hfs := hS.fs
  have hx15 := hS.x15; have hdf := hS.df
  have hSacc : S.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
    rw [hS.mf.accessible]; exact hw
  have m0 := hS.ra; have mb := hS.bp
  have m1 := hS.s1; have m2 := hS.s2; have m3 := hS.s3; have m4 := hS.s4; have m5 := hS.s5; have m6 := hS.s6
  have m7 := hS.s7; have m8 := hS.s8; have m9 := hS.s9; have m10 := hS.s10; have m11 := hS.s11; have m12 := hS.s12
  have m13 := hS.s13
  have hmf := hS.mf; have hreg := hS.reg
  have hst64 : st < 2 ^ 64 := by rw [← m4]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l8 : u < 2 ^ 64 := by rw [← m8]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l9 : ul < 2 ^ 64 := by rw [← m9]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l10 : uc < 2 ^ 64 := by rw [← m10]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l11 : v < 2 ^ 64 := by rw [← m11]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l12 : vl < 2 ^ 64 := by rw [← m12]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have l13 : vc < 2 ^ 64 := by rw [← m13]; exact Janus.Arm64.Memory.readLE_lt _ _ _
  have hst' : (BitVec.ofNat 64 st = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hc' : (c = 0 ∨ c = 1) := by omega
  clear hS
  rcases hc' with rfl | rfl
  all_goals janus64_run [hr0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, hst', BitVec.msb_eq_decide]
    until [divLE]
  all_goals
    refine k _
      { pc := rfl, sp := ?_, r5 := ?_, r14 := ?_, fs := hfs, x15 := hx15, df := ?_, a0 := ?_, a3 := ?_, a1 := ?_,
        a7 := ?_, a6 := ?_, a8 := ?_, a9 := ?_, rc := ?rc
        mf := hmf.trans (by janus_frame : MemFrame S.mem _ [((s.regs 4).toNat - 240, (s.regs 4).toNat - 184),
            ((s.regs 4).toNat - 122, (s.regs 4).toNat - 121)])
          fun a n h => ⟨h, by simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
        reg := ?reg, ra := ?ra, bp := ?bp, by0 := ?by0, i0 := ?i0, i1 := ?i1, i2 := ?i2, i3 := ?i3, i4 := ?i4,
        i5 := ?i5 }
    case reg => simp only [Janus.Arm64.Memory.regions_writeLE]; exact hreg
    case rc =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
        m0, mb]
    case ra =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
        m0, mb]
    case bp =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
        m0, mb]
    case by0 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
        m0, mb]
    case i0 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
        m8, m9, m10, m11, m12, m13]
      exact Nat.mod_eq_of_lt l8
    case i1 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
        m8, m9, m10, m11, m12, m13]
      exact Nat.mod_eq_of_lt l9
    case i2 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
        m8, m9, m10, m11, m12, m13]
      exact Nat.mod_eq_of_lt l10
    case i3 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
        m8, m9, m10, m11, m12, m13]
      exact Nat.mod_eq_of_lt l11
    case i4 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
        m8, m9, m10, m11, m12, m13]
      exact Nat.mod_eq_of_lt l12
    case i5 =>
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, FvModexp.Expmc.readLE_writeLE_same,
        m8, m9, m10, m11, m12, m13]
      exact Nat.mod_eq_of_lt l13
    all_goals janus64_simp

end FvModexp.Amd64.NatDiv
