import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsD5
import FvModexp.Proofs.Arm64.NatQ.DrsC6
import FvModexp.Proofs.Common.MaskWord

/-! (Q-form copy of Arm64/Nat/DrsD6R.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), end of a loop iteration: to `CALL addTo(z[j-B:], qhat)` (natdiv.go:851)

`d6r`: from `0x1ba8d4` (`Mc` at `Cx.stG`) → `z[j-B:]` bounds check (`BCC` panic excluded: `j - B ≤ len z`; the
`cap = 0` pointer mask is all ones) → the `CALL addTo` state (`0x1ba90c`, return `0x1ba910`). No stores.
-/

set_option autoImplicit false
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
set_option linter.janusRenameI false
namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

theorem bvS1 {b u : Nat} (h : b ≤ u) (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u - BitVec.ofNat 64 b = BitVec.ofNat 64 (u - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem bvM1 {q a x : Nat} (h : a < x) (hx : x < 2 ^ 63) (hq : q + 8 * a < 2 ^ 64) :
    BitVec.ofNat 64 q + (BitVec.ofNat 64 a &&& (BitVec.ofNat 64 a - BitVec.ofNat 64 x).sshiftRight 63) <<< 3 =
      BitVec.ofNat 64 (q + 8 * a) := by
  rw [FvModexp.sshr63_allOnes _ (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega), BitVec.and_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d6r (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rD5) (hsp : T.sp = s.sp - 400#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 408#64) (h18 : T.regs 18 = s.regs 18)
    (hmc : Mc R c s Lk bk T.mem j Z U qv (c.stG s j U))
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 addToA → X.regs 30 = BitVec.ofNat 64 rD6 →
      X.regs 0 = BitVec.ofNat 64 (c.qp + 8 * (j - c.vl / 2)) → X.regs 1 = BitVec.ofNat 64 (c.ql - (j - c.vl / 2)) →
      X.regs 2 = BitVec.ofNat 64 (c.qc - (j - c.vl / 2)) → X.regs 3 = BitVec.ofNat 64 c.t0 →
      X.regs 4 = BitVec.ofNat 64 (c.q0 s j U).length → X.regs 5 = BitVec.ofNat 64 (c.vl / 2 + 1) →
      X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 →
      X.mem = T.mem → ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
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
  have hroom := (room hcr).1
  have hjB := hmc.jB
  have hqlc := hcr.pre.2.2.2.1
  have hqc40 := hcr.pre.2.2.2.2.1
  have hle' : BitVec.ofNat 64 (j - c.vl / 2) ≤ BitVec.ofNat 64 c.ql := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  have r1 := hmc.bd.sl.s1; have r2 := hmc.bd.sl.s2; have r3 := hmc.bd.sl.s3; have r4 := hmc.bd.sj
  have r5 := hmc.bd.sl.q0p; have r6 := hmc.q3.s208; have r7 := hmc.bd.sl.q0c
  have hq48 := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have e1 := bvS1 (b := j - c.vl / 2) (u := c.ql) (by omega) (by omega)
  have e2 := bvS1 (b := j - c.vl / 2) (u := c.qc) (by omega) (by omega)
  have e3 := bvM1 (q := c.qp) (a := j - c.vl / 2) (x := c.qc) (by omega) (by omega) (by omega)
  have hB : Box (Mc R c s Lk bk T.mem j Z U qv (c.stG s j U)) := ⟨hmc⟩
  clear hmc
  janus_run [r1, r2, r3, r4, r5, r6, r7] until [addToA]
  refine k _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ rfl
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  all_goals first | exact h28 | exact h29 | exact h18 | exact e3 | exact e1 | exact e2
end FvModexp.Arm64.Q.DivRec
