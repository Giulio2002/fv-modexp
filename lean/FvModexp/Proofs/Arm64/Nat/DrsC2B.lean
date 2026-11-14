import FvModexp.Proofs.Arm64.Nat.DrsSegD
import FvModexp.Proofs.Arm64.Nat.SubVW
/-!
# `divRecursiveStep` (arm64), correction loop: `if e <= 0 { break }` (natdiv.go:834)
`c2b`: from `nat.cmp`'s return (`0x1ba74c`, `X0 = ofInt (cmpQ |P| st)`): `e ≤ 0` → `0x1bad74` (reload `qhatv`) → the
exit `E` (`0x1ba80c`, the state is final by `C.brk`); `e > 0` → the loads of `qhat` → `CALL subVW(qhat, qhat, 1)`
(`0x1ba770`) with `Bx` (base state = the head's).
-/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
set_option linter.janusRenameI false
namespace FvModexp.Arm64.DivRec
/-- `subVW(qhat, qhat, 1)`'s return address -/
abbrev rW1 : Nat := 0x1ba774

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the break test** after the loop's `nat.cmp` -/
theorem c2b (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (st : Mdl.St) (Q : State → Prop)
    (hi : i < 2) (hinv : Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length (2 - i) st =
      Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length 2 (c.st0 s j U))
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rC1) (hsp : T.sp = s.sp - 400#64) (h28 : T.regs 28 = s.regs 28)
    (h29 : T.regs 29 = s.sp - 408#64) (h18 : T.regs 18 = s.regs 18)
    (h0 : T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.P s j U).length st))
    (hmc : Mc R c s Lk bk T.mem j Z U qv st) (hv4 : V4 c s T.mem qv (c.P s j U).length)
    (hsi : T.mem.readLE (s.sp.toNat - 160) 8 = i)
    (kE : ∀ S', E R c s Lk bk S' j Z U qv → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q)
    (kY : ∀ Y : State, Y.pc = BitVec.ofNat 64 SubVW.entry → Y.regs 30 = BitVec.ofNat 64 rW1 →
      Y.regs 0 = BitVec.ofNat 64 c.t0 → Y.regs 1 = BitVec.ofNat 64 (c.q0 s j U).length →
      Y.regs 2 = BitVec.ofNat 64 (c.vl / 2 + 1) → Y.regs 3 = BitVec.ofNat 64 c.t0 →
      Y.regs 4 = BitVec.ofNat 64 (c.q0 s j U).length → Y.regs 5 = BitVec.ofNat 64 (c.vl / 2 + 1) →
      Y.regs 6 = 1#64 → Bx R c s Lk bk Y j Z U qv i st st →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) Y Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hB : Box (Mc R c s Lk bk T.mem j Z U qv st) := ⟨hmc⟩
  have hB4 : Box (V4 c s T.mem qv (c.P s j U).length) := ⟨hv4⟩
  have r1 := hv4.s328; have r2 := hv4.s152; have r3 := hv4.s168
  have r4 := hmc.bd.sl.q0p; have r5 := hmc.q3.s208; have r6 := hmc.bd.sl.q0c
  rcases natCmp_range (st.buf.take (c.P s j U).length) (Mdl.norm st.w) with he | he | he
  · -- e = -1: break
    have hle : Mdl.cmpQ (c.P s j U).length st ≤ 0 := by show Mdl.natCmp _ _ ≤ 0; rw [he]; decide
    have h0' : T.regs 0 = 18446744073709551615#64 := by rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [he]; rfl
    have hfin := C.brk hi hle hinv
    clear hmc hv4 h0 kY
    janus_run [r1, r2, r3, h0'] until [cExit]
    refine kE _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hfin ▸ hB.1, hB4.1⟩
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h28
    · exact h29
    · exact h18
  · -- e = 0: break
    have hle : Mdl.cmpQ (c.P s j U).length st ≤ 0 := by show Mdl.natCmp _ _ ≤ 0; rw [he]; decide
    have h0' : T.regs 0 = 0#64 := by rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [he]; rfl
    have hfin := C.brk hi hle hinv
    clear hmc hv4 h0 kY
    janus_run [r1, r2, r3, h0'] until [cExit]
    refine kE _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hfin ▸ hB.1, hB4.1⟩
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h28
    · exact h29
    · exact h18
  · -- e = 1: correct
    have hpos : 0 < Mdl.cmpQ (c.P s j U).length st := by show 0 < Mdl.natCmp _ _; rw [he]; decide
    have h0' : T.regs 0 = 1#64 := by rw [h0]; show BitVec.ofInt 64 (Mdl.natCmp _ _) = _; rw [he]; rfl
    clear hmc hv4 h0 kE
    janus_run [r4, r5, r6, h0'] until [SubVW.entry]
    refine kY _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨rfl, ?_, ?_, ?_, hB.1, hB4.1, hsi, hi, hpos, hinv⟩
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h28
    · exact h29
    · exact h18

end FvModexp.Arm64.DivRec
