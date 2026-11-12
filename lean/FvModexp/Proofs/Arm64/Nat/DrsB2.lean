import FvModexp.Proofs.Arm64.Nat.DrsRecP
import FvModexp.Proofs.Arm64.Nat.DrsRecQ
import FvModexp.Proofs.Common.MaskWord

/-!
# `divRecursiveStep` (arm64), loop body segment 2: the recursive call (natdiv.go:813)

`b2`: from `A1` (after `clear(qhat)`) → arguments `qhat0`, `stk`, `uu[s:B+n]`, `v[s:]`, `depth+1` → `CALL
divRecursiveStep` (the induction hypothesis, divisor length `n - B + 1 < n`) → its return `0x1ba614` (`A2`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem b2 (impl : List Segment) (R : RtInv) (c : Cx) (ih : ∀ a, IH impl R c.vl a)
    (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat)
    (hA : A1 R c s Lk bk S j Z U) (Q : State → Prop) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hcr := hA.cr
  obtain ⟨hce, -, -, -, -, huc, huc4, hvlc, hvc4, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, hu48, -, -, -⟩,
    ⟨-, hv48, -, -, -, -, hvc48⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl
  have hW := hcr.hW; have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have hj := hA.jB
  have hjm : j ≤ c.u1 - c.vl := by have := hA.li.2.2.2.2.2.2.2; omega
  have hsl := hA.bd.sl; have hbd := hA.bd
  have hpc := hA.pc; have hsp := hA.sp; have h28 := hA.r28; have h29 := hA.r29; have h18 := hA.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hA.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hB := lsr1 c.vl (by omega)
  have hB' : BitVec.ofNat 64 c.vl >>> 1 = BitVec.ofNat 64 (c.vl / 2) := by rw [← klsr1]; exact hB
  have r1 := hsl.q0p; have r2 := hsl.q0l; have r3 := hsl.q0c; have r4 := hsl.nn; have r5 := hbd.sj
  have r6 := hsl.ul'; have r7 := hsl.s7; have r8 := hbd.sup; have r9 := hbd.suc; have r10 := hsl.s5
  have r11 := hbd.sul; have r12 := hsl.bb; have r13 := hsl.s10; have r14 := hsl.s8; have r15 := hsl.s11
  have r16 := hsl.s4
  have bv : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 → (a + b < 2 ^ 64 → BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b)) ∧
      (b ≤ a → BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b)) := fun a b ha hb => by
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  have e1 := (bv (j - c.vl / 2) (c.vl / 2) (by omega) (by omega)).1 (by omega)
  rw [show j - c.vl / 2 + c.vl / 2 = j by omega] at e1
  have e2 := (bv c.uc j (by omega) (by omega)).2 (by omega)
  have e3 := (bv (c.uc - j) 1 (by omega) (by omega)).1 (by omega)
  have e4 := (bv (c.vl / 2) 1 (by omega) (by omega)).2 (by omega)
  have e5 := (bv c.vc (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have e6 := (bv (c.vc - c.vl / 2) 1 (by omega) (by omega)).1 (by omega)
  have e7 := (bv c.vl (c.vl / 2) (by omega) (by omega)).2 (by omega)
  have e8 := (bv (c.vl - c.vl / 2) 1 (by omega) (by omega)).1 (by omega)
  have e9 := (bv c.vl 1 (by omega) (by omega)).1 (by omega)
  have mk : ∀ x y : Nat, x < 2 ^ 64 → 0 < y → y < 2 ^ 63 →
      BitVec.ofNat 64 x &&& (0#64 - BitVec.ofNat 64 y).sshiftRight 63 = BitVec.ofNat 64 x := fun x y hx h0 hy => by
    rw [FvModexp.sshr63_allOnes _ (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega)]
    exact BitVec.and_allOnes
  have m1 := mk (c.vl / 2 - 1) (c.uc - j + 1) (by omega) (by omega) (by omega)
  have m2 := mk (c.vl / 2 - 1) (c.vc - c.vl / 2 + 1) (by omega) (by omega) (by omega)
  have sh : BitVec.ofNat 64 (c.vl / 2 - 1) <<< 3 = BitVec.ofNat 64 (8 * (c.vl / 2 - 1)) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  have a1 := (bv (c.up + 8 * (j - c.vl / 2)) (8 * (c.vl / 2 - 1)) (by omega) (by omega)).1 (by omega)
  rw [show c.up + 8 * (j - c.vl / 2) + 8 * (c.vl / 2 - 1) = c.up + 8 * (j - 1) by omega] at a1
  have a2 := (bv c.vp (8 * (c.vl / 2 - 1)) (by omega) (by omega)).1 (by omega)
  janus_run [hB', e1, e2, e3, e4, e5, e6, e7, e8, e9, m1, m2, sh, a1, a2, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16] until [0x1ba3a0]
  -- WIP (s22): call the IH here (see NOTES-asm s22 handover)
  sorry

end FvModexp.Arm64.DivRec
