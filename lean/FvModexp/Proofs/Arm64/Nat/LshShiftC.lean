import FvModexp.Proofs.Arm64.Nat.LshShiftF

/-! # `nat.lsh` (arm64): shift path from `CALL lshVU.abi0` (`+0x204`) to the clear point -/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Lsh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from `CALL lshVU.abi0` (state `C`) to the clear point, then `fromClr` -/
theorem shiftC (impl : List Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibLsh.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hmc : MemclrNoHeapPointersLive (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M) (hr0 : sh % 64 ≠ 0)
    (C : State) (hpc : C.pc = BitVec.ofNat 64 callLsh) (hsp : C.sp = s.sp - 160#64) (h28 : C.regs 28 = s.regs 28)
    (h29 : C.regs 29 = s.sp - 168#64) (h18 : C.regs 18 = s.regs 18)
    (hF : MemFrame M C.mem [(s.sp.toNat - 152, s.sp.toNat - 96), (s.sp.toNat - 80, s.sp.toNat - 72),
      (s.sp.toNat - 32, s.sp.toNat - 16)])
    (k1 : C.mem.readLE (s.sp.toNat - 160 + 8) 8 = p + 8 * (sh / 64))
    (k2 : C.mem.readLE (s.sp.toNat - 160 + 16) 8 = xl)
    (k3 : C.mem.readLE (s.sp.toNat - 160 + 32) 8 = x)
    (k4 : C.mem.readLE (s.sp.toNat - 160 + 56) 8 = sh % 64)
    (k5 : C.mem.readLE (s.sp.toNat - 24) 8 = p) (k6 : C.mem.readLE (s.sp.toNat - 80) 8 = c)
    (k7 : C.mem.readLE (s.sp.toNat - 32) 8 = sh / 64)
    (hinvC : R.inv b' L' (s.regs 28).toNat (view R.rt L' C.mem)) :
    ReachesRet (LibLsh.program.link impl) (s.regs 30) C fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hn16 := h.n16; have hxl0 := h.xl0; have hal := h.al; have hx48 := h.x48
  have hwrt := h.wrt; have hpw := h.pw; have hgw := h.gw; have hpg := h.pg
  have hxw := h.xw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  simp only [need] at hcap hn16
  unfold Apart at hpw hgw hpg
  have rC : ∀ a, (s.sp.toNat - 72 ≤ a ∧ a + 8 ≤ s.sp.toNat - 32) ∨ (s.sp.toNat - 16 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) →
      C.mem.readLE a 8 = M.readLE a 8 := fun a ha =>
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have k8 : C.mem.readLE (s.sp.toNat - 40) 8 = xl + sh / 64 := (rC _ (by omega)).trans h.sn
  have k9 : C.mem.readLE (s.sp.toNat - 48) 8 = xl + sh / 64 + 1 := by
    rw [rC _ (by omega)]; have := h.sn1; simp only [need] at this; exact this
  have k10 : C.mem.readLE (s.sp.toNat + 56) 8 = sh := (rC _ (by omega)).trans h.ssh
  have hzacc : C.mem.accessible (p + 8 * (sh / 64)) (8 * xl) true = true := by
    rw [hF.accessible]; exact Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hxacc : C.mem.accessible x (8 * xl) false = true := by rw [hF.accessible]; exact h.xacc
  have hsacc : C.mem.accessible (s.sp.toNat - 4256) (4256 + 64) true = true := by rw [hF.accessible]; exact h.sacc
  have hzH : Held R L' (p + 8 * (sh / 64)) (8 * xl) := h.pheld.sub (by omega) (by omega)
  have hro : Outside (s.sp.toNat - 160 + 64) 8 R.rt := hwrt.of_sub (by omega) (by omega)
  have hzg : Apart (p + 8 * (sh / 64)) (8 * xl) ((s.regs 28).toNat + 16) 8 := by unfold Apart; omega
  have hrg : Apart (s.sp.toNat - 160 + 64) 8 ((s.regs 28).toNat + 16) 8 := by unfold Apart; omega
  have hzr : Apart (p + 8 * (sh / 64)) (8 * xl) (s.sp.toNat - 160 + 64) 8 := by unfold Apart; omega
  have hxr : Apart x (8 * xl) (s.sp.toNat - 160 + 64) 8 := by unfold Apart; omega
  have halx : x ≤ p + 8 * (sh / 64) ∨ Apart (p + 8 * (sh / 64)) (8 * xl) x (8 * xl) := by
    rcases h.px with e | e
    · left; omega
    · right; unfold Apart at e ⊢; omega
  have hr1 : 1 ≤ sh % 64 := by omega
  have hr63 : sh % 64 ≤ 63 := by omega
  janus_run [k1, k2, k3, k4] until [callLsh + 4] calls [hLsh b' L']
  rename_i w hq hinvw _
  have e160 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold LshVUSum.Q at hq
  rw [e160, k1, k2, k3, k4] at hq
  obtain ⟨q1, q2, q3⟩ := hq
  dsimp only at q1 q2 q3
  have e96 : s.sp.toNat - 160 + 64 = s.sp.toNat - 96 := by omega
  have e88 : s.sp.toNat - 160 + 72 = s.sp.toNat - 88 := by omega
  try rw [e96] at q2
  try rw [e96] at q3
  try rw [e88] at q3
  obtain ⟨hF1, hLF1, hinv2, hval⟩ := shift_facts h hF q1 q2 q3 hinvw
  have rw' : ∀ a, (s.sp.toNat - 88 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) → w.readLE a 8 = C.mem.readLE a 8 := fun a ha =>
    q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have w5 := (rw' _ (by omega)).trans k5
  have w6 := (rw' _ (by omega)).trans k6
  have w7 := (rw' _ (by omega)).trans k7
  have w8 := (rw' _ (by omega)).trans k8
  have w9 := (rw' _ (by omega)).trans k9
  have w10 := (rw' _ (by omega)).trans k10
  have hwacc : w.accessible (p + 8 * (xl + sh / 64)) 8 true = true := by
    rw [q3.accessible, hF.accessible]; exact Memory.accessible_mono _ h.pacc (by omega) (by omega)
  have hsacc' : w.accessible (s.sp.toNat - 4256) (4256 + 64) true = true := by rw [q3.accessible]; exact hsacc
  have q2' : w.readLE (s.sp.toNat - 96) 8 = natVal C.mem x xl * 2 ^ (sh % 64) / 2 ^ (64 * xl) := q2
  rw [← q2'] at hF1 hLF1 hinv2 hval
  janus_run [w5, w6, w7, w8, w9, w10, mod64_of_lt (p + 8 * (xl + sh / 64)) (by omega)] until [hClr]
  refine fromClr impl R hmc b L zp zc x xl sh s p c L' b' M h _ hF1 hLF1 hinv2 hval ?_ ?_ ?_ _ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_
  · exact (Memory.readLE_writeLE_of_disjoint (m := w) _ (by omega)).trans w5
  · exact (Memory.readLE_writeLE_of_disjoint (m := w) _ (by omega)).trans w9
  · exact (Memory.readLE_writeLE_of_disjoint (m := w) _ (by omega)).trans w6
  all_goals try janus_simp
  all_goals (congr 1; omega)


end FvModexp.Arm64.Lsh
