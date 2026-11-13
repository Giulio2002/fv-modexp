import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsDG

/-! (Q-form copy of Arm64/Nat/DrsD7.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), end of a loop iteration: `j -= B; stk.restore(mark)` → the loop head (natdiv.go:852-853)

`d7`: from `G` at `0x1ba910`: `mark ≤ cap` (`BCS`; the `panicBounds` is excluded), the header store `len := mark`
(`0x1ba4f0`), the reloads of `qhat0` and `j - B` → the loop head `H (j - B)` (`0x1ba504`) on the quotient / dividend
`Cx.BS` (`li_next`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

theorem bud_next {lo K bk j B X : Nat} (hB : 0 < B) (hj : B < j) (h : lo + (j / B) * K + X ≤ bk) :
    lo + ((j - B) / B + 1) * K + X ≤ bk := by
  have e : j / B = (j - B) / B + 1 := by rw [← Nat.add_div_right _ hB, Nat.sub_add_cancel (by omega)]
  rw [← e]; exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem d7 (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (Q : State → Prop) (S : State) (hpc : S.pc = BitVec.ofNat 64 rD6)
    (hG : G R c s Lk bk S j Z U)
    (k : ∀ S', H R c s Lk bk S' (j - c.vl / 2) → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hcr := hG.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, -, -, -, -, -, -, -, ⟨hqs, -⟩, ⟨hus, -⟩, ⟨hvs, -⟩,
    -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hsto : Outside c.st 24 (win s c.W 96) := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hsp := hG.sp; have h28 := hG.r28; have h29 := hG.r29; have h18 := hG.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hG.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hlc := hG.ev.sok.2.2.2.2.2.1
  have hlen := hG.fp.len
  have hc40 := hG.ev.sok.2.2.2.2.2.2
  have hst48 := hG.ev.sok.2.2.2.1
  have hsta := hG.ev.sok.2.2.1
  have hl1 : c.l1 s ≤ stCap S.mem c.st := by simp only [Cx.l1, StackNat.rnd] at hlen hlc ⊢; omega
  have hl64 : c.l1 s < 2 ^ 64 := by omega
  obtain ⟨K, hK⟩ : ∃ K, S.mem.readLE (c.st + 16) 8 = K := ⟨_, rfl⟩
  have hK' : stCap S.mem c.st = K := hK
  have hKb : BitVec.ofNat 64 (c.l1 s) ≤ BitVec.ofNat 64 K := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64,
      Nat.mod_eq_of_lt (by omega)]; omega
  have r1 := hG.sl.s4; have r2 := hG.mrk; have r3 := hG.sl.q0p; have r4 := hG.sl.q0l; have r5 := hG.sl.q0c
  have r6 := hG.sj
  have hB : Box (G R c s Lk bk S j Z U) := ⟨hG⟩
  clear hG
  have hsto' := hsto
  simp only [win, outside_cons, outside_nil, and_true] at hsto'
  janus_run [r1, r2, r3, r4, r5, r6, hK] until [head]
  -- the state after the store
  have hG := hB.1
  have hF : MemFrame S.mem (S.mem.writeLE (c.st + 8) 8 (c.l1 s)) [(c.st + 8, c.st + 16)] :=
    MemFrame.of_writeLE _ _ (List.mem_singleton.2 rfl) (Nat.le_refl _) (Nat.le_refl _)
  have rd : ∀ x n, Apart x n c.st 24 → (S.mem.writeLE (c.st + 8) 8 (c.l1 s)).readLE x n = S.mem.readLE x n :=
    fun x n h => Memory.readLE_writeLE_of_disjoint _ _ (by unfold Apart at h; omega)
  have hfo : FixOut s [(c.st + 8, c.st + 16)] := by
    simp only [FixOut, win, outside_cons, outside_nil, and_true] at hsto ⊢; omega
  have hli := li_next hcr hG.li hG.jB
  rw [← hG.zk, ← hG.uk] at hli
  have kz : Asm.limbs (S.mem.writeLE (c.st + 8) 8 (c.l1 s)) c.qp c.ql = Asm.limbs S.mem c.qp c.ql :=
    limbs_congr (rd _ _ hqs)
  have ku : Asm.limbs (S.mem.writeLE (c.st + 8) 8 (c.l1 s)) c.up c.u1 = Asm.limbs S.mem c.up c.u1 :=
    limbs_congr (rd _ _ (apS hus (Nat.le_refl _) (by have := hcr.u1ul; omega)))
  have eCw : stCap (S.mem.writeLE (c.st + 8) 8 (c.l1 s)) c.st = stCap S.mem c.st :=
    Memory.readLE_writeLE_of_disjoint _ _ (Or.inr (by omega))
  refine k _ ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcr, Ev.restore hG.ev _ hl1 hl64, Fp.restore hG.fl hl64,
    hG.sl.frame hF hfo, by rw [kz, ku]; exact hli, by rw [rd _ _ hvs]; exact hG.vk,
    by rw [rd _ _ (apS hus (by omega) (by have := hcr.u1ul; omega))]; exact hG.utl,
    bud_cap eCw (bud_next (by omega) hG.jB hG.bud)⟩
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28
  · exact h29
  · exact h18

end FvModexp.Arm64.Q.DivRec
