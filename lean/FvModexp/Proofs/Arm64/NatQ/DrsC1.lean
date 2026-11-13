import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsCE
import FvModexp.Proofs.Arm64.Nat.DrsNorm

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DrsC1.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), correction loop: the head (natdiv.go:832-833)

`c1`: from the head `C` (`0x1ba700`): `i = 2` → the exit `E` (`0x1ba80c`); otherwise `uu.norm()` (`norm4`, nat.go:51),
the `len ≤ cap` check (`BHI` panic excluded), the spill of `i` (`SP'+240`) → `CALL nat.cmp(qhatv, uu.norm())` (`0x1ba748`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

/-- `nat.cmp`'s entry -/
abbrev cmpA : Nat := 1782608

/-- the return address of the loop's `nat.cmp` -/
abbrev rC1 : Nat := 0x1ba74c

/-- `uu`'s pointer / length / capacity in iteration `j` -/
@[reducible] def Cx.uuP (c : Cx) (j : Nat) : Nat := c.up + 8 * (j - c.vl / 2)
@[reducible] def Cx.uuL (c : Cx) (j : Nat) : Nat := c.u1 - (j - c.vl / 2)
@[reducible] def Cx.uuC (c : Cx) (j : Nat) : Nat := c.uc - (j - c.vl / 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from `norm4`'s exit to the `CALL nat.cmp` -/
theorem c1x (impl : List Segment) (c : Cx) (s : State) (M : Memory) (j i qv ql n' : Nat) (Q : State → Prop)
    (P : State) (hpc : P.pc = BitVec.ofNat 64 nExit4) (hm : P.mem = M) (h19 : P.regs 19 = BitVec.ofNat 64 n')
    (hsp : P.sp = s.sp - 400#64) (h0 : P.regs 0 = BitVec.ofNat 64 qv) (h1 : P.regs 1 = BitVec.ofNat 64 ql)
    (h2 : P.regs 2 = BitVec.ofNat 64 (3 * c.vl)) (h3 : P.regs 3 = BitVec.ofNat 64 i)
    (h6 : P.regs 6 = BitVec.ofNat 64 (c.uuP j)) (h28 : P.regs 28 = s.regs 28) (h29 : P.regs 29 = s.sp - 408#64)
    (h18 : P.regs 18 = s.regs 18) (hi : i < 2) (hsp4 : 408 ≤ s.sp.toNat) (hsp48 : s.sp.toNat + 96 ≤ 2 ^ 48)
    (hal : s.sp.toNat % 16 = 0)
    (hacc : M.accessible (s.sp.toNat - 408) 504 true = true)
    (hsuc : M.readLE (s.sp.toNat - 280) 8 = c.uuC j) (hle : n' ≤ c.uuC j) (hcap : c.uuC j < 2 ^ 40)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 cmpA → X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 →
      X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 → X.regs 30 = BitVec.ofNat 64 rC1 →
      X.regs 0 = BitVec.ofNat 64 qv → X.regs 1 = BitVec.ofNat 64 ql → X.regs 2 = BitVec.ofNat 64 (3 * c.vl) →
      X.regs 3 = BitVec.ofNat 64 (c.uuP j) → X.regs 4 = BitVec.ofNat 64 n' →
      MemFrame M X.mem (is1 s) → X.mem.regions = M.regions → X.mem.readLE (s.sp.toNat - 160) 8 = i →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) P Q := by
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hn' : (BitVec.ofNat 64 n').toNat = n' := by rw [BitVec.toNat_ofNat]; omega
  have hc' : (BitVec.ofNat 64 (c.uuC j)).toNat = c.uuC j := by rw [BitVec.toNat_ofNat]; omega
  have hle' : BitVec.ofNat 64 n' ≤ BitVec.ofNat 64 (c.uuC j) := by
    rw [BitVec.le_def, hn', hc']; exact hle
  janus_run [hsuc] until [cmpA]
  refine k _ rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28
  · exact h29
  · exact h18
  · exact h0
  · exact h1
  · exact h2
  · unfold is1; janus_frame
  · simp
  · rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by rw [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the correction loop's head**: `i = 2` → `E`; else `uu.norm()` → `CALL nat.cmp` -/
theorem c1 (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (st : Mdl.St) (hC : C R c s Lk bk S j Z U qv i st) (Q : State → Prop)
    (kE : ∀ S', E R c s Lk bk S' j Z U qv → ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q)
    (kX : ∀ (X : State) (n' : Nat), X.pc = BitVec.ofNat 64 cmpA → X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 →
      X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 → X.regs 30 = BitVec.ofNat 64 rC1 →
      X.regs 0 = BitVec.ofNat 64 qv → X.regs 1 = BitVec.ofNat 64 (c.P s j U).length →
      X.regs 2 = BitVec.ofNat 64 (3 * c.vl) → X.regs 3 = BitVec.ofNat 64 (c.uuP j) → X.regs 4 = BitVec.ofNat 64 n' →
      MemFrame S.mem X.mem (is1 s) → X.mem.regions = S.mem.regions → X.mem.readLE (s.sp.toNat - 160) 8 = i →
      i < 2 → n' ≤ c.uuL j → natVal S.mem (c.uuP j) n' = natVal S.mem (c.uuP j) (c.uuL j) →
      NatNorm S.mem (c.uuP j) n' → ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hmc := hC.mc
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, hulc, huc40, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨hua, hu48, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have hpc := hC.pc; have hsp := hC.sp; have h28 := hC.r28; have h29 := hC.r29; have h18 := hC.r18
  have h0 := hC.r0; have h1 := hC.r1; have h2 := hC.r2; have h3 := hC.r3
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hiN : (BitVec.ofNat 64 i).toInt = (i : Int) := by
    have := hC.hi; unfold BitVec.toInt; rw [BitVec.toNat_ofNat]; split <;> omega
  by_cases hi : i < 2
  · have r1 := hmc.bd.sup; have r2 := hmc.bd.sul
    have hacc : S.mem.accessible (c.uuP j) (8 * c.uuL j) false = true := by
      rw [hmc.ev.fr.accessible]
      exact Memory.accessible_read_of_write _ (Memory.accessible_mono _ hua (by simp only [Cx.uuP]; omega)
        (by simp only [Cx.uuP, Cx.uuL]; omega))
    have hsuc := hmc.bd.suc
    have hB : Box (C R c s Lk bk S j Z U qv i st) := ⟨hC⟩
    clear hC hmc
    janus_run [r1, r2] until [nHead4]
    refine norm4 impl (s.regs 30) S.mem (c.uuP j) (c.uuL j) (natVal S.mem (c.uuP j) (c.uuL j)) _ Q ?_
      (by simp only [Cx.uuL]; omega) (by simp only [Cx.uuP, Cx.uuL]; omega) hacc ?_ (c.uuL j) _ (Nat.le_refl _)
      rfl ?_ rfl (fun _ _ _ _ => rfl) rfl rfl
    · intro P n' hpc' hm' h1' hsp' hS' hle' hv' hN'
      have g : ∀ r, r ≠ 19 → r ≠ 7 → r ≠ 8 → P.regs r = _ := fun r a b c => hS' r a b c
      refine c1x impl c s S.mem j i qv (c.P s j U).length n' Q P hpc' hm' h1' (by rw [hsp']) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        hi (by omega) ha48 hal (by rw [hm'] at *; exact haccS) hsuc
        (by simp only [Cx.uuC, Cx.uuL] at hle' ⊢; omega) (by simp only [Cx.uuC]; omega) ?k
      case k =>
        exact fun X a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 =>
          kX X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 hi hle' hv' hN'
      all_goals (rw [g _ (by decide) (by decide) (by decide)]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h28
      · exact h29
      · exact h18
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · have hfin := C.done hC.hi hi hC.inv
    have hM : Mc R c s Lk bk S.mem j Z U qv
        (Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length 2 (c.st0 s j U)) := hfin ▸ hmc
    have hv4 := hC.v4
    have hB : Box (Mc R c s Lk bk S.mem j Z U qv
        (Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length 2 (c.st0 s j U))) := ⟨hM⟩
    have hB4 : Box (V4 c s S.mem qv (c.P s j U).length) := ⟨hv4⟩
    clear hC hmc hM hv4 hfin
    janus_run until [cExit]
    refine kE _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hB.1, hB4.1⟩
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h28
    · exact h29
    · exact h18
    · exact h0
    · exact h1
    · exact h2

end FvModexp.Arm64.Q.DivRec
