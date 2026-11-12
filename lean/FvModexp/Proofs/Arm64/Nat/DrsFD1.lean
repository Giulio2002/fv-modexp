import FvModexp.Proofs.Arm64.Nat.DrsFV
import FvModexp.Proofs.Arm64.Nat.DrsFCE
import FvModexp.Proofs.Arm64.Nat.DrsD1

/-!
# `divRecursiveStep` (arm64), final block after the correction loop: `u.norm()` → `CALL nat.cmp` (natdiv.go:880)

`d1F`: from the exit `EF` (`0x1babd0`): `u.norm()` (`norm9`), the `len ≤ cap` check (`BCC` panic excluded) → `CALL
nat.cmp(qhatv, u.norm())` (`0x1bac0c`, return `0x1bac10`), memory unchanged. Adapted from DrsD1.
-/

set_option autoImplicit false

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- the return address of the `nat.cmp` after the final correction loop -/
abbrev rFD2 : Nat := 0x1bac10

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from `norm9`'s exit to the `CALL nat.cmp` -/
theorem d1xF (impl : List Segment) (c : Cx) (s : State) (M : Memory) (j qv ql n' : Nat) (Q : State → Prop)
    (P : State) (hpc : P.pc = BitVec.ofNat 64 nExit9) (hm : P.mem = M) (h5 : P.regs 5 = BitVec.ofNat 64 n')
    (hsp : P.sp = s.sp - 400#64) (h0 : P.regs 0 = BitVec.ofNat 64 qv) (h1 : P.regs 1 = BitVec.ofNat 64 ql)
    (h2 : P.regs 2 = BitVec.ofNat 64 (3 * c.vl)) (h3 : P.regs 3 = BitVec.ofNat 64 c.up)
    (h28 : P.regs 28 = s.regs 28) (h29 : P.regs 29 = s.sp - 408#64) (h18 : P.regs 18 = s.regs 18)
    (hsp4 : 408 ≤ s.sp.toNat) (hsp48 : s.sp.toNat + 96 ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hacc : M.accessible (s.sp.toNat - 408) 504 true = true)
    (hsuc : M.readLE (s.sp.toNat + 56) 8 = c.uc) (hle : n' ≤ c.uc) (hcap : c.uc < 2 ^ 40)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 cmpA → X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 →
      X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 → X.regs 30 = BitVec.ofNat 64 rFD2 →
      X.regs 0 = BitVec.ofNat 64 qv → X.regs 1 = BitVec.ofNat 64 ql → X.regs 2 = BitVec.ofNat 64 (3 * c.vl) →
      X.regs 3 = BitVec.ofNat 64 c.up → X.regs 4 = BitVec.ofNat 64 n' → X.mem = M →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) P Q := by
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hn' : (BitVec.ofNat 64 n').toNat = n' := by rw [BitVec.toNat_ofNat]; omega
  have hc' : (BitVec.ofNat 64 c.uc).toNat = c.uc := by rw [BitVec.toNat_ofNat]; omega
  have hle' : BitVec.ofNat 64 n' ≤ BitVec.ofNat 64 c.uc := by
    rw [BitVec.le_def, hn', hc']; exact hle
  janus_run [hsuc] until [cmpA]
  refine k _ rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h28
  · exact h29
  · exact h18
  · exact h0
  · exact h1
  · exact h2
  · exact h3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **after the correction loop**: `uu.norm()` → `CALL nat.cmp` -/
theorem d1F (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State)
    (j : Nat) (Z U : List Nat) (qv : Nat) (hE : EF R c s Lk bk S j Z U qv) (Q : State → Prop)
    (kX : ∀ (X : State) (n' : Nat), X.pc = BitVec.ofNat 64 cmpA → X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 →
      X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 → X.regs 30 = BitVec.ofNat 64 rFD2 →
      X.regs 0 = BitVec.ofNat 64 qv → X.regs 1 = BitVec.ofNat 64 (c.PF s U).length →
      X.regs 2 = BitVec.ofNat 64 (3 * c.vl) → X.regs 3 = BitVec.ofNat 64 c.up → X.regs 4 = BitVec.ofNat 64 n' →
      X.mem = S.mem → n' ≤ c.u1 → natVal S.mem c.up n' = natVal S.mem c.up c.u1 →
      NatNorm S.mem c.up n' → ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hmc := hE.mc
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, hulc, huc40, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨hua, hu48, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hjB := hmc.jB
  have hpc := hE.pc; have hsp := hE.sp; have h28 := hE.r28; have h29 := hE.r29; have h18 := hE.r18
  have h0 := hE.r0; have h1 := hE.r1; have h2 := hE.r2
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hmc.bd.sl.s5; have r2 := hmc.bd.sl.ul'
  have hacc : S.mem.accessible c.up (8 * c.u1) false = true := by
    rw [hmc.ev.fr.accessible]
    exact Memory.accessible_read_of_write _ (Memory.accessible_mono _ hua (by omega)
      (by omega))
  have hsuc := hmc.bd.sl.s7
  have hB : Box (EF R c s Lk bk S j Z U qv) := ⟨hE⟩
  clear hE hmc
  janus_run [r1, r2] until [nHead9]
  refine norm9 impl (s.regs 30) S.mem c.up c.u1 (natVal S.mem c.up c.u1) _ Q ?_
    (by omega) (by omega) hacc ?_ c.u1 _ (Nat.le_refl _)
    rfl ?_ rfl (fun _ _ _ _ => rfl) rfl rfl
  · intro P n' hpc' hm' h1' hsp' hS' hle' hv' hN'
    have g : ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → P.regs r = _ := fun r a b c => hS' r a b c
    refine d1xF impl c s S.mem j qv (c.PF s U).length n' Q P hpc' hm' h1' (by rw [hsp']) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (by omega) ha48 hal (by rw [hm'] at *; exact haccS) hsuc
      (by omega) (by omega) ?k
    case k =>
      exact fun X a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 =>
        kX X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hle' hv' hN'
    all_goals (rw [g _ (by decide) (by decide) (by decide)]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h0
    · exact h1
    · exact h2
    · exact h28
    · exact h29
    · exact h18
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])

end FvModexp.Arm64.DivRec
