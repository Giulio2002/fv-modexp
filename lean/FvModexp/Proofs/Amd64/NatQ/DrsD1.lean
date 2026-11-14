import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s50) of Arm64/NatQ/DrsD1.lean)
# `divRecursiveStep` (amd64), after the correction loop: `uu.norm()` → `CALL nat.cmp` (natdiv.go:844)

`d1`: from the loop exit `E` (`0x5eff2e`): `uu.norm()` (`norm5`, nat.go:51; `R12 = 0x68(SP')`, `DI = 0x130(SP')`), the
`len ≤ cap` check (`JA 0x5f0727` panic excluded; cap `0x70(SP')`) → `CALL nat.cmp(qhatv, uu.norm())` (`0x5eff6c`,
return `0x5eff71`). The only store is the return address (`isR`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from `norm5`'s exit (`0x5eff54`) to the `CALL nat.cmp` -/
theorem d1x (impl : List Amd64.Segment) (c : Cx) (s : State) (M : Memory) (j qv ql n' : Nat) (Q : State → Prop)
    (P : State) (hpc : P.rip = BitVec.ofNat 64 nExit5) (hm : P.mem = M) (h12 : P.regs 12 = BitVec.ofNat 64 n')
    (hsp : P.regs 4 = s.regs 4 - 392#64) (h5 : P.regs 5 = s.regs 4 - 8#64) (h14 : P.regs 14 = s.regs 14)
    (hfs : P.fsBase = s.fsBase) (hdf : P.df = false) (hx15 : P.xmm 15 = 0#128)
    (h0 : P.regs 0 = BitVec.ofNat 64 qv) (h3 : P.regs 3 = BitVec.ofNat 64 ql)
    (h1 : P.regs 1 = BitVec.ofNat 64 (3 * c.vl)) (h7 : P.regs 7 = BitVec.ofNat 64 (c.uuP j))
    (hsp4 : 408 ≤ (s.regs 4).toNat) (hsp48 : (s.regs 4).toNat + 96 ≤ 2 ^ 48)
    (hacc : M.accessible ((s.regs 4).toNat - 400) 496 true = true)
    (hsuc : M.readLE ((s.regs 4).toNat - 280) 8 = c.uuC j) (hle : n' ≤ c.uuC j) (hcap : c.uuC j < 2 ^ 40)
    (k : ∀ X : State, X.rip = BitVec.ofNat 64 cmpA → X.regs 4 = s.regs 4 - 400#64 → X.regs 5 = s.regs 4 - 8#64 →
      X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false → X.xmm 15 = 0#128 →
      X.regs 0 = BitVec.ofNat 64 qv → X.regs 3 = BitVec.ofNat 64 ql → X.regs 1 = BitVec.ofNat 64 (3 * c.vl) →
      X.regs 7 = BitVec.ofNat 64 (c.uuP j) → X.regs 6 = BitVec.ofNat 64 n' →
      MemFrame M X.mem (isR s) → X.mem.regions = M.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rD2 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) P Q := by
  subst hm
  have hgt : (BitVec.ofNat 64 (c.uuC j) < BitVec.ofNat 64 n') = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]; omega
  janus64_run [hsuc, hgt] until [cmpA]
  refine k _ rfl ?sp ?r5 ?r14 hfs rfl hx15 ?r0 ?r3 ?r1 ?r7 ?r6 (by unfold isR; janus_frame) (by janus64_simp) ?ra
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h0
  case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h3
  case r1 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h1
  case r7 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h7
  case r6 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals dsimp only
  case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **after the correction loop**: `uu.norm()` → `CALL nat.cmp` -/
theorem d1 (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (S : State) (j : Nat) (Z U : List Nat) (qv : Nat) (hE : E R c s Lk bk S j Z U qv) (Q : State → Prop)
    (kX : ∀ (X : State) (n' : Nat), X.rip = BitVec.ofNat 64 cmpA → X.regs 4 = s.regs 4 - 400#64 →
      X.regs 5 = s.regs 4 - 8#64 → X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false →
      X.xmm 15 = 0#128 → X.regs 0 = BitVec.ofNat 64 qv → X.regs 3 = BitVec.ofNat 64 (c.P s j U).length →
      X.regs 1 = BitVec.ofNat 64 (3 * c.vl) → X.regs 7 = BitVec.ofNat 64 (c.uuP j) →
      X.regs 6 = BitVec.ofNat 64 n' → MemFrame S.mem X.mem (isR s) → X.mem.regions = S.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rD2 →
      n' ≤ c.uuL j → natVal S.mem (c.uuP j) n' = natVal S.mem (c.uuP j) (c.uuL j) →
      NatNorm S.mem (c.uuP j) n' → ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) S Q := by
  have hmc := hE.mc
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  obtain ⟨hua, hu48, -, -, -⟩ := hpre.ua
  have hulc := hpre.ulc; have huc40 := hpre.uc40
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have hpc := hE.pc; have hsp := hE.sp; have h5 := hE.r5; have h14 := hE.r14; have hfs := hE.fs
  have hdf := hE.df; have hx15 := hE.x15
  have h0 := hE.r0; have h1 := hE.r1; have h3 := hE.r3
  have hspS : (S.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccS : S.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hmc.bd.sup; have r2 := hmc.bd.sul
  have hacc : S.mem.accessible (c.uuP j) (8 * c.uuL j) false = true := by
    rw [hmc.ev.fr.accessible]
    exact Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hua
      (by simp only [Cx.uuP]; omega) (by simp only [Cx.uuP, Cx.uuL]; omega))
  have hsuc := hmc.bd.suc
  clear hE hmc hpre hcr
  janus64_run [r1, r2] until [nHead5]
  refine norm5 impl (retAddrOf s) S.mem (c.uuP j) (c.uuL j) (natVal S.mem (c.uuP j) (c.uuL j)) _ Q ?_
    (by simp only [Cx.uuL]; omega) (by simp only [Cx.uuP, Cx.uuL]; omega) hacc ?_ (c.uuL j) _ (Nat.le_refl _)
    rfl ?_ ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩ rfl rfl
  · intro P n' hpc' hm' h12' hS' hle' hv' hN'
    refine d1x impl c s S.mem j qv (c.P s j U).length n' Q P hpc' hm' h12' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (by omega) (by omega) haccS hsuc (by simp only [Cx.uuC, Cx.uuL] at hle' ⊢; omega)
      (by simp only [Cx.uuC]; omega) ?k
    case k =>
      exact fun X a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 =>
        kX X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 hle' hv' hN'
    · rw [hS'.1 4 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hsp
    · rw [hS'.1 5 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
    · rw [hS'.1 14 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
    · rw [hS'.2.1]; exact hfs
    · rw [hS'.2.2.1]
    · rw [hS'.2.2.2]; exact hx15
    · rw [hS'.1 0 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h0
    · rw [hS'.1 3 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h3
    · rw [hS'.1 1 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h1
    · rw [hS'.1 7 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])

end FvModexp.Amd64.Q.DivRec
