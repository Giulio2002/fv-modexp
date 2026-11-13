import FvModexp.Proofs.Amd64.NatQ.DrsFD5
import FvModexp.Proofs.Amd64.NatQ.DrsNormF

set_option autoImplicit false

/-! (amd64 twin (asm s54) of Arm64/NatQ/DrsFD6R.lean; norm-call pattern of Amd64/NatQ/DrsFD1.lean)
# `divRecursiveStep` (amd64), final block: `qhat.norm()` → the `addTo(z, qhat.norm())` call setup (natdiv.go:891)

`d6rF`: from `0x5f0630` (`rJF6`, `McF … sGF`): `DI = t0`, `BX = len qhat` → `normF5` (`0x5f0645`) → its exit `0x5f0654`
(`d6xF`): `R8 = B + 1`, `CMPQ R8, BX; JB` (panicBounds excluded: `n' ≤ B + 1`), `AX = qp`, `CX = qc`, `SI = n'`,
`BX = ql` → `CALL addTo` (`0x5f0680`, return `0x5f0685` = `rFD6`). The only store is the return slot `r - 400`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the return address of `addTo(z, qhat.norm())` -/
abbrev rFD6 : Nat := 0x5f0685

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from `normF5`'s exit (`0x5f0654`) to the `CALL addTo` -/
theorem d6xF (impl : List Amd64.Segment) (c : Cx) (s : State) (M : Memory) (n' : Nat) (Q : State → Prop)
    (P : State) (hpc : P.rip = BitVec.ofNat 64 nExF5) (hm : P.mem = M) (h3 : P.regs 3 = BitVec.ofNat 64 n')
    (hsp : P.regs 4 = s.regs 4 - 392#64) (h5 : P.regs 5 = s.regs 4 - 8#64) (h14 : P.regs 14 = s.regs 14)
    (hfs : P.fsBase = s.fsBase) (hdf : P.df = false) (hx15 : P.xmm 15 = 0#128)
    (h7 : P.regs 7 = BitVec.ofNat 64 c.t0)
    (hsp4 : 408 ≤ (s.regs 4).toNat) (hsp48 : (s.regs 4).toNat + 96 ≤ 2 ^ 48)
    (hacc : M.accessible ((s.regs 4).toNat - 400) 496 true = true)
    (r1 : M.readLE ((s.regs 4).toNat - 224) 8 = c.vl / 2 + 1) (r2 : M.readLE ((s.regs 4).toNat + 32) 8 = c.qp)
    (r3 : M.readLE ((s.regs 4).toNat + 48) 8 = c.qc) (r4 : M.readLE ((s.regs 4).toNat + 40) 8 = c.ql)
    (hle : n' ≤ c.vl / 2 + 1) (hB : c.vl / 2 + 1 < 2 ^ 40)
    (k : ∀ X : State, X.rip = BitVec.ofNat 64 addToC → X.regs 4 = s.regs 4 - 400#64 →
      X.regs 5 = s.regs 4 - 8#64 → X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false →
      X.xmm 15 = 0#128 →
      X.regs 0 = BitVec.ofNat 64 c.qp → X.regs 3 = BitVec.ofNat 64 c.ql →
      X.regs 1 = BitVec.ofNat 64 c.qc → X.regs 7 = BitVec.ofNat 64 c.t0 →
      X.regs 6 = BitVec.ofNat 64 n' → X.regs 8 = BitVec.ofNat 64 (c.vl / 2 + 1) →
      MemFrame M X.mem (isR s) → X.mem.regions = M.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rFD6 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) P Q := by
  subst hm
  have hlt : (BitVec.ofNat 64 (c.vl / 2 + 1) < BitVec.ofNat 64 n') = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]
    rw [Nat.mod_eq_of_lt (show c.vl / 2 + 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show n' < 2 ^ 64 by omega)]
    omega
  janus64_run [r1, r2, r3, r4, hlt] until [addToC]
  refine k _ rfl ?sp ?r5 ?r14 hfs rfl hx15 ?a0 ?a3 ?a1 ?a7 ?a6 ?a8
    (by unfold isR; janus_frame) (by janus64_simp) ?ra
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
  case r5 => exact h5
  case r14 => exact h14
  case a7 => exact h7
  all_goals (try dsimp only)
  case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`qhat.norm()`** from `0x5f0630` → the `CALL addTo(z, qhat.norm())` state -/
theorem d6rF (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rJF6) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false) (hx15 : T.xmm 15 = 0#128)
    (hmc : McF R c s Lk bk T.mem j Z U qv (c.sGF s U))
    (k : ∀ (X : State) (n' : Nat), X.rip = BitVec.ofNat 64 addToC → X.regs 4 = s.regs 4 - 400#64 →
      X.regs 5 = s.regs 4 - 8#64 → X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false →
      X.xmm 15 = 0#128 →
      X.regs 0 = BitVec.ofNat 64 c.qp → X.regs 3 = BitVec.ofNat 64 c.ql →
      X.regs 1 = BitVec.ofNat 64 c.qc → X.regs 7 = BitVec.ofNat 64 c.t0 →
      X.regs 6 = BitVec.ofNat 64 n' → X.regs 8 = BitVec.ofNat 64 (c.vl / 2 + 1) →
      MemFrame T.mem X.mem (isR s) → X.mem.regions = T.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rFD6 → n' ≤ (c.qF s U).length →
      natVal T.mem c.t0 n' = natVal T.mem c.t0 (c.qF s U).length → NatNorm T.mem c.t0 n' →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have ht48 := hcr.t048
  have hacc : T.mem.accessible c.t0 (8 * (c.qF s U).length) false = true := by
    rw [hmc.ev.fr.accessible]
    exact Janus.Arm64.Memory.accessible_read_of_write _
      (Janus.Arm64.Memory.accessible_mono _ hcr.t0acc (Nat.le_refl _) (by omega))
  have q1 := hmc.bd.sl.q0c; have q2 := hmc.bd.sl.s1; have q3 := hmc.bd.sl.s3; have q4 := hmc.bd.sl.s2
  have r1 := hmc.bd.sl.q0p; have r2 := hmc.q3.s200
  clear hmc hpre hcr
  janus64_run [r1, r2] until [nHdF5]
  refine normF5 impl (retAddrOf s) T.mem c.t0 (c.qF s U).length (natVal T.mem c.t0 (c.qF s U).length) _ Q ?_
    (by omega) (by omega) hacc ?_ (c.qF s U).length _ (Nat.le_refl _)
    rfl ?_ ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩ rfl rfl
  · intro P n' hpc' hm' h3' hS' hle' hv' hN'
    refine d6xF impl c s T.mem n' Q P hpc' hm' h3' ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (by omega) (by omega) haccT q1 q2 q3 q4 (by omega) (by omega) ?k
    case k =>
      exact fun X a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 =>
        k X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 hle' hv' hN'
    · rw [hS'.1 4 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hsp
    · rw [hS'.1 5 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
    · rw [hS'.1 14 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
    · rw [hS'.2.1]; exact hfs
    · rw [hS'.2.2.1]
    · rw [hS'.2.2.2]; exact hx15
    · rw [hS'.1 7 (by decide) (by decide)]; simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])

end FvModexp.Amd64.Q.DivRec
