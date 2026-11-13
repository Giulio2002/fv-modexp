import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsFD5
import FvModexp.Proofs.Arm64.Nat.DrsNorm

/-! (Q-form copy of Arm64/Nat/DrsFD6R.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final block: to `CALL addTo(z, qhat.norm())` (natdiv.go:891)

`d6rF`: from `0x1bac98` (`McF` at `Cx.sGF`) → `qhat.norm()` (`norm10`, nat.go:51, pointer `R3 = t0`, length
`R1 = len qhat`) → the `len ≤ cap` check (`BCC` panic excluded: `n' ≤ B + 1`) → the `CALL addTo` state (`0x1bacd8`,
return `0x1bacdc`). No stores.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

/-- the return address of `addTo(z, qhat.norm())` -/
abbrev rFD6 : Nat := 0x1bacdc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- from `norm10`'s exit to the `CALL addTo` -/
theorem d6xF (impl : List Segment) (c : Cx) (s : State) (M : Memory) (n' : Nat) (Q : State → Prop)
    (P : State) (hpc : P.pc = BitVec.ofNat 64 nExit10) (hm : P.mem = M) (h1 : P.regs 1 = BitVec.ofNat 64 n')
    (hsp : P.sp = s.sp - 400#64) (h3 : P.regs 3 = BitVec.ofNat 64 c.t0) (h28 : P.regs 28 = s.regs 28)
    (h29 : P.regs 29 = s.sp - 408#64) (h18 : P.regs 18 = s.regs 18) (hsp4 : 408 ≤ s.sp.toNat)
    (hsp48 : s.sp.toNat + 96 ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hacc : M.accessible (s.sp.toNat - 408) 504 true = true)
    (r1 : M.readLE (s.sp.toNat - 216) 8 = c.vl / 2 + 1) (r2 : M.readLE (s.sp.toNat + 8) 8 = c.qp)
    (r3 : M.readLE (s.sp.toNat + 24) 8 = c.qc) (r4 : M.readLE (s.sp.toNat + 16) 8 = c.ql)
    (hle : n' ≤ c.vl / 2 + 1) (hB : c.vl / 2 + 1 < 2 ^ 40)
    (k : ∀ X : State, X.pc = BitVec.ofNat 64 addToA → X.regs 30 = BitVec.ofNat 64 rFD6 →
      X.regs 0 = BitVec.ofNat 64 c.qp → X.regs 1 = BitVec.ofNat 64 c.ql → X.regs 2 = BitVec.ofNat 64 c.qc →
      X.regs 3 = BitVec.ofNat 64 c.t0 → X.regs 4 = BitVec.ofNat 64 n' → X.regs 5 = BitVec.ofNat 64 (c.vl / 2 + 1) →
      X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 →
      X.mem = M → ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) P Q := by
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hn' : (BitVec.ofNat 64 n').toNat = n' := by rw [BitVec.toNat_ofNat]; omega
  have hc' : (BitVec.ofNat 64 (c.vl / 2 + 1)).toNat = c.vl / 2 + 1 := by rw [BitVec.toNat_ofNat]; omega
  have hle' : BitVec.ofNat 64 n' ≤ BitVec.ofNat 64 (c.vl / 2 + 1) := by
    rw [BitVec.le_def, hn', hc']; exact hle
  janus_run [r1, r2, r3, r4] until [addToA]
  refine k _ rfl rfl ?_ ?_ ?_ ?_ ?_ rfl rfl ?_ ?_ ?_ ?_
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  all_goals first | exact h28 | exact h29 | exact h18 | exact h3 | exact h1 | exact hm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`qhat.norm()`** from `0x1bac98` → the `CALL addTo(z, qhat.norm())` state -/
theorem d6rF (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rFD5) (hsp : T.sp = s.sp - 400#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 408#64) (h18 : T.regs 18 = s.regs 18)
    (hmc : McF R c s Lk bk T.mem j Z U qv (c.sGF s U))
    (k : ∀ (X : State) (n' : Nat), X.pc = BitVec.ofNat 64 addToA → X.regs 30 = BitVec.ofNat 64 rFD6 →
      X.regs 0 = BitVec.ofNat 64 c.qp → X.regs 1 = BitVec.ofNat 64 c.ql → X.regs 2 = BitVec.ofNat 64 c.qc →
      X.regs 3 = BitVec.ofNat 64 c.t0 → X.regs 4 = BitVec.ofNat 64 n' → X.regs 5 = BitVec.ofNat 64 (c.vl / 2 + 1) →
      X.sp = s.sp - 400#64 → X.regs 28 = s.regs 28 → X.regs 29 = s.sp - 408#64 → X.regs 18 = s.regs 18 →
      X.mem = T.mem → n' ≤ (c.qF s U).length →
      natVal T.mem c.t0 n' = natVal T.mem c.t0 (c.qF s U).length → NatNorm T.mem c.t0 n' →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  have ht48 := hcr.t048
  have hacc : T.mem.accessible c.t0 (8 * (c.qF s U).length) false = true := by
    rw [hmc.ev.fr.accessible]
    exact Memory.accessible_read_of_write _ (Memory.accessible_mono _ hcr.t0acc (Nat.le_refl _) (by omega))
  have q1 := hmc.bd.sl.q0c; have q2 := hmc.bd.sl.s1; have q3 := hmc.bd.sl.s3; have q4 := hmc.bd.sl.s2
  have r1 := hmc.bd.sl.q0p; have r2 := hmc.q3.s200
  have hB : Box (McF R c s Lk bk T.mem j Z U qv (c.sGF s U)) := ⟨hmc⟩
  clear hmc
  janus_run [r1, r2] until [nHead10]
  refine norm10 impl (s.regs 30) T.mem c.t0 (c.qF s U).length (natVal T.mem c.t0 (c.qF s U).length) _ Q ?_
    (by omega) (by omega) hacc ?_ (c.qF s U).length _ (Nat.le_refl _) rfl ?_ rfl (fun _ _ _ _ => rfl) rfl rfl
  · intro P n' hpc' hm' h1' hsp' hS' hle' hv' hN'
    have g : ∀ r, r ≠ 1 → r ≠ 6 → r ≠ 7 → P.regs r = _ := fun r a b c => hS' r a b c
    refine d6xF impl c s T.mem n' Q P hpc' hm' h1' (by rw [hsp']) ?_ ?_ ?_ ?_ (by omega) ha48 hal haccT
      q1 q2 q3 q4 (by omega) (by omega) ?k
    case k =>
      exact fun X a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 =>
        k X n' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 hle' hv' hN'
    all_goals (rw [g _ (by decide) (by decide) (by decide)]; try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals first | exact h28 | exact h29 | exact h18 | rfl
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])

end FvModexp.Arm64.Q.DivRec
