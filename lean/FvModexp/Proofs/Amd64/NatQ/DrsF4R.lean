import FvModexp.Proofs.Amd64.NatQ.DrsF4D

set_option autoImplicit false

/-! (amd64 twin (asm s52) of Arm64/NatQ/DrsF4R.lean; adapted from Amd64/NatQ/DrsB4R.lean)
# `divRecursiveStep` (amd64), final block segment 4 (after the call) (natdiv.go:867)

`b4rF`: from the return state `T` of `nat.mul` (`0x5f0319`, `McF` at `Cx.sF0`) → the stores of the result `qhatv`
(`0x138/0x80/0x90(SP)` = `r-80`, `r-264`, `r-248`), `i := 0` (`XORL DX, DX`) → the final correction loop's head `CF`
(`0x5f0360`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the length of the model product fits a word -/
theorem PF_len {c : Cx} {s : State} {U : List Nat} (h9 : c.vl ≤ 2 ^ 9) : (c.PF s U).length < 2 ^ 64 := by
  have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.qF s U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
    ((c.qF s U).length + ((c.V s).take (c.vl / 2 - 1)).length))
  rw [Mdl.length_toL, List.length_take] at h1
  have h2 := qF_len (c := c) (s := s) (U := U)
  have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
  show (Mdl.norm _).length < _
  rw [List.length_take]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- after `nat.mul` returns: the stores of `qhatv`'s slots and `i := 0` → `C` -/
theorem b4rF (impl : List Amd64.Segment) (c : Cx) (s : State) (R : RtInv) (L' : List (Nat × Nat)) (b' : Nat) (j : Nat)
    (Z U : List Nat) (qv : Nat) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rF4) (hsp : T.regs 4 = s.regs 4 - 392#64)
    (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase)
    (hdf : T.df = false) (hx15 : T.xmm 15 = 0#128) (hr0 : T.regs 0 = BitVec.ofNat 64 qv)
    (hr3 : T.regs 3 = BitVec.ofNat 64 (c.PF s U).length) (hr1 : T.regs 1 = BitVec.ofNat 64 (3 * c.vl))
    (hmc : McF R c s L' b' T.mem j Z U qv (c.sF0 s U)) (hqv : qv < 2 ^ 64)
    (k : ∀ S', CF R c s L' b' S' j Z U qv 0 (c.sF0 s U) → ReachesRet (LibDrs.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1
  have hWg := drsW64_ge c.vl; have hW := hcr.hW
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hPl : (c.PF s U).length < 2 ^ 64 := PF_len hv9
  have h3v : 3 * c.vl < 2 ^ 64 := by omega
  have hB : Box (McF R c s L' b' T.mem j Z U qv (c.sF0 s U)) := ⟨hmc⟩
  clear hmc hcr hpre
  janus64_run until [cHeadF]
  refine k _ ⟨rfl, ?sp, ?r5, ?r14, hfs, rfl, hx15, ?r0, ?r3, ?r1, ?r2,
    hB.h.own3 (by unfold is3F; janus_frame) (by janus64_simp), ⟨?e1, ?e2, ?e3⟩, by omega, rfl⟩
  case sp => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hsp
  case r5 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
  case r14 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  case r0 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hr0
  case r3 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hr3
  case r1 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hr1
  case r2 => simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals dsimp only
  case e1 =>
    (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]))
    rw [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]; omega
  case e2 =>
    (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]))
    rw [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]; omega
  case e3 =>
    (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]))
    rw [show (256 : Nat) ^ 8 = 2 ^ 64 by decide]; omega

end FvModexp.Amd64.Q.DivRec
