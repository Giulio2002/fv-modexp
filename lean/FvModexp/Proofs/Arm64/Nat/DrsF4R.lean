import FvModexp.Proofs.Arm64.Nat.DrsF4C

/-!
# `divRecursiveStep` (arm64), final block segment 4 (after the call): `qhatv = qhatv.mul(stk, qhat, v[:s])` (natdiv.go:867)

`b4rF`: from the return state `T` of `nat.mul` (`0x1baa90`, `McF` at `Cx.sF0`) → the stores of `qhatv`'s slots
(`SP'+320/144/160`), `i := 0` → the final correction loop's head `CF` (`0x1baab8`). Adapted from DrsB4R.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- the three stores of the final block's `qhatv` slots (`SP'+320/144/160`) read back -/
theorem rd3F (M : Memory) (p a b c : Nat) (hp : 256 ≤ p) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    (((M.writeLE (p - 80) 8 a).writeLE (p - 256) 8 b).writeLE (p - 240) 8 c).readLE (p - 80) 8 = a ∧
    (((M.writeLE (p - 80) 8 a).writeLE (p - 256) 8 b).writeLE (p - 240) 8 c).readLE (p - 256) 8 = b ∧
    (((M.writeLE (p - 80) 8 a).writeLE (p - 256) 8 b).writeLE (p - 240) 8 c).readLE (p - 240) 8 = c := by
  have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt ha]
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt hb]
  · rw [Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt hc]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- after `nat.mul` returns: the stores of `qhatv`'s slots and `i := 0` → `C` -/
theorem b4rF (impl : List Segment) (_hap : ImplApart Extracted.program impl) (R : RtInv)
    (c : Cx) (s : State) (L' : List (Nat × Nat)) (b' : Nat) (j : Nat) (Z U : List Nat) (qv : Nat) (Q : State → Prop)
    (T : State) (hTpc : T.pc = BitVec.ofNat 64 rF4) (hTsp : T.sp = s.sp - 400#64) (hT28 : T.regs 28 = s.regs 28)
    (hT29 : T.regs 29 = s.sp - 408#64) (hT18 : T.regs 18 = s.regs 18) (hr0 : T.regs 0 = BitVec.ofNat 64 qv)
    (hr1 : T.regs 1 = BitVec.ofNat 64 (c.PF s U).length) (hr2 : T.regs 2 = BitVec.ofNat 64 (3 * c.vl))
    (hmc : McF R c s L' b' T.mem j Z U qv (c.sF0 s U)) (hqv : qv < 2 ^ 64)
    (k : ∀ S', CF R c s L' b' S' j Z U qv 0 (c.sF0 s U) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn' : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hPl : (c.PF s U).length < 2 ^ 64 := by
    have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.qF s U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
      ((c.qF s U).length + ((c.V s).take (c.vl / 2 - 1)).length))
    rw [Mdl.length_toL, List.length_take] at h1
    have h2 := qF_len (c := c) (s := s) (U := U)
    have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
    show (Mdl.norm _).length < _
    rw [List.length_take]
    omega
  have h3v : 3 * c.vl < 2 ^ 64 := by omega
  obtain ⟨e1, e2, e3⟩ := rd3F T.mem s.sp.toNat qv (c.PF s U).length (3 * c.vl) (by omega) hqv hPl h3v
  have hB : Box (McF R c s L' b' T.mem j Z U qv (c.sF0 s U)) := ⟨hmc⟩
  clear hmc
  janus_run until [cHeadF]
  refine k _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, hB.1.own3 (by unfold is3F; janus_frame) (by simp),
    ⟨?_, ?_, ?_⟩, by omega, rfl⟩
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact hT28
  · exact hT29
  · exact hT18
  · exact hr0
  · exact hr1
  · exact hr2
  all_goals (try dsimp only)
  · exact e1
  · exact e2
  · exact e3

end FvModexp.Arm64.DivRec
