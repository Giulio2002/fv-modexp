import FvModexp.Proofs.Arm64.Nat.DrsFC4
import FvModexp.Proofs.Arm64.Nat.DrsC5R

/-!
# `divRecursiveStep` (arm64), final correction loop: after `subVV` (natdiv.go:873-875)

`c5rF`: from `subVV.abi0`'s return `0x1bab64`: `len(qhatv) ≤ s` → the `addTo` setup `0x1babb0` (`BxF` at `stC`);
otherwise → `CALL subVW(qhatv[s:], qhatv[s:], c)` (`0x1babac`, return `0x1babb0`). Adapted from DrsC5R.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- the `addTo(u[s:], v[s:])` setup of the final correction loop -/
abbrev rFA : Nat := 0x1babb0

theorem PF_len_le {c : Cx} {s : State} {U : List Nat} (h2v : 2 ≤ c.vl) : (c.PF s U).length ≤ 3 * c.vl := by
  have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.qF s U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
    ((c.qF s U).length + ((c.V s).take (c.vl / 2 - 1)).length))
  rw [Mdl.length_toL, List.length_take] at h1
  have h2 := qF_len (c := c) (s := s) (U := U)
  have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
  show (Mdl.norm _).length ≤ _
  rw [List.length_take]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c5rF (impl : List Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 rFVV)
    (hbx : BxF R c s Lk bk T j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb)))
    (hcy : T.mem.readLE (s.sp.toNat - 320) 8 =
      (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2)
    (kA : ∀ X : State, X.pc = BitVec.ofNat 64 rFA →
      BxF R c s Lk bk X j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q)
    (kW : ∀ Y : State, Y.pc = BitVec.ofNat 64 SubVW.entry → Y.regs 30 = BitVec.ofNat 64 rFA →
      Y.regs 0 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)) →
      Y.regs 1 = BitVec.ofNat 64 ((c.PF s U).length - c.vl / 2 + 1) →
      Y.regs 2 = BitVec.ofNat 64 (3 * c.vl - c.vl / 2 + 1) → Y.regs 3 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)) →
      Y.regs 4 = BitVec.ofNat 64 ((c.PF s U).length - c.vl / 2 + 1) →
      Y.regs 5 = BitVec.ofNat 64 (3 * c.vl - c.vl / 2 + 1) →
      Y.regs 6 = BitVec.ofNat 64 (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 →
      c.vl / 2 - 1 < (c.PF s U).length →
      BxF R c s Lk bk Y j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb)) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) Y Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hmc := hbx.mc
  have hcr := hmc.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40
  have hsp := hbx.sp; have h28 := hbx.r28; have h29 := hbx.r29; have h18 := hbx.r18
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have r1 := hbx.v3.s144; have r2 := hmc.bd.ss; have r3 := hbx.v3.s160; have r4 := hbx.v3.s320
  have r5 := hmc.bd.sl.nn; have r6 := hcy
  have haccT : T.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hmc.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hqv : qv < 2 ^ 48 := by have := Memory.accessible_bound _ hmc.qa; omega
  have hPl : (c.PF s U).length ≤ 3 * c.vl := PF_len_le (by omega)
  have hti := toInt_small (n := (c.PF s U).length) (by omega)
  have hB1 : Box (McF R c s Lk bk T.mem j Z U qv (stV (c.V s) (c.vl / 2 - 1) (stQ stb))) := ⟨hbx.mc⟩
  have hB2 : Box (V3F c s T.mem qv (c.PF s U).length) := ⟨hbx.v3⟩
  have hsi := hbx.si; have hi := hbx.hi; have hpos := hbx.pos; have hinv := hbx.inv
  have e2 := bvB (a := (c.PF s U).length) (n := c.vl)
  have e3 := bvB (a := 3 * c.vl) (n := c.vl) (by omega) (by omega) (by omega)
  have e4 := bvC (q := qv) (k := c.vl / 2 - 1) (x := 3 * c.vl - c.vl / 2 + 1) (by omega) (by omega) (by omega) (by omega)
  clear hbx hmc
  janus_run [r1, r2, r3, r4, r5, r6] until [SubVW.entry, rFA]
  · -- `len(qhatv) ≤ s`
    have hle : ¬ c.vl / 2 - 1 < (c.PF s U).length := by omega
    refine kA _ rfl ⟨rfl, ?_, ?_, ?_, stC_le hle ▸ hB1.1, hB2.1, hsi, hi, hpos, hinv⟩
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · exact h28
    · exact h29
    · exact h18
  · -- `len(qhatv) > s`: `subVW(qhatv[s:], qhatv[s:], c)`
    have hlt : c.vl / 2 - 1 < (c.PF s U).length := by omega
    have e2' := e2 (by omega) (by omega) (by omega)
    refine kW _ rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ rfl hlt ⟨rfl, ?_, ?_, ?_, hB1.1, hB2.1, hsi, hi, hpos, hinv⟩
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    · rw [e3]; exact e4
    · exact e2'
    · exact e3
    · rw [e3]; exact e4
    · exact e2'
    · exact e3
    · exact h28
    · exact h29
    · exact h18

end FvModexp.Arm64.DivRec
