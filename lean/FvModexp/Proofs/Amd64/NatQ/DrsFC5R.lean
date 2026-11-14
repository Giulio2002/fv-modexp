import FvModexp.Proofs.Amd64.NatQ.DrsSegD

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFC5R.lean; adapted from Amd64/NatQ/DrsC5R.lean)
# `divRecursiveStep` (amd64), final correction loop: `if len(qhatv) > s { subVW(qhatv[s:], qhatv[s:], c) }` test
(natdiv.go:874)

`c5rF`: from `subVV.abi0`'s re-entry (`0x5f0464`, `BxF`): `CMPQ SI, AX; JLE` (`SI = 0x80(SP')` = `len qhatv`,
`AX = 0x118(SP')` = `s`).
* `len(qhatv) ≤ s`: the join `0x5f04d1` → `addTo(u[s:], v[s:])` (`CALL` `0x5f0500`, return `0x5f0505`; NO bounds check
  before it; model `stC`, via `corrSub`'s `else`).
* `len(qhatv) > s`: `CALL subVW(qhatv[s:], qhatv[s:], c)` (`0x5f04cc`, return `0x5f04d1` = the join).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c5rF (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rFV2)
    (hby : BxF R c s Lk bk T j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb)))
    (hcy : T.mem.readLE ((s.regs 4).toNat - 320) 8 =
      (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2)
    (kA : ∀ X : State, BxF R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.PF s U).length stb) →
      X.rip = BitVec.ofNat 64 addToC → X.regs 4 = s.regs 4 - 400#64 → X.regs 5 = s.regs 4 - 8#64 →
      X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false → X.xmm 15 = 0#128 →
      X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (c.vl / 2 - 1)) → X.regs 3 = BitVec.ofNat 64 (c.u1 - (c.vl / 2 - 1)) →
      X.regs 1 = BitVec.ofNat 64 (c.uc - (c.vl / 2 - 1)) → X.regs 7 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)) →
      X.regs 6 = BitVec.ofNat 64 (c.vl - (c.vl / 2 - 1)) → X.regs 8 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)) →
      MemFrame T.mem X.mem (isR s) → X.mem.regions = T.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rFA →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q)
    (kW : ∀ Y : State, BxF R c s Lk bk T j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb)) →
      c.vl / 2 - 1 < (c.PF s U).length →
      Y.rip = BitVec.ofNat 64 SubVW.entry → Y.regs 4 = s.regs 4 - 400#64 → Y.regs 5 = s.regs 4 - 8#64 →
      Y.regs 14 = s.regs 14 → Y.fsBase = s.fsBase → Y.df = false → Y.xmm 15 = 0#128 →
      Y.regs 0 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)) →
      Y.regs 3 = BitVec.ofNat 64 ((c.PF s U).length - (c.vl / 2 - 1)) →
      Y.regs 1 = BitVec.ofNat 64 (3 * c.vl - (c.vl / 2 - 1)) → Y.regs 7 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)) →
      Y.regs 6 = BitVec.ofNat 64 ((c.PF s U).length - (c.vl / 2 - 1)) →
      Y.regs 8 = BitVec.ofNat 64 (3 * c.vl - (c.vl / 2 - 1)) →
      Y.regs 9 = BitVec.ofNat 64 (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 →
      MemFrame T.mem Y.mem (isR s) → Y.mem.regions = T.mem.regions →
      Y.mem.readLE ((s.regs 4).toNat - 400) 8 = rFW2 →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) Y Q) :
    ReachesRet (LibDrs.program.link impl) (retAddrOf s) T Q := by
  have hmc := hby.mc
  have hcr := hmc.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hv9 := hpre.v9.1; have hvc40 := hpre.vc40
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hul := hpre.ulc; have huc := hpre.uc40
  have hsp := hby.sp; have h5 := hby.r5; have h14 := hby.r14; have hfs := hby.fs; have hx15 := hby.x15
  have hdf := hby.df
  have hspT : (T.regs 4).toNat = (s.regs 4).toNat - 392 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have haccT : T.mem.accessible ((s.regs 4).toNat - 400) 496 true = true := by
    rw [hmc.ev.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have r1 := hby.v3.s144; have r2 := hmc.bd.ss; have r3 := hby.v3.s160; have r4 := hby.v3.s320
  have r5 := hmc.bd.sl.bb; have r6 := hcy; have r7 := hmc.bd.ul; have r8 := hmc.bd.s8
  have r9 := hmc.bd.up; have r10 := hmc.bd.uc; have r11 := hmc.bd.vp; have r12 := hmc.bd.vl
  have r13 := hmc.bd.vc
  have hqv : qv < 2 ^ 48 := by have := Janus.Arm64.Memory.accessible_bound _ hmc.qa; omega
  have hPl : (c.PF s U).length ≤ 3 * c.vl := PF_len_le (by omega)
  have ht1 := toInt_small (n := (c.PF s U).length) (by omega)
  have ht2 := toInt_small (n := c.vl / 2 - 1) (by omega)
  have e3 : BitVec.ofNat 64 (3 * c.vl) - BitVec.ofNat 64 (c.vl / 2) + 1#64 =
      BitVec.ofNat 64 (3 * c.vl - (c.vl / 2 - 1)) := by exact (bvA (by omega) (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have e4 : BitVec.ofNat 64 qv + ((0#64 - BitVec.ofNat 64 (3 * c.vl - (c.vl / 2 - 1))).sshiftRight 63 &&&
      BitVec.ofNat 64 (8 * (c.vl / 2 - 1))) = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)) :=
    bvM (by omega) (by omega) (by omega) (by omega)
  have hB1 : Box (BxF R c s Lk bk T j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb))) := ⟨hby⟩
  clear hby hmc hpre hcr
  janus64_run [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, ht1, ht2, e3, e4] until [SubVW.entry, addToC]
  · -- `len(qhatv) ≤ s`: `addTo`
    have hle : ¬ c.vl / 2 - 1 < (c.PF s U).length := by omega
    refine kA _ (by rw [← stC_le hle]; exact hB1.h) rfl ?sp ?r5 ?r14 hfs (by dsimp only) ?x15 ?a0 ?a3 ?a1 ?a7 ?a6 ?a8
      (by unfold isR; janus_frame) (by janus64_simp) ?ra
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    case r5 => exact h5
    case r14 => exact h14
    case x15 => exact hx15
    case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  · -- `len(qhatv) > s`: `subVW(qhatv[s:], qhatv[s:], c)`
    have hlt : c.vl / 2 - 1 < (c.PF s U).length := by omega
    refine kW _ hB1.h hlt rfl ?wsp ?wr5 ?wr14 hfs (by dsimp only) ?wx15 ?wa0 ?wa3 ?wa1 ?wa7 ?wa6 ?wa8 ?wa9
      (by unfold isR; janus_frame) (by janus64_simp) ?wra
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    case wr5 => exact h5
    case wr14 => exact h14
    case wx15 => exact hx15
    case wa3 => exact (bvA (by omega) (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
    case wa6 => exact (bvA (by omega) (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
    case wra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega

end FvModexp.Amd64.Q.DivRec
