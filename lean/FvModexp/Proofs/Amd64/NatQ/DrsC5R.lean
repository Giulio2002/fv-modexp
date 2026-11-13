import FvModexp.Proofs.Amd64.NatQ.DrsC4
import FvModexp.Proofs.Common.MaskWord

set_option autoImplicit false

/-! (amd64 twin (asm s50) of Arm64/NatQ/DrsC5R.lean)
# `divRecursiveStep` (amd64), correction loop: `if len(qhatv) > s { subVW(qhatv[s:], qhatv[s:], c) }` test (natdiv.go:839)

`c5r`: from `subVV.abi0`'s re-entry (`0x5efea1`, `Bx`): `CMPQ SI, AX; JLE` (`SI = 0x88(SP')` = `len qhatv`, `AX = 0x78(SP')`
= `s`).
* `len(qhatv) ≤ s`: the join `0x5eff18` (`CMPQ BX, AX; JAE`: `len uu ≥ s`) → `addTo(uu[s:], v[s:])` (`CALL` `0x5efd80`,
  return `0x5efd85`; model `stC`, via `corrSub`'s `else`).
* `len(qhatv) > s`: `CALL subVW(qhatv[s:], qhatv[s:], c)` (`0x5eff06`, return `0x5eff0b`; `DI = qv + (mask & 8s)`).
Both continuations get `Bx` of the input state `T` (no store happens before the `CALL`) and the callee-entry facts.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- `addTo`'s entry -/
abbrev addToC : Nat := 0x5e62c0

/-- the return address of the correction loop's `CALL addTo` -/
abbrev rA : Nat := 0x5efd85

/-- the return address of the correction loop's `CALL subVW(qhatv[s:], …)` -/
abbrev rW2 : Nat := 0x5eff0b

/-- the model after `qhat--` and `qhatv -= v[:s]` (with the borrow into `qhatv[s:]`) -/
@[reducible] def stC (V : List Nat) (s0 ql : Nat) (stb : Mdl.St) : Mdl.St :=
  { stQ stb with buf := Mdl.corrSub stb.buf (V.take s0) s0 ql }

theorem stC_le {V : List Nat} {s0 ql : Nat} {stb : Mdl.St} (h : ¬ s0 < ql) :
    stV V s0 (stQ stb) = stC V s0 ql stb := by
  simp only [stC, stV, stQ, Mdl.corrSub, if_neg h]

theorem bvA {u j : Nat} (hj : j ≤ u) (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u - BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (u - j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem bvM {q k x : Nat} (hx0 : 0 < x) (hx : x < 2 ^ 63) (hk : k < 2 ^ 64) (hq : q + k < 2 ^ 64) :
    BitVec.ofNat 64 q + ((0#64 - BitVec.ofNat 64 x).sshiftRight 63 &&& BitVec.ofNat 64 k) = BitVec.ofNat 64 (q + k) := by
  rw [FvModexp.sshr63_allOnes _ (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega), BitVec.allOnes_and]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toInt_small {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]
  rw [if_pos (by omega)]; congr 1; omega

theorem P_len_le {c : Cx} {s : State} {j : Nat} {U : List Nat} (h2v : 2 ≤ c.vl) : (c.P s j U).length ≤ 3 * c.vl := by
  have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.q0 s j U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
    ((c.q0 s j U).length + ((c.V s).take (c.vl / 2 - 1)).length))
  rw [Mdl.length_toL, List.length_take] at h1
  have h2 := q0_len (c := c) (s := s) (j := j) (U := U)
  have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
  show (Mdl.norm _).length ≤ _
  rw [List.length_take]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem c5r (impl : List Amd64.Segment) (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat)
    (j : Nat) (Z U : List Nat) (qv i : Nat) (stb : Mdl.St) (Q : State → Prop)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 rV2)
    (hby : Bx R c s Lk bk T j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb)))
    (hcy : T.mem.readLE ((s.regs 4).toNat - 320) 8 =
      (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2)
    (kA : ∀ X : State, Bx R c s Lk bk T j Z U qv i stb (stC (c.V s) (c.vl / 2 - 1) (c.P s j U).length stb) →
      X.rip = BitVec.ofNat 64 addToC → X.regs 4 = s.regs 4 - 400#64 → X.regs 5 = s.regs 4 - 8#64 →
      X.regs 14 = s.regs 14 → X.fsBase = s.fsBase → X.df = false → X.xmm 15 = 0#128 →
      X.regs 0 = BitVec.ofNat 64 (c.up + 8 * (j - 1)) → X.regs 3 = BitVec.ofNat 64 (c.u1 - j + 1) →
      X.regs 1 = BitVec.ofNat 64 (c.uc - (j - 1)) → X.regs 7 = BitVec.ofNat 64 (c.vp + 8 * (c.vl / 2 - 1)) →
      X.regs 6 = BitVec.ofNat 64 (c.vl - c.vl / 2 + 1) → X.regs 8 = BitVec.ofNat 64 (c.vc - (c.vl / 2 - 1)) →
      MemFrame T.mem X.mem (isR s) → X.mem.regions = T.mem.regions →
      X.mem.readLE ((s.regs 4).toNat - 400) 8 = rA →
      ReachesRet (LibDrs.program.link impl) (retAddrOf s) X Q)
    (kW : ∀ Y : State, Bx R c s Lk bk T j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb)) →
      c.vl / 2 - 1 < (c.P s j U).length →
      Y.rip = BitVec.ofNat 64 SubVW.entry → Y.regs 4 = s.regs 4 - 400#64 → Y.regs 5 = s.regs 4 - 8#64 →
      Y.regs 14 = s.regs 14 → Y.fsBase = s.fsBase → Y.df = false → Y.xmm 15 = 0#128 →
      Y.regs 0 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)) →
      Y.regs 3 = BitVec.ofNat 64 ((c.P s j U).length - (c.vl / 2 - 1)) →
      Y.regs 1 = BitVec.ofNat 64 (3 * c.vl - (c.vl / 2 - 1)) → Y.regs 7 = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)) →
      Y.regs 6 = BitVec.ofNat 64 ((c.P s j U).length - (c.vl / 2 - 1)) →
      Y.regs 8 = BitVec.ofNat 64 (3 * c.vl - (c.vl / 2 - 1)) →
      Y.regs 9 = BitVec.ofNat 64 (Mdl.subVV (stb.buf.take (c.vl / 2 - 1)) ((c.V s).take (c.vl / 2 - 1))).2 →
      MemFrame T.mem Y.mem (isR s) → Y.mem.regions = T.mem.regions →
      Y.mem.readLE ((s.regs 4).toNat - 400) 8 = rW2 →
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
  have hjm : j ≤ c.u1 - c.vl := by have := hmc.li.2.2.2.2.2.2.2; omega
  have hjB := hmc.jB
  have r1 := hby.v4.s152; have r2 := hmc.bs.b1; have r3 := hby.v4.s168; have r4 := hby.v4.s328
  have r5 := hmc.bd.sl.bb; have r6 := hcy; have r7 := hmc.bd.sul; have r8 := hmc.bs.b8
  have r9 := hmc.bs.uptr; have r10 := hmc.bs.ucap; have r11 := hmc.bs.vptr; have r12 := hmc.bs.vlen
  have r13 := hmc.bs.vcap
  have hqv : qv < 2 ^ 48 := by have := Janus.Arm64.Memory.accessible_bound _ hmc.qa; omega
  have hPl : (c.P s j U).length ≤ 3 * c.vl := P_len_le (by omega)
  have ht1 := toInt_small (n := (c.P s j U).length) (by omega)
  have ht2 := toInt_small (n := c.vl / 2 - 1) (by omega)
  have e1 : BitVec.ofNat 64 (c.u1 - (j - c.vl / 2)) - BitVec.ofNat 64 (c.vl / 2) + 1#64 =
      BitVec.ofNat 64 (c.u1 - j + 1) := by exact (bvA (by omega) (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have e3 : BitVec.ofNat 64 (3 * c.vl) - BitVec.ofNat 64 (c.vl / 2) + 1#64 =
      BitVec.ofNat 64 (3 * c.vl - (c.vl / 2 - 1)) := by exact (bvA (by omega) (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have e4 : BitVec.ofNat 64 qv + ((0#64 - BitVec.ofNat 64 (3 * c.vl - (c.vl / 2 - 1))).sshiftRight 63 &&&
      BitVec.ofNat 64 (8 * (c.vl / 2 - 1))) = BitVec.ofNat 64 (qv + 8 * (c.vl / 2 - 1)) :=
    bvM (by omega) (by omega) (by omega) (by omega)
  have t7 := tN (by omega : c.u1 - (j - c.vl / 2) < 2 ^ 64)
  have t8 := tN (by omega : c.vl / 2 - 1 < 2 ^ 64)
  have hB1 : Box (Bx R c s Lk bk T j Z U qv i stb (stV (c.V s) (c.vl / 2 - 1) (stQ stb))) := ⟨hby⟩
  clear hby hmc hpre hcr
  janus64_run [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, ht1, ht2, t7, t8, e1, e3, e4] until [SubVW.entry, addToC]
  · -- `len(qhatv) ≤ s`: `addTo`
    have hle : ¬ c.vl / 2 - 1 < (c.P s j U).length := by omega
    refine kA _ (by rw [← stC_le hle]; exact hB1.h) rfl ?sp ?r5 ?r14 hfs (by dsimp only) ?x15 ?a0 ?a3 ?a1 ?a7 ?a6 ?a8
      (by unfold isR; janus_frame) (by janus64_simp) ?ra
    all_goals (try simp only [Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    case r5 => exact h5
    case r14 => exact h14
    case x15 => exact hx15
    case ra => (repeat (first | rw [Janus.Arm64.Memory.readLE_writeLE_self] | rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])) <;> omega
  · -- `len(qhatv) > s`: `subVW(qhatv[s:], qhatv[s:], c)`
    have hlt : c.vl / 2 - 1 < (c.P s j U).length := by omega
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
