import FvModexp.Proofs.Amd64.Nat.DivBasicRel
import FvModexp.Proofs.Amd64.Nat.DivBasicCallees
import FvModexp.Proofs.Common.MaskWord

set_option autoImplicit false

/-!
# `divBasic` (amd64): the runs of `qhatv[n] = c; qhl; c := subVV(u[j:j+qhl], u[j:], qhatv[:qhl])` (natdiv.go:703-709)
on small contexts (agent top s24)

`subQ`: `afterVww = +0x2bf → subPt = +0x30e`: `CMPQ len qhatv, n` (bounds), `qhatv[n] = c` (`c` = mulAddVWW's carry at
`RSP-160`), `qhl := len(qhatv) = n + 1`, `qhl--` when `j + qhl > len u ∧ c = 0` (`RDX = qhl`, `RSI = j`, `RBX = qhatv.ptr`).
`subRun`: `subPt → afterSub = +0x3bc`: bounds checks, `&u[j]` (masked `8j`), spills `qhl → RSP-128`, `cap(u)-j → RSP-80`,
`&u[j] → RSP-48`, the ABI0 frame `[RSP-224, RSP-152)` = `(&u[j], qhl, cap u - j, &u[j], qhl, cap u - j, qhatv, qhl,
cap qhatv)`, `CALL subVV.abi0` (return slot `RSP-232`, borrow at `RSP-152`), `XORPS X15; MOVQ FS:-8, R14`.
(`RSP` = the entry's.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

/-- `qhl` (natdiv.go:705-708) -/
@[reducible] def qhlOf (j vl ul c : Nat) : Nat := if ul < j + (vl + 1) ∧ c = 0 then vl else vl + 1

/-- after the `qhl` computation (`LEAQ 0(DX)(SI*1), DI`) -/
abbrev subPt : Nat := segAddr Extracted.program fn + 0x30e

theorem toInt_add_lt (a b : Nat) (h : a + b < 2 ^ 63) :
    BitVec.toInt (BitVec.ofNat 64 a + BitVec.ofNat 64 b) = ((a + b : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have : (BitVec.ofNat 64 a + BitVec.ofNat 64 b).toNat = a + b := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [this]; split <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem subQ (impl : List Amd64.Segment) (r : Nat) (Q : State → Prop) (S : State) (sp t vl j ul c : Nat)
    (hpc : S.rip = BitVec.ofNat 64 afterVww) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (hvb : vl + 4 ≤ 2 ^ 16) (hj : j < 2 ^ 40) (hul : ul < 2 ^ 40) (hc : c < 2 ^ 64) (ht48 : t + 8 * (vl + 1) ≤ 2 ^ 48)
    (htacc : S.mem.accessible t (8 * (vl + 1)) true = true) (htw : t + 8 * (vl + 1) ≤ sp - 4424 ∨ sp + 88 ≤ t)
    (m120 : S.mem.readLE (sp - 120) 8 = vl + 1) (m16 : S.mem.readLE (sp + 16) 8 = vl)
    (m160 : S.mem.readLE (sp - 160) 8 = c) (m56 : S.mem.readLE (sp - 56) 8 = t)
    (m96 : S.mem.readLE (sp - 96) 8 = j) (m72 : S.mem.readLE (sp + 72) 8 = ul)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 subPt → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.regs 2 = BitVec.ofNat 64 (qhlOf j vl ul c) → S'.regs 6 = BitVec.ofNat 64 j →
      S'.regs 3 = BitVec.ofNat 64 t → S'.mem = S.mem.writeLE (t + 8 * vl) 8 c → S'.xmm = S.xmm →
      S'.fsBase = S.fsBase → S'.df = S.df → ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have e120 : S.mem.readLE ((S.regs 4).toNat + 104) 8 = vl + 1 := by
    rw [show (S.regs 4).toNat + 104 = sp - 120 by omega]; exact m120
  have e16 : S.mem.readLE ((S.regs 4).toNat + 240) 8 = vl := by rw [show (S.regs 4).toNat + 240 = sp + 16 by omega]; exact m16
  have e160 : S.mem.readLE ((S.regs 4).toNat + 64) 8 = c := by rw [show (S.regs 4).toNat + 64 = sp - 160 by omega]; exact m160
  have e56 : S.mem.readLE ((S.regs 4).toNat + 168) 8 = t := by rw [show (S.regs 4).toNat + 168 = sp - 56 by omega]; exact m56
  have e96 : S.mem.readLE ((S.regs 4).toNat + 128) 8 = j := by rw [show (S.regs 4).toNat + 128 = sp - 96 by omega]; exact m96
  have e72 : S.mem.readLE ((S.regs 4).toNat + 296) 8 = ul := by rw [show (S.regs 4).toNat + 296 = sp + 72 by omega]; exact m72
  have hti := toInt_add_lt j (vl + 1) (by omega)
  janus64_run [e120, e16, e160, e56, e96, e72] until [subPt]
  all_goals
    simp only [hti] at *
    refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl
    · janus64_simp
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; unfold qhlOf
      split <;> (apply BitVec.eq_of_toNat_eq; simp <;> omega)
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · show Arm64.Memory.writeLE S.mem (t + vl * 8) 8 _ = _; rw [Nat.mul_comm vl 8]
      all_goals (congr 1; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option linter.janusRenameI false in
theorem subRun (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b1 : Nat) (L1 : List (Nat × Nat)) (r : Nat) (Q : State → Prop) (S : State) (sp t vl j q up uc : Nat)
    (hpc : S.rip = BitVec.ofNat 64 subPt) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (hvb : vl + 4 ≤ 2 ^ 16) (hq1 : 2 ≤ q) (hq2 : q ≤ vl + 1) (hjq : j + q ≤ uc) (huc : uc < 2 ^ 40)
    (ht64 : t < 2 ^ 64) (hup : up + 8 * uc ≤ 2 ^ 48)
    (h2 : S.regs 2 = BitVec.ofNat 64 q) (h6 : S.regs 6 = BitVec.ofNat 64 j) (h3 : S.regs 3 = BitVec.ofNat 64 t)
    (m80 : S.mem.readLE (sp + 80) 8 = uc) (m64 : S.mem.readLE (sp + 64) 8 = up)
    (m64' : S.mem.readLE (sp - 64) 8 = vl + 1)
    (hzacc : S.mem.accessible (up + 8 * j) (8 * q) true = true) (htacc : S.mem.accessible t (8 * q) false = true)
    (hzt : Apart (up + 8 * j) (8 * q) t (8 * q))
    (hzw : up + 8 * j + 8 * q ≤ sp - 4424 ∨ sp + 88 ≤ up + 8 * j) (htw : t + 8 * q ≤ sp - 4424 ∨ sp + 88 ≤ t)
    (hzH : Held R L1 (up + 8 * j) (8 * q)) (hinv : R.inv b1 L1 (S.regs 14).toNat (view R.rt L1 S.mem))
    (hout : Outside (sp - 4424) (4424 + 88) R.rt)
    (hgw : Apart ((S.regs 14).toNat + 16) 8 (sp - 4424) (4424 + 88))
    (hzg : Apart (up + 8 * j) (8 * q) ((S.regs 14).toNat + 16) 8)
    (htl : TlsG S) (hlw : Apart (S.fsBase.toNat - 8) 8 (sp - 4424) (4424 + 88))
    (hzl : Apart (up + 8 * j) (8 * q) (S.fsBase.toNat - 8) 8)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 afterSub → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.xmm 15 = 0#128 → S'.fsBase = S.fsBase → S'.df = S.df →
      natVal S'.mem (up + 8 * j) q + natVal S.mem t q =
        natVal S.mem (up + 8 * j) q + 2 ^ (64 * q) * S'.mem.readLE (sp - 152) 8 →
      S'.mem.readLE (sp - 152) 8 = (if natVal S.mem (up + 8 * j) q < natVal S.mem t q then 1 else 0) →
      S'.mem.readLE (sp - 128) 8 = q → S'.mem.readLE (sp - 80) 8 = uc - j →
      S'.mem.readLE (sp - 48) 8 = up + 8 * j →
      MemFrame S.mem S'.mem [(sp - 232, sp - 144), (sp - 128, sp - 120), (sp - 80, sp - 72), (sp - 48, sp - 40),
        (up + 8 * j, up + 8 * j + 8 * q)] →
      ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have e80 : S.mem.readLE ((S.regs 4).toNat + 304) 8 = uc := by rw [show (S.regs 4).toNat + 304 = sp + 80 by omega]; exact m80
  have e64 : S.mem.readLE ((S.regs 4).toNat + 288) 8 = up := by rw [show (S.regs 4).toNat + 288 = sp + 64 by omega]; exact m64
  have e64' : S.mem.readLE ((S.regs 4).toNat + 160) 8 = vl + 1 := by
    rw [show (S.regs 4).toNat + 160 = sp - 64 by omega]; exact m64'
  have hmask : ((0#64 - (BitVec.ofNat 64 uc - BitVec.ofNat 64 j)).sshiftRight 63).toNat &&& j * 8 = j * 8 :=
    neg_sshr_land_lt _ _ _ (by omega) (by omega) (by omega)
  have hupm : up % 18446744073709551616 = up := Nat.mod_eq_of_lt (by omega)
  have hzx : up + 8 * j = up + 8 * j ∨ Apart (up + 8 * j) (8 * q) (up + 8 * j) (8 * q) := Or.inl rfl
  have hzt' : up + 8 * j = t ∨ Apart (up + 8 * j) (8 * q) t (8 * q) := Or.inr hzt
  have hzacc' : S.mem.accessible (up + 8 * j) (8 * q) false = true :=
    Janus.Arm64.Memory.accessible_read_of_write _ hzacc
  have hvw' := view_win hout L1
  have hfa := htl.addr
  obtain ⟨⟨hfb1, hfb2⟩, hfacc, hfg⟩ := htl
  have ez : up + 8 * j = j * 8 + up := by omega
  rw [ez] at hzt' hzH hzx hzacc hzacc' k
  unfold Apart at hzt hgw hzg hlw hzl
  janus64_run [h2, h6, h3, e80, e64, e64', hmask, hupm, hvw', hfa] until [afterSub] calls [subvv impl hap R b1 L1]
  rename_i _ _ _ _ _ m _ _ hv hc hfr _ _ _
  have rd : ∀ a, (a + 8 ≤ j * 8 + up ∨ j * 8 + up + 8 * q ≤ a) → (a + 8 ≤ sp - 152 ∨ sp - 144 ≤ a) →
      m.readLE a 8 = _ := fun a h1 h2 => hfr.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hfr' : MemFrame S.mem m [(sp - 232, sp - 144), (sp - 128, sp - 120), (sp - 80, sp - 72), (sp - 48, sp - 40),
      (j * 8 + up, j * 8 + up + 8 * q)] := by
    refine ⟨fun a n ho => ?_, fun a n v => ?_⟩
    · simp only [outside_cons, outside_nil, and_true] at ho
      obtain ⟨o1, o2, o3, o4, o5⟩ := ho
      rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · rw [hfr.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]
  have e152 : sp - 152 = (S.regs 4).toNat - 8 + 80 := by omega
  refine k _ ?_ ?_ ?_ ?_ ?_ rfl rfl (by rw [e152]; exact hv) (by rw [e152]; exact hc) ?_ ?_ ?_ hfr'
  · janus64_simp
  · simp only [setRegF_apply, regs0, regSP, Nat.reduceEqDiff, ↓reduceIte]; exact BitVec.sub_add_cancel _ _
  · simp only [setRegF_apply, regs0, regSP, regFP, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, regG, ↓reduceIte]
  · simp only [setXmmF, ↓reduceIte]
  · rw [rd _ (by omega) (by omega), show sp - 128 = (S.regs 4).toNat + 96 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  · rw [rd _ (by omega) (by omega), show sp - 80 = (S.regs 4).toNat + 144 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
  · rw [rd _ (by omega) (by omega), show sp - 48 = (S.regs 4).toNat + 176 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)

end FvModexp.Amd64.DivBasic
