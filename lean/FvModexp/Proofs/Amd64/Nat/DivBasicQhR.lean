import FvModexp.Proofs.Amd64.Nat.DivBasicRel
import FvModexp.Proofs.Amd64.Nat.DivBasicCallees
import FvModexp.Proofs.Amd64.Nat.DivBasicCorr
import FvModexp.Proofs.Common.AsmDivVW

set_option autoImplicit false

/-!
# `divBasic` (amd64): the runs of the `qhat` estimate on small contexts (agent top s23)

`estE`: head → `mulPt` when `ujn = vn1` (`qhat = _M`). `estD1`: head → after `CALL divWW`. `estD2`: → `ctest` (the
correction loop, DivBasicCorr). `estX`: `cexit` → `mulPt` (registers reloaded from the frame). Code map: DivBasicQh.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- head → `mulPt`, `ujn = vn1` -/
theorem estE (impl : List Amd64.Segment) (r : Nat) (Q : State → Prop) (S : State) (sp j vn1 : Nat)
    (hpc : S.rip = BitVec.ofNat 64 head) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48)
    (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true) (hr2 : S.regs 2 = BitVec.ofNat 64 j)
    (hj : j < 2 ^ 63) (hr8 : S.regs 8 = BitVec.ofNat 64 vn1) (hr11 : S.regs 11 = BitVec.ofNat 64 vn1)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 mulPt → (∀ i, i ≠ 8 → S'.regs i = S.regs i) →
      S'.regs 8 = BitVec.ofNat 64 (2 ^ 64 - 1) → S'.mem = S.mem.writeLE (sp - 96) 8 j → S'.xmm = S.xmm →
      S'.fsBase = S.fsBase → S'.df = S.df → ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have hjm : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
  have hj63 : (BitVec.ofNat 64 j).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]; omega
  janus64_run [hr2, hr8, hr11, hj63, hjm] until [mulPt]
  refine k _ ?gpc (fun i h => by simp only [setRegF_apply, h, if_false]) (by simp only [setRegF_apply, ↓reduceIte])
    ?gm rfl rfl rfl
  case gpc => janus64_simp
  case gm => show _ = _; rw [show sp - 96 = (S.regs 4).toNat + 128 by omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `cexit` → `mulPt`: the head registers reloaded (`CX = n`, `DX = j`, `BX = len qhatv`, `SI = v.ptr`,
`DI = cap qhatv`, `R10 = qhatv.ptr`, `R11 = vn1`, `R8 = qhat`, `AX = rec`) -/
theorem estX (impl : List Amd64.Segment) (r : Nat) (Q : State → Prop) (S : State) (sp : Nat)
    (hpc : S.rip = BitVec.ofNat 64 cexit) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (a3 a6 a7 a10 a0 : Nat)
    (m3 : S.mem.readLE (sp - 120) 8 = a3) (m6 : S.mem.readLE (sp + 8) 8 = a6) (m7 : S.mem.readLE (sp - 64) 8 = a7)
    (m10 : S.mem.readLE (sp - 56) 8 = a10) (m0 : S.mem.readLE (sp - 136) 8 = a0)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 mulPt → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.regs 1 = S.regs 10 → S'.regs 2 = S.regs 7 → S'.regs 3 = BitVec.ofNat 64 a3 →
      S'.regs 6 = BitVec.ofNat 64 a6 → S'.regs 7 = BitVec.ofNat 64 a7 → S'.regs 10 = BitVec.ofNat 64 a10 →
      S'.regs 11 = S.regs 13 → S'.regs 8 = S.regs 0 → S'.regs 0 = BitVec.ofNat 64 a0 → S'.mem = S.mem →
      S'.xmm = S.xmm → S'.fsBase = S.fsBase → S'.df = S.df → ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have e3 : S.mem.readLE ((S.regs 4).toNat + 104) 8 = a3 := by rw [show (S.regs 4).toNat + 104 = sp - 120 by omega]; exact m3
  have e6 : S.mem.readLE ((S.regs 4).toNat + 232) 8 = a6 := by rw [show (S.regs 4).toNat + 232 = sp + 8 by omega]; exact m6
  have e7 : S.mem.readLE ((S.regs 4).toNat + 160) 8 = a7 := by rw [show (S.regs 4).toNat + 160 = sp - 64 by omega]; exact m7
  have e10 : S.mem.readLE ((S.regs 4).toNat + 168) 8 = a10 := by
    rw [show (S.regs 4).toNat + 168 = sp - 56 by omega]; exact m10
  have e0 : S.mem.readLE ((S.regs 4).toNat + 88) 8 = a0 := by rw [show (S.regs 4).toNat + 88 = sp - 136 by omega]; exact m0
  janus64_run [e3, e6, e7, e10, e0] until [mulPt]
  refine k _ ?gpc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl
  case gpc => janus64_simp
  all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option linter.janusRenameI false in
/-- head → after `CALL divWW` (`ujn ≠ vn1`): `RAX, RBX = (ujn·B + u[j+n-1]) /% vn1` -/
theorem estD1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (r : Nat)
    (Q : State → Prop) (S : State) (sp j vl ul up vn1 ujn un1 : Nat)
    (hpc : S.rip = BitVec.ofNat 64 head) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (huacc : S.mem.accessible up (8 * ul) false = true) (hu48 : up + 8 * ul ≤ 2 ^ 48)
    (huw : up + 8 * ul ≤ sp - 4424 ∨ sp + 88 ≤ up)
    (hr0 : S.regs 0 = BitVec.ofNat 64 (AsmDiv.recipWord vn1)) (hr1 : S.regs 1 = BitVec.ofNat 64 vl)
    (hr2 : S.regs 2 = BitVec.ofNat 64 j) (hr8 : S.regs 8 = BitVec.ofNat 64 ujn)
    (hr11 : S.regs 11 = BitVec.ofNat 64 vn1) (hv1 : 1 ≤ vl) (hj : j + vl ≤ ul) (hul : ul < 2 ^ 40)
    (hlt : ujn < vn1) (hvn1B : vn1 < 2 ^ 64)
    (m72 : S.mem.readLE (sp + 72) 8 = ul) (m64 : S.mem.readLE (sp + 64) 8 = up)
    (mu : S.mem.readLE (up + 8 * (j + vl - 1)) 8 = un1)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 (callWW + 5) → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.regs 0 = BitVec.ofNat 64 ((ujn * 2 ^ 64 + un1) / vn1) →
      S'.regs 3 = BitVec.ofNat 64 ((ujn * 2 ^ 64 + un1) % vn1) →
      MemFrame ((S.mem.writeLE (sp - 96) 8 j).writeLE (sp - 232) 8 (callWW + 5)) S'.mem [] →
      S'.xmm = S.xmm → S'.fsBase = S.fsBase → S'.df = S.df → ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have hjm : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
  have hj63 : (BitVec.ofNat 64 j).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]; omega
  have hne : (BitVec.ofNat 64 ujn = BitVec.ofNat 64 vn1) = False := by
    simp only [eq_iff_iff, iff_false]; intro h
    have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have e72 : S.mem.readLE ((S.regs 4).toNat + 296) 8 = ul := by rw [show (S.regs 4).toNat + 296 = sp + 72 by omega]; exact m72
  have e64 : S.mem.readLE ((S.regs 4).toNat + 288) 8 = up := by rw [show (S.regs 4).toNat + 288 = sp + 64 by omega]; exact m64
  have hu1 : S.mem.readLE (up + (vl + j - 1) * 8) 8 = un1 := by
    rw [show (vl + j - 1) * 8 = 8 * (j + vl - 1) by omega]; exact mu
  have hrcm : AsmDiv.recipWord vn1 % 18446744073709551616 = AsmDiv.recipWord vn1 :=
    Nat.mod_eq_of_lt (FvModexp.AsmDivVW.recipWord_lt vn1 (by omega) hvn1B)
  janus64_run [hr0, hr1, hr2, hr8, hr11, hj63, hjm, hne, e72, e64, hu1, hrcm] until [callWW + 5] calls [divww impl hap]
  rename_i hb0 hpcw hspw hr0w hr3w h5w h14w _ _ _ hFw hxw hfsw hdfw
  clear hb0 hbr
  have hidx : (vl + (18446744073709551615 + j) % 18446744073709551616) % 18446744073709551616 = j + vl - 1 := by omega
  have hrd : S.mem.readLE (up + (j + vl - 1) * 8) 8 = un1 := by
    rw [show (j + vl - 1) * 8 = 8 * (j + vl - 1) by omega]; exact mu
  have hun1 : un1 < 2 ^ 64 := mu ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hidx, hrd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvn1B,
    Nat.mod_eq_of_lt (show ujn < 2 ^ 64 by omega), Nat.mod_eq_of_lt hun1]
    at hpcw hspw hr0w hr3w h5w h14w
  refine k s' ?_ (by rw [hspw]; exact BitVec.sub_add_cancel _ _) h5w h14w hr0w hr3w ?_ hxw hfsw hdfw
  · rw [hpcw]; janus64_simp
  · rw [show (S.regs 4).toNat + 128 = sp - 96 by omega, show (S.regs 4).toNat - 8 = sp - 232 by omega,
      show (6222798 : Nat) = callWW + 5 from by decide] at hFw
    exact hFw

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option linter.janusRenameI false in
/-- after `divWW` → `ctest`: `x1, x2 = mulWW(qhat, vn2)`, `ujn2 = u[j+n-2]`, `R13 = vn1` -/
theorem estD2 (impl : List Amd64.Segment) (r : Nat) (Q : State → Prop) (S : State)
    (sp j vl vp ul up vn1 vn2 un2 q : Nat)
    (hpc : S.rip = BitVec.ofNat 64 (callWW + 5)) (hsp : (S.regs 4).toNat + 224 = sp) (hsp0 : 4424 ≤ sp)
    (hsp1 : sp + 88 ≤ 2 ^ 48) (hwacc : S.mem.accessible (sp - 4424) (4424 + 88) true = true)
    (huacc : S.mem.accessible up (8 * ul) false = true) (hu48 : up + 8 * ul ≤ 2 ^ 48)
    (hvacc : S.mem.accessible vp (8 * vl) false = true) (hv48 : vp + 8 * vl ≤ 2 ^ 48)
    (hr0 : S.regs 0 = BitVec.ofNat 64 q) (hq : q < 2 ^ 64) (hv2 : 2 ≤ vl) (hj : j + vl ≤ ul) (hul : ul < 2 ^ 40)
    (m16 : S.mem.readLE (sp + 16) 8 = vl) (m8 : S.mem.readLE (sp + 8) 8 = vp) (m96 : S.mem.readLE (sp - 96) 8 = j)
    (m72 : S.mem.readLE (sp + 72) 8 = ul) (m64 : S.mem.readLE (sp + 64) 8 = up)
    (mn1 : S.mem.readLE (sp - 72) 8 = vn1)
    (mv2 : S.mem.readLE (vp + 8 * (vl - 2)) 8 = vn2) (mu2 : S.mem.readLE (up + 8 * (j + vl - 2)) 8 = un2)
    (k : ∀ S' : State, S'.rip = BitVec.ofNat 64 ctest → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 →
      S'.regs 14 = S.regs 14 → S'.regs 3 = S.regs 3 → S'.regs 9 = BitVec.ofNat 64 q →
      S'.regs 2 = BitVec.ofNat 64 (q * vn2 / 2 ^ 64) → S'.regs 0 = BitVec.ofNat 64 (q * vn2 % 2 ^ 64) →
      S'.regs 6 = BitVec.ofNat 64 vn2 → S'.regs 8 = BitVec.ofNat 64 un2 → S'.regs 13 = BitVec.ofNat 64 vn1 →
      S'.regs 10 = BitVec.ofNat 64 vl → S'.regs 7 = BitVec.ofNat 64 j → S'.mem = S.mem →
      S'.xmm = S.xmm → S'.fsBase = S.fsBase → S'.df = S.df → ReachesRet (LibDivBasic.program.link impl) r S' Q) :
    ReachesRet (LibDivBasic.program.link impl) r S Q := by
  have e16 : S.mem.readLE ((S.regs 4).toNat + 240) 8 = vl := by rw [show (S.regs 4).toNat + 240 = sp + 16 by omega]; exact m16
  have e8 : S.mem.readLE ((S.regs 4).toNat + 232) 8 = vp := by rw [show (S.regs 4).toNat + 232 = sp + 8 by omega]; exact m8
  have e96 : S.mem.readLE ((S.regs 4).toNat + 128) 8 = j := by rw [show (S.regs 4).toNat + 128 = sp - 96 by omega]; exact m96
  have e72 : S.mem.readLE ((S.regs 4).toNat + 296) 8 = ul := by rw [show (S.regs 4).toNat + 296 = sp + 72 by omega]; exact m72
  have e64 : S.mem.readLE ((S.regs 4).toNat + 288) 8 = up := by rw [show (S.regs 4).toNat + 288 = sp + 64 by omega]; exact m64
  have en1 : S.mem.readLE ((S.regs 4).toNat + 152) 8 = vn1 := by
    rw [show (S.regs 4).toNat + 152 = sp - 72 by omega]; exact mn1
  have ev2 : S.mem.readLE (vp + vl * 8 - 16) 8 = vn2 := by rw [show vp + vl * 8 - 16 = vp + 8 * (vl - 2) by omega]; exact mv2
  janus64_run [hr0, e16, e8, e96, e72, e64, en1, ev2] until [ctest]
  rename_i hb0; clear hb0 hbr
  have hvn2 : vn2 < 2 ^ 64 := mv2 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have eu2 : S.mem.readLE (up + (j + (vl - 2)) * 8) 8 = un2 := by
    rw [show (j + (vl - 2)) * 8 = 8 * (j + vl - 2) by omega]; exact mu2
  refine k _ ?gpc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl
  case gpc => janus64_simp
  all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.mod_eq_of_lt hvn2, eu2, Nat.mul_comm vn2 q]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]

end FvModexp.Amd64.DivBasic
