import FvModexp.Proofs.Arm64.NatQ.DivBasicRel
import FvModexp.Proofs.Arm64.NatQ.DivBasicCorr

set_option autoImplicit false
/-! (Q-form copy of Arm64/Nat/DivBasicQh.lean, TIGHT COSTS, asm s38)
# `divBasic` (arm64): the loop head and the estimate `qhat` (natdiv.go:667-697)

`est`: from the head with `j ≥ 0` (`R1 = j`, `R2 = ujn`) to `+0x160` (`R2 = qhat`): `ujn == vn1` → `qhat = _M`; else
`qhat, rhat := divWW(ujn, u[j+n-1], vn1, rec)`, `x1, x2 := mulWW(qhat, vn2)`, the correction loop (`corr`). The value is
`Mdl.qhatEst` (by `Mdl.qhatEst_eq`). Writes only the slots `j` (`SP-80`) and `j+n` (`SP-64`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.DivBasic
open FvModexp.Arm64.DivBasic
variable {H : Nat}




set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem est (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State) (j ujn : Nat)
    (hH : Hd R b H L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S j ujn)
    (hj : j + vl ≤ ul) (hle : ujn ≤ s.mem.readLE (vp + 8 * (vl - 1)) 8) (Q : State → Prop)
    (k : ∀ S', AtMul s S S' j (Mdl.qhatEst (s.mem.readLE (vp + 8 * (vl - 1)) 8) (s.mem.readLE (vp + 8 * (vl - 2)) 8)
      (Mdl.reciprocalWord (s.mem.readLE (vp + 8 * (vl - 1)) 8)) ujn (S.mem.readLE (up + 8 * (j + vl - 1)) 8)
      (S.mem.readLE (up + 8 * (j + vl - 2)) 8)) → ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S Q := by
  obtain ⟨hpc, hsp, h28, h29, h18, hr0, hr1, hr2, hE, hM⟩ := hH
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hvb := hl.vb; have hv48 := hl.v48
  have hu48 := hl.u48
  have hub := hE.pre.ub
  have hvtop := hE.pre.vtop
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩ := hE.pre.ce
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [hMacc]; exact hw
  have huacc : S.mem.accessible up (8 * ul) false = true := by
    rw [hMacc]; exact Memory.accessible_weaken _ hE.pre.uacc
  have hvacc : S.mem.accessible vp (8 * vl) false = true := by rw [hMacc]; exact hE.pre.vacc
  have m4 := hM.vn1; have m5 := hM.rw; have s4 := hM.s4; have s5 := hM.s5; have s7 := hM.s7; have s8 := hM.s8
  generalize hvn1 : s.mem.readLE (vp + 8 * (vl - 1)) 8 = vn1 at *
  have hvn1B : vn1 < 2 ^ 64 := by rw [← hvn1]; exact Memory.readLE_lt _ _ _
  have hvn2 : S.mem.readLE (vp + (vl - 2) * 8) 8 = s.mem.readLE (vp + 8 * (vl - 2)) 8 := by
    rw [Nat.mul_comm]; exact hM.vs _ _ (by omega) (by omega)
  generalize hvn2' : s.mem.readLE (vp + 8 * (vl - 2)) 8 = vn2 at *
  have hvn2B : vn2 < 2 ^ 64 := by rw [← hvn2']; exact Memory.readLE_lt _ _ _
  have hu1 : S.mem.readLE (up + (j + vl - 1) * 8) 8 = S.mem.readLE (up + 8 * (j + vl - 1)) 8 := by rw [Nat.mul_comm]
  have hu2 : S.mem.readLE (up + (j + vl - 2) * 8) 8 = S.mem.readLE (up + 8 * (j + vl - 2)) 8 := by rw [Nat.mul_comm]
  generalize hun1 : S.mem.readLE (up + 8 * (j + vl - 1)) 8 = un1 at *
  generalize hun2 : S.mem.readLE (up + 8 * (j + vl - 2)) 8 = un2 at *
  have hun1B : un1 < 2 ^ 64 := by rw [← hun1]; exact Memory.readLE_lt _ _ _
  have hun2B : un2 < 2 ^ 64 := by rw [← hun2]; exact Memory.readLE_lt _ _ _
  have hujnB : ujn < 2 ^ 64 := by omega
  have hj63 : (BitVec.ofNat 64 j).getLsbD 63 = false := by
    rw [BitVec.getLsbD_ofNat]; simp only [Nat.reduceLT, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (by omega)
  have hjm : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
  have hqe := Mdl.qhatEst_eq vn1 vn2 ujn un1 un2 hvtop hvn1B hle hun1B
  rw [hqe] at k
  by_cases hq : ujn = vn1
  · subst hq
    simp only [ne_eq, not_true_eq_false, ↓reduceIte] at k
    janus_run [hr0, hr1, hr2, m4, hj63, hjm] until [mulPt]
    refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?fr, ?jj⟩
    case fr => janus_frame
    case jj => simp only [Memory.readLE_writeLE_self]; omega
    all_goals try (janus_simp; done)
  · have hlt : ujn < vn1 := by omega
    simp only [ne_eq, hq, not_false_eq_true, ↓reduceIte] at k
    have s4 := hM.s4; have s5 := hM.s5; have s7 := hM.s7; have s8 := hM.s8
    have hrcm : AsmDiv.recipWord vn1 % 18446744073709551616 = AsmDiv.recipWord vn1 :=
      Nat.mod_eq_of_lt (FvModexp.AsmDivVW.recipWord_lt vn1 (by omega) hvn1B)
    janus_run [hr0, hr1, hr2, m4, hj63, hjm, hu1, hu2, hvn2, s4, s5, s7, s8, hrcm] until [callWW + 4]
      calls [divww impl hap]
    rename_i hpcw hspw hr0w hr1w h18w h28w h29w hFw
    have hvw := hl.vw; have huw := hl.uw
    have hW : ∀ a n, (a + n ≤ s.sp.toNat - 80 ∨ s.sp.toNat - 72 ≤ a) → (a + n ≤ s.sp.toNat - 64 ∨ s.sp.toNat - 56 ≤ a) →
        ((S.mem.writeLE (s.sp.toNat - 80) 8 j).writeLE (s.sp.toNat - 64) 8 (vl + j)).readLE a n = S.mem.readLE a n :=
      fun a n h1 h2 => by
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have eu1 : ((S.mem.writeLE (s.sp.toNat - 80) 8 j).writeLE (s.sp.toNat - 64) 8 (vl + j)).readLE
        (up + 8 * (vl + j - 1)) 8 = un1 := by
      rw [hW _ _ (by omega) (by omega), ← hun1, show vl + j - 1 = j + vl - 1 by omega]
    rw [eu1] at hpcw hspw hr0w hr1w h18w h28w h29w
    have kw : ∀ a n, s'.mem.readLE a n =
        ((S.mem.writeLE (s.sp.toNat - 80) 8 j).writeLE (s.sp.toNat - 64) 8 (vl + j)).readLE a n :=
      fun a n => hFw.readLE a n (by simp)
    have kacc : ∀ a n v, s'.mem.accessible a n v = S.mem.accessible a n v := fun a n v => by
      rw [hFw.accessible]; simp only [Memory.accessible_writeLE]
    have w72 : s'.mem.readLE (s.sp.toNat + 72) 8 = vl := by rw [kw, hW _ _ (by omega) (by omega), s8]
    have w48 : s'.mem.readLE (s.sp.toNat + 48) 8 = ul := by rw [kw, hW _ _ (by omega) (by omega), s5]
    have w40 : s'.mem.readLE (s.sp.toNat + 40) 8 = up := by rw [kw, hW _ _ (by omega) (by omega), s4]
    have w64 : s'.mem.readLE (s.sp.toNat + 64) 8 = vp := by rw [kw, hW _ _ (by omega) (by omega), s7]
    have w136 : s'.mem.readLE (s.sp.toNat - 136) 8 = vn1 := by
      rw [kw, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), m4]
    have wjn : s'.mem.readLE (s.sp.toNat - 64) 8 = vl + j := by
      rw [kw, Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
    have wv2 : s'.mem.readLE (vp + (vl - 2) * 8) 8 = vn2 := by rw [kw, hW _ _ (by omega) (by omega), hvn2]
    have wu2 : s'.mem.readLE (up + (vl + j - 2) * 8) 8 = un2 := by
      rw [kw, hW _ _ (by omega) (by omega), ← hun2, Nat.mul_comm, show vl + j - 2 = j + vl - 2 by omega]
    have hwacc' : s'.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [kacc]; exact hwacc
    have huacc' : s'.mem.accessible up (8 * ul) false = true := by rw [kacc]; exact huacc
    have hvacc' : s'.mem.accessible vp (8 * vl) false = true := by rw [kacc]; exact hvacc
    have wj : s'.mem.readLE (s.sp.toNat - 80) 8 = j := by
      rw [kw, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]; exact hjm
    have w128 : s'.mem.readLE (s.sp.toNat - 128) 8 = AsmDiv.recipWord vn1 := by
      rw [kw, hW _ _ (by omega) (by omega), m5]
    have hfr : MemFrame S.mem s'.mem [(s.sp.toNat - 80, s.sp.toNat - 72), (s.sp.toNat - 64, s.sp.toNat - 56)] :=
      ⟨fun a n h => by
        simp only [outside_cons, outside_nil, and_true] at h
        rw [kw, hW a n h.1 h.2], fun a n v => kacc a n v⟩
    clear kw
    janus_run [w72, w48, w40, w64, w136, wjn, wv2, wu2] until [ctest]
    have e2 : S.mem.readLE (vp + 8 * (vl - 2)) 8 = vn2 := by rw [← hvn2, Nat.mul_comm]
    have e3 : S.mem.readLE (up + 8 * (vl + j - 2)) 8 = un2 := by
      rw [← hun2, show vl + j - 2 = j + vl - 2 by omega]
    rw [e2, e3]
    have hq0 : (ujn * 2 ^ 64 + un1) / vn1 < 2 ^ 64 := by
      apply Nat.div_lt_of_lt_mul
      have : (ujn + 1) * 2 ^ 64 ≤ vn1 * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      rw [Nat.mul_comm]; omega
    have hr0 : (ujn * 2 ^ 64 + un1) % vn1 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
    have hx1 : (ujn * 2 ^ 64 + un1) / vn1 * vn2 / 2 ^ 64 < 2 ^ 64 :=
      Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_le hq0 (by omega) (by omega))
    have hx2 : (ujn * 2 ^ 64 + un1) / vn1 * vn2 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
    have hq0' : (ujn * 18446744073709551616 + un1) / vn1 < 2 ^ 64 := hq0
    refine corr impl (s.regs 30) Q vn1 vn2 un2 (by omega) hvn1B hvn2B hun2B (2 ^ 64) _ _ _ _ _ ?gpc ?g0 ?g1 ?g7 ?g6
      ?g3 ?g5 ?g10 hq0 hr0 hx1 hx2 (by omega) ?gk
    case gk =>
      intro S2 hp e0 e10 em es e28 e29 e18
      have wj' : S2.mem.readLE (s.sp.toNat - 80) 8 = j := by rw [em]; exact wj
      have w128' : S2.mem.readLE (s.sp.toNat - 128) 8 = AsmDiv.recipWord vn1 := by rw [em]; exact w128
      have hwacc2 : S2.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [em]; exact hwacc'
      janus_run [e0, e10, es, e28, e29, e18, wj', w128'] until [mulPt]
      refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?fr, ?jj⟩
      case fr => exact hfr
      case jj => exact wj
      all_goals janus_simp
    case gpc => janus_simp
    all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    case g0 =>
      rw [hr0w]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hujnB,
        Nat.mod_eq_of_lt hun1B, Nat.mod_eq_of_lt hvn1B, Nat.reducePow]
    case g1 =>
      rw [hr1w]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hujnB,
        Nat.mod_eq_of_lt hun1B, Nat.mod_eq_of_lt hvn1B, Nat.reducePow]
    case g7 => rw [bv_umulh _ _ hvn2B hq0']
    case g6 => rw [bv_mul _ _ hq0', Nat.mod_eq_of_lt hvn2B]

end FvModexp.Arm64.Q.DivBasic
