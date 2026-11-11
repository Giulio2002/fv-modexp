import FvModexp.Proofs.Arm64.Nat.DivBasicRec
import FvModexp.Proofs.Arm64.Nat.DivBasicCorr

/-!
# `divBasic` (arm64): the loop head and the estimate `qhat` (natdiv.go:667-697)

`est`: from the head with `j ≥ 0` (`R1 = j`, `R2 = ujn`) to `+0x160` (`R2 = qhat`): `ujn == vn1` → `qhat = _M`; else
`qhat, rhat := divWW(ujn, u[j+n-1], vn1, rec)`, `x1, x2 := mulWW(qhat, vn2)`, the correction loop (`corr`). The value is
`Mdl.qhatEst` (by `Mdl.qhatEst_eq`). Writes only the slots `j` (`SP-80`) and `j+n` (`SP-64`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic

/-- `qhatv[0:n] = mulAddVWW(…)` setup point -/
abbrev mulPt : Nat := segAddr Extracted.program fn + 0x160

/-- the facts at `mulPt` (state `S'`), `S` the head state -/
structure AtMul (s S S' : State) (j qhat : Nat) : Prop where
  pc : S'.pc = BitVec.ofNat 64 mulPt
  sp : S'.sp = s.sp - 240#64
  r28 : S'.regs 28 = s.regs 28
  r29 : S'.regs 29 = s.sp - 248#64
  r18 : S'.regs 18 = s.regs 18
  r2 : S'.regs 2 = BitVec.ofNat 64 qhat
  fr : MemFrame S.mem S'.mem [(s.sp.toNat - 80, s.sp.toNat - 72), (s.sp.toNat - 64, s.sp.toNat - 56)]
  jj : S'.mem.readLE (s.sp.toNat - 80) 8 = j

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem est (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (S : State) (j ujn : Nat)
    (hH : Hd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S j ujn)
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
  have hj63 : (BitVec.ofNat 64 j).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hjm : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega)
  have hqe := Mdl.qhatEst_eq vn1 vn2 ujn un1 un2 hvtop hvn1B hle hun1B
  rw [hqe] at k
  by_cases hq : ujn = vn1
  · subst hq
    rw [if_neg (by simp)] at k
    janus_run [hr0, hr1, hr2, m4, hj63, hjm] until [mulPt]
    refine k _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?fr, ?jj⟩
    case fr => janus_frame
    case jj => sorry
    all_goals sorry
  · sorry

end FvModexp.Arm64.DivBasic
