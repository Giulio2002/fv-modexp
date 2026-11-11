import FvModexp.Proofs.Arm64.Nat.DivBasicSubFin
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.DivmcMem

/-!
# `divBasic` (arm64): `qhatv[n] = c`, `qhl`, `c := subVV(u[j:j+qhl], u[j:j+qhl], qhatv[:qhl])` (natdiv.go:703-709),
`+0x194 → +0x230`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.DivBasic

abbrev afterSub : Nat := segAddr Extracted.program fn + 0x230

/-- `qhl` (natdiv.go:705-708) -/
@[reducible] def qhlOf (j vl ul c : Nat) : Nat := if ul < j + (vl + 1) ∧ c = 0 then vl else vl + 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem subA (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qhat c : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S afterVww j)
    (hqh : S.mem.readLE (s.sp.toNat - 96) 8 = qhat) (hc : S.mem.readLE (s.sp.toNat - 168) 8 = c)
    (hj : j + vl ≤ ul) (hq1a : ul < j + (vl + 1)) (hq1b : c = 0) (Q : State → Prop)
    (k : ∀ S', Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' afterSub j →
      S'.mem.readLE (s.sp.toNat - 96) 8 = qhat → S'.mem.readLE (s.sp.toNat - 120) 8 = vl →
      S'.mem.readLE (s.sp.toNat - 48) 8 = up + 8 * j → S'.mem.readLE (s.sp.toNat - 64) 8 = uc - j →
      MemFrame S.mem S'.mem (scr s ++ [(t + 8 * vl, t + 8 * vl + 8), (up + 8 * j, up + 8 * j + 8 * vl)]) →
      S'.mem.readLE (t + 8 * vl) 8 = c →
      natVal S'.mem (up + 8 * j) (vl) + natVal S'.mem t (vl) =
        natVal S.mem (up + 8 * j) (vl) +
          2 ^ (64 * vl) * S'.mem.readLE (s.sp.toNat - 160) 8 →
      S'.mem.readLE (s.sp.toNat - 160) 8 ≤ 1 →
      ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S Q := by
  obtain ⟨hpc, hsp, h28, h29, h18, hM, hjj⟩ := hB
  subst hq1b
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hvb := hl.vb; have hv48 := hl.v48
  have ht48 := hl.t48; have hu48 := hl.u48
  have hulc := hE.pre.ulc; have hub := hE.pre.ub
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hE.pre.ce
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible (s.sp.toNat - 4464) (4464 + 88) true = true := by rw [hMacc]; exact hw
  have htacc : S.mem.accessible t (8 * (vl + 1)) true = true := by rw [hMacc]; exact hE.scr.acc
  have huacc : S.mem.accessible up (8 * ul) true = true := by rw [hMacc]; exact hE.pre.uacc
  have htH : Held R L1 (t + vl * 8) 8 := hl.theld.sub (by omega) (by omega)
  have hvt := view_writeLE_held htH
  have hinv := hM.inv
  have m7 := hM.hl; have m8 := hM.hc; have s8 := hM.s8; have tp := hM.tp; have s4 := hM.s4; have s5 := hM.s5
  have s6 := hM.s6
  have hvw := view_win hout L1
  have htw := hl.tw; have huw := hl.uw; have htu := hl.tu
  have hucB : uc < 2 ^ 40 := hE.pre.ucb
  have hmask := sliceMask_lt j (BitVec.ofNat 64 j) (BitVec.ofNat 64 uc) (by simp; omega) (by simp; omega) (by omega)
  have hucm : uc % 18446744073709551616 = uc := Nat.mod_eq_of_lt (by omega)
  have huH : Held R L1 up (8 * ul) := hE.ext.held hE.pre.uh
  have hug := hl.ug
  have hfacts : ∀ n, j + n ≤ ul → n ≤ vl + 1 → (up + 8 * j = t ∨ Apart (up + 8 * j) (8 * n) t (8 * n)) ∧
      (InRanges (up + 8 * j) (8 * n) L1 ∨ Outside (up + 8 * j) (8 * n) R.rt) ∧
      (up + 8 * j + 8 * n ≤ (s.regs 28).toNat + 16 ∨ (s.regs 28).toNat + 16 + 8 ≤ up + 8 * j) := by
    intro n h1 h2
    refine ⟨Or.inr (by unfold Apart; omega), huH.sub (by omega) (by omega), by omega⟩
  obtain ⟨f1, f2, f3⟩ := hfacts vl (by omega) (by omega)
  janus_run [hqh, hc, hjj, m7, m8, s8, tp, s4, s5, s6, hucm, hmask, hvt, hvw, BitVec.msb_eq_decide] until [afterSub]
    calls [subvv impl hap R b1 L1]
  rename_i w hval hbw hFw hinvw hgd
  have e80 : s.sp.toNat - 240 + 80 = s.sp.toNat - 160 := by omega
  have e88 : s.sp.toNat - 240 + 88 = s.sp.toNat - 152 := by omega
  rw [e80] at hval hbw; rw [e80, e88] at hFw
  have hf := finS hE hM hjj hqh (q := vl) (by omega) (Or.inl rfl) (by omega) (by omega) hucB hFw
  have hty := hf.ty
  refine k _ ⟨?_, ?_, ?_, ?_, ?_, hf.mem, hf.jj⟩ hf.qh hf.ql hf.uj hf.cj hf.fr hf.tc ?q6 ?q7
  case q7 => show w.readLE _ _ ≤ 1; rw [hbw]; split <;> omega
  case q6 =>
    show natVal w _ _ + natVal w t _ = _
    rw [hty, Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hval
  all_goals janus_simp

end FvModexp.Arm64.DivBasic
