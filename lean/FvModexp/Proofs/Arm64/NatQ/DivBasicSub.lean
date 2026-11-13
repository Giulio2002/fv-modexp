import FvModexp.Proofs.Arm64.NatQ.DivBasicSubA
import FvModexp.Proofs.Arm64.NatQ.DivBasicSubB

set_option autoImplicit false
/-! (Q-form copy of Arm64/Nat/DivBasicSub.lean, TIGHT COSTS, asm s38)
# `divBasic` (arm64): `qhatv[n] = c`, `qhl`, `c := subVV(u[j:j+qhl], u[j:j+qhl], qhatv[:qhl])` (natdiv.go:703-709),
`+0x194 → +0x230`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Q.DivBasic
open FvModexp.Arm64.DivBasic
variable {H : Nat}

theorem sub1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b H L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qhat c : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S afterVww j)
    (hqh : S.mem.readLE (s.sp.toNat - 96) 8 = qhat) (hc : S.mem.readLE (s.sp.toNat - 168) 8 = c)
    (hj : j + vl ≤ ul) (hcz : ul = j + vl → c = 0) (Q : State → Prop)
    (k : ∀ S', Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' afterSub j →
      S'.mem.readLE (s.sp.toNat - 96) 8 = qhat → S'.mem.readLE (s.sp.toNat - 120) 8 = qhlOf j vl ul c →
      S'.mem.readLE (s.sp.toNat - 48) 8 = up + 8 * j → S'.mem.readLE (s.sp.toNat - 64) 8 = uc - j →
      MemFrame S.mem S'.mem (scr s ++ [(t + 8 * vl, t + 8 * vl + 8), (up + 8 * j, up + 8 * j + 8 * qhlOf j vl ul c)]) →
      S'.mem.readLE (t + 8 * vl) 8 = c →
      natVal S'.mem (up + 8 * j) (qhlOf j vl ul c) + natVal S'.mem t (qhlOf j vl ul c) =
        natVal S.mem (up + 8 * j) (qhlOf j vl ul c) +
          2 ^ (64 * qhlOf j vl ul c) * S'.mem.readLE (s.sp.toNat - 160) 8 →
      S'.mem.readLE (s.sp.toNat - 160) 8 ≤ 1 →
      ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (s.regs 30) S Q := by
  by_cases hq1 : ul < j + (vl + 1) ∧ c = 0
  · have hqv : qhlOf j vl ul c = vl := by simp only [qhlOf, hq1, and_self, ↓reduceIte]
    rw [hqv] at k
    exact subA impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S j qhat c hB hqh hc hj hq1.1 hq1.2 Q k
  · have hqv : qhlOf j vl ul c = vl + 1 := by simp only [qhlOf, hq1, ↓reduceIte]
    rw [hqv] at k
    have hq1' : j + (vl + 1) ≤ ul := by
      by_cases hcc : c = 0
      · have : ¬ ul < j + (vl + 1) := fun h => hq1 ⟨h, hcc⟩
        omega
      · have := mt hcz hcc; omega
    exact subB impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S j qhat c hB hqh hc hj hq1' Q k

end FvModexp.Arm64.Q.DivBasic
