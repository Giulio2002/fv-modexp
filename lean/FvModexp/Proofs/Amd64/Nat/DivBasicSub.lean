import FvModexp.Proofs.Amd64.Nat.DivBasicMemF
import FvModexp.Proofs.Amd64.Nat.DivBasicSubR

set_option autoImplicit false

/-!
# `divBasic` (amd64): `qhatv[n] = c`, `qhl`, `c := subVV(u[j:j+qhl], u[j:], qhatv[:qhl])` (natdiv.go:703-709),
`afterVww = +0x2bf → afterSub = +0x3bc`

The runs are DivBasicSubR's `subQ` (the store `qhatv[n] = c` and `qhl`) and `subRun` (the `subVV.abi0` call).
The twin of `Arm64/Nat/DivBasicSub.lean` (`qhl` spilled at `RSP-128`, the borrow at `RSP-152`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.DivBasic

theorem qhl_facts (j vl ul c : Nat) (hv2 : 2 ≤ vl) (hj : j + vl ≤ ul) (hcz : ul = j + vl → c = 0) :
    2 ≤ qhlOf j vl ul c ∧ qhlOf j vl ul c ≤ vl + 1 ∧ vl ≤ qhlOf j vl ul c ∧ j + qhlOf j vl ul c ≤ ul := by
  unfold qhlOf; split
  · omega
  · rename_i h
    by_cases h1 : ul < j + (vl + 1)
    · exact absurd ⟨h1, hcz (by omega)⟩ h
    · omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem sub1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (S : State) (j qhat c : Nat) (hB : Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S afterVww j)
    (hqh : S.mem.readLE ((s.regs 4).toNat - 112) 8 = qhat) (hc : S.mem.readLE ((s.regs 4).toNat - 160) 8 = c)
    (hj : j + vl ≤ ul) (hcz : ul = j + vl → c = 0) (Q : State → Prop)
    (k : ∀ S', Bd R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' afterSub j →
      S'.mem.readLE ((s.regs 4).toNat - 112) 8 = qhat →
      S'.mem.readLE ((s.regs 4).toNat - 128) 8 = qhlOf j vl ul c →
      S'.mem.readLE ((s.regs 4).toNat - 48) 8 = up + 8 * j → S'.mem.readLE ((s.regs 4).toNat - 80) 8 = uc - j →
      MemFrame S.mem S'.mem (scr s ++ [(t + 8 * vl, t + 8 * vl + 8), (up + 8 * j, up + 8 * j + 8 * qhlOf j vl ul c)]) →
      S'.mem.readLE (t + 8 * vl) 8 = c →
      natVal S'.mem (up + 8 * j) (qhlOf j vl ul c) + natVal S'.mem t (qhlOf j vl ul c) =
        natVal S.mem (up + 8 * j) (qhlOf j vl ul c) +
          2 ^ (64 * qhlOf j vl ul c) * S'.mem.readLE ((s.regs 4).toNat - 152) 8 →
      S'.mem.readLE ((s.regs 4).toNat - 152) 8 ≤ 1 →
      ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S Q := by
  obtain ⟨r, hr⟩ : ∃ r : Nat, retAddrOf s = (r : W64) := ⟨(retAddrOf s).toNat, by simp⟩
  rw [hr] at k ⊢
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have ht48 := hl.t48; have hu48 := hl.u48
  have hvb := hl.vb
  have hM := hB.mem
  have hsp : (S.regs 4).toNat + 224 = (s.regs 4).toNat := by
    rw [hB.sp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := (s.regs 4).isLt; omega
  have hce := hE.pre.ce
  have hulc := hE.pre.ulc; have hucb := hE.pre.ucb
  have hc64 : c < 2 ^ 64 := hc ▸ Janus.Arm64.Memory.readLE_lt _ _ 8
  obtain ⟨hq2, hqv1, hqv, hjq⟩ := qhl_facts j vl ul c hv2 hj hcz
  have hMacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  refine subQ impl r Q S (s.regs 4).toNat t vl j ul c hB.pc hsp hsp0 hsp1 (by rw [hMacc]; exact hce.2.1.2.2) hvb
    (by omega) hE.pre.ub hc64 ht48 (by rw [hMacc]; exact hE.scr.acc) hl.tw hM.hl hM.s8 hc hM.tp hB.jj hM.s5 ?_
  intro S1 e0 e4 e5 e14 e2 e6 e3 em ex efs edf
  have hf1 : MemFrame S.mem S1.mem [(t + 8 * vl, t + 8 * vl + 8)] := by rw [em]; janus_frame
  have hM1 : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S1.mem := Mem.frame hE hM (hf1.mono fun a n ho => by
    simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    omega)
  have hM1acc : ∀ a n v, S1.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM1.fr.accessible a n v
  have hsp1' : (S1.regs 4).toNat + 224 = (s.regs 4).toNat := by rw [e4]; exact hsp
  have hr14 : S1.regs 14 = s.regs 14 := e14.trans hB.r14
  have hfs : S1.fsBase = s.fsBase := efs.trans hB.fs
  have htl : TlsG S1 := by
    obtain ⟨hb, hacc, -⟩ := hce.2.2.2.2.2.2.2.2.2.1
    exact ⟨by rw [hfs]; exact hb, by rw [hfs, hM1acc]; exact hacc, by rw [hfs, hr14]; exact hM1.tls⟩
  have hzt : Apart (up + 8 * j) (8 * qhlOf j vl ul c) t (8 * qhlOf j vl ul c) := by
    unfold Apart; have := hl.tu; omega
  have hzw : up + 8 * j + 8 * qhlOf j vl ul c ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ up + 8 * j := by
    have := hl.uw; omega
  have htw : t + 8 * qhlOf j vl ul c ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 88 ≤ t := by have := hl.tw; omega
  have hzg : Apart (up + 8 * j) (8 * qhlOf j vl ul c) ((S1.regs 14).toNat + 16) 8 := by
    rw [hr14]; unfold Apart; have := hl.ug; omega
  have hzl : Apart (up + 8 * j) (8 * qhlOf j vl ul c) (S1.fsBase.toNat - 8) 8 := by
    rw [hfs]; unfold Apart; have := hl.tlu; omega
  refine subRun impl hap R b1 L1 r Q S1 (s.regs 4).toNat t vl j (qhlOf j vl ul c) up uc
    (by rw [e0]) hsp1' hsp0 hsp1 (by rw [hM1acc]; exact hce.2.1.2.2) hvb hq2 hqv1 (by omega) hucb (by omega)
    (by omega) e2 e6 e3 hM1.s6 hM1.s4 hM1.hc
    (by rw [hM1acc]; exact Janus.Arm64.Memory.accessible_mono _ hE.pre.uacc (by omega) (by omega))
    (by rw [hM1acc]; exact Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hE.scr.acc (by omega) (by omega)))
    hzt hzw htw ((hE.ext.held hE.pre.uh).sub (by omega) (by omega)) (by rw [hr14]; exact hM1.inv)
    hce.2.2.2.2.1 (by rw [hr14]; exact hce.2.2.2.2.2.1) hzg htl (by rw [hfs]; exact hce.2.2.2.2.2.2.2.2.2.2.2) hzl ?_
  intro S' f0 f4 f5 f14 fx ffs fdf hv hbw hq hucj huj hfr
  have hfs' : MemFrame S.mem S'.mem (scr s ++ [(t + 8 * vl, t + 8 * vl + 8),
      (up + 8 * j, up + 8 * j + 8 * qhlOf j vl ul c)]) := (mfTrans hf1 hfr).mono fun a n ho => by
    simp only [scr, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  have rdS : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat - 137 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 128 ∨ (s.regs 4).toNat - 120 ≤ a) → (a + 8 ≤ (s.regs 4).toNat - 80 ∨
      (s.regs 4).toNat - 72 ≤ a) → (a + 8 ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat - 40 ≤ a) →
      (a + 8 ≤ up + 8 * j ∨ up + 8 * j + 8 * qhlOf j vl ul c ≤ a) → S'.mem.readLE a 8 = S1.mem.readLE a 8 :=
    fun a h1 h2 h3 h4 h5 => hfr.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hut : natVal S'.mem t (qhlOf j vl ul c) = natVal S1.mem t (qhlOf j vl ul c) :=
    hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := hl.tu; omega)
  have huS : natVal S1.mem (up + 8 * j) (qhlOf j vl ul c) = natVal S.mem (up + 8 * j) (qhlOf j vl ul c) :=
    hf1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := hl.tu; omega)
  have htc : S'.mem.readLE (t + 8 * vl) 8 = c := by
    have := hl.tw
    rw [rdS _ (by omega) (by omega) (by omega) (by omega) (by have := hl.tu; omega), em,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt hc64
  refine k S' ⟨f0, (f4.trans e4).trans hB.sp, (f5.trans e5).trans hB.r5, f14.trans hr14, ffs.trans hfs, fx,
    (fdf.trans edf).trans hB.df, Mem.frame hE hM1 (hfr.mono fun a n ho => ?_), ?_⟩ ?_ hq huj hucj hfs' htc ?_ ?_
  · simp only [scr, wsL, outside_append, outside_cons, outside_nil, and_true, and_assoc] at ho ⊢
    omega
  · rw [rdS _ (by omega) (by omega) (by omega) (by omega) (by omega), em,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hB.jj
  · rw [rdS _ (by omega) (by omega) (by omega) (by omega) (by omega), em,
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hqh
  · rw [hut, ← huS]; exact hv
  · rw [hbw]; split <;> omega

end FvModexp.Amd64.DivBasic
