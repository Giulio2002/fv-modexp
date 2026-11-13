import FvModexp.Proofs.Arm64.NatQ.DivMBigJ
import FvModexp.Proofs.Arm64.NatQ.DivMNew

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivMGetK.lean, TIGHT COSTS, asm s38)
# `nat.div` (arm64), `stk == nil`, `z = nil`, `z2 = u`, `u ≥ v`: `getStack()` and the rest (`bigM`)

From `nat.cmp`'s return (`AtC`, `cmp ≥ 0`, stack slot 0): `nilG` → `getCallD` (`Pool.Get`, contract `PoolGetLive`) →
pooled (`getTD`, `newStk_T`) or nil (`getND` → `noCallD` (`newobject`) → `noRetD`, `newStk_ND`) → `joinBig`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.DivNil

namespace FvModexp.Arm64.Q.NatDiv
open FvModexp.Arm64.NatDiv
variable {H : Nat}

/-- the Q copy of `AtC` (NatQ/DivRel.lean, same fields) as the original one (`nilG` is stated on it) -/
theorem atC_old {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s S : State}
    (h : AtC zp zl zc st z2 z2l z2c u ul uc v vl vc s S) :
    Arm64.NatDiv.AtC zp zl zc st z2 z2l z2c u ul uc v vl vc s S :=
  ⟨h.pc, h.sp, h.r28, h.r29, h.r18, h.r0, h.mf, h.reg, h.lr, h.fp, h.s1, h.s2, h.s3, h.s4, h.s5, h.s6, h.s7, h.s8,
    h.s9, h.s10, h.s11, h.s12, h.s13⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem bigM (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat) (hL : DivLarge.Hyp impl R dc)
    (hget : PoolGetLive (LibDiv.program.link impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput : PoolPutLive (LibDivFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (hno : NewobjectLiveContract (LibDiv.program.link impl) (cA "runtime.newobject") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {u ul uc v vl vc : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl s)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl) (hu64 : u < 2 ^ 64)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    {S : State} (hS : AtC 0 0 0 0 u ul uc u ul uc v vl vc s S) (c : Nat) (hc : c ≤ 1)
    (hr0 : S.regs 0 = BitVec.ofNat 64 c) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) S (RQM R b dc L u ul uc v vl s) := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hp.ce
  have hwO : Outside (s.sp.toNat - 41504) (41504 + 112) R.rt := hout
  have hga' := hga; unfold Apart at hga'
  have hsv := hp.sv
  obtain ⟨hz01, hnw0, -, hnwW⟩ := hp.pg
  have hb24 : 24 ≤ b := by have := hp.cost; simp only [costM, costMQ, costQ, DivLarge.costQ] at this; omega
  -- facts about `S.mem` (the window-only frame from the entry)
  have hSF : MemFrame s.mem S.mem (winA s 41504 112) := hS.mf
  have hSa : ∀ a k w, S.mem.accessible a k w = s.mem.accessible a k w := hSF.accessible
  have hgS : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hSF.readLE _ 8 (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have hnS : S.mem.readLE (Free.poolA + newOffset) 8 = 0 := by
    have h := hnwW; simp only [win, outside_cons, outside_nil, and_true] at h
    show S.mem.readLE (RunIface.stackPoolA + newOffset) 8 = 0
    rw [hSF.readLE _ 8 (by simp only [winA, outside_cons, outside_nil, and_true]; omega)]; exact hnw0
  have hLsW : LiveSep L (winA s 41504 112) := fun r hr => by
    have := hLs r hr; simp only [winA, win, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hLFS : LiveFrame s.mem S.mem L [] := LiveFrame.of_win hSF hLsW
  have hinvS : R.inv b L (s.regs 28).toNat (view R.rt L S.mem) := RtInv.inv_frame' hSF (fun q hq => by
    simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals left; exact hwO.of_sub (by simp only; omega) (by simp only; omega)) hp.inv
  have hdS : Extracted.program.DataLoaded S.mem :=
    dataLoaded_win hdl hS.reg hro (hSF.mono fun a n h => by simp only [outside_append] at h; exact h.2) hw
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)
  -- the `Get` callee window and `getStack()`'s frame (all inside `winA s`)
  have hcw : ∀ a n, Outside a n (R.rt ++ winA s 41504 112) →
      Outside a n (R.rt ++ [(s.sp.toNat - 240 - 4096, s.sp.toNat - 248), (s.sp.toNat - 232, s.sp.toNat - 224)]) := by
    intro a n h
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1, by omega, by omega⟩
  have hLsC : LiveSep L [(s.sp.toNat - 240 - 4096, s.sp.toNat - 248), (s.sp.toNat - 232, s.sp.toNat - 224)] :=
    fun r hr => by
      have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hoC : ∀ a n, (s.sp.toNat - 248 ≤ a ∧ a + n ≤ s.sp.toNat - 232) ∨ (s.sp.toNat - 224 ≤ a ∧ a + n ≤ s.sp.toNat + 112) →
      Outside a n (R.rt ++ [(s.sp.toNat - 240 - 4096, s.sp.toNat - 248), (s.sp.toNat - 232, s.sp.toNat - 224)]) := by
    intro a n h
    have := hwO.of_sub (a := a) (n := n) (by omega) (by omega)
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨this, by omega, by omega⟩
  have o240 := hoC (s.sp.toNat - 240) 8 (Or.inl ⟨by omega, by omega⟩)
  have o248 := hoC (s.sp.toNat - 248) 8 (Or.inl ⟨by omega, by omega⟩)
  have oS : ∀ k, 8 ≤ k → k ≤ 104 → Outside (s.sp.toNat + k) 8
      (R.rt ++ [(s.sp.toNat - 240 - 4096, s.sp.toNat - 248), (s.sp.toNat - 232, s.sp.toNat - 224)]) :=
    fun k h1 h2 => hoC _ 8 (Or.inr ⟨by omega, by omega⟩)
  have esp : BitVec.ofNat 64 (s.sp.toNat - 240) = s.sp - 240#64 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  -- the continuation at `joinA` (common to both `getStack()` outcomes)
  have J : ∀ (S' : State) (m : Memory) (d : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
      S'.pc = BitVec.ofNat 64 joinA → S'.sp = s.sp - 240#64 → S'.regs 1 = BitVec.ofNat 64 d →
      S'.regs 28 = s.regs 28 → S'.regs 29 = s.sp - 248#64 → S'.regs 18 = s.regs 18 → S'.mem = m →
      MemFrame S.mem m (R.rt ++ [(s.sp.toNat - 240 - 4096, s.sp.toNat - 248), (s.sp.toNat - 232, s.sp.toNat - 224)]) →
      LiveFrame S.mem m L [] → m.regions = S.mem.regions → NewStk R L L1 b b1 (s.regs 28).toNat m d →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) S' (RQM R b dc L u ul uc v vl s) := by
    intro S' m d L1 b1 j1 j2 j3 j4 j5 j6 j7 jF jLF jR jN
    subst j7
    have rd : ∀ k, 8 ≤ k → k ≤ 104 → S'.mem.readLE (s.sp.toNat + k) 8 = S.mem.readLE (s.sp.toNat + k) 8 :=
      fun k h1 h2 => jF.readLE _ 8 (oS k h1 h2)
    exact joinBig impl hap R dc hL hput hp hge hv2 hu64 hl4 hl48 S' jN
      (hSF.trans jF fun a n h => ⟨by simp only [outside_append] at h; exact h.2, hcw a n h⟩)
      (hLFS.trans jLF fun _ _ h => h) (jR.trans hS.reg) j1 j2 j3 j4 j5 j6
      ((jF.readLE _ 8 o240).trans hS.lr) ((jF.readLE _ 8 o248).trans hS.fp)
      ((rd 8 (by decide) (by decide)).trans hS.s1) ((rd 16 (by decide) (by decide)).trans hS.s2)
      ((rd 24 (by decide) (by decide)).trans hS.s3) ((rd 40 (by decide) (by decide)).trans hS.s5)
      ((rd 48 (by decide) (by decide)).trans hS.s6) ((rd 56 (by decide) (by decide)).trans hS.s7)
      ((rd 64 (by decide) (by decide)).trans hS.s8) ((rd 72 (by decide) (by decide)).trans hS.s9)
      ((rd 80 (by decide) (by decide)).trans hS.s10) ((rd 88 (by decide) (by decide)).trans hS.s11)
      ((rd 96 (by decide) (by decide)).trans hS.s12) ((rd 104 (by decide) (by decide)).trans hS.s13)
  have hws : ∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) R.rt := fun r hr => absurd hr (by simp)
  refine nilG impl (atC_old hS) c hc hr0 hal hb' ha hw _ fun X1 y1 y2 y3 y4 y5 y6 y7 y8 => ?_
  refine getCallD impl R hget (s.regs 30) _ b L (s.regs 28).toNat s.sp.toNat S.mem hal hb' ha
    (by rw [hSa]; exact hw) hg1 (by rw [hSa]; exact hg2) (by rw [hgS]; exact hg3) hwO hga hgr hLs
    (hsv.2.2.2.2.2.2.2.1 [Free.poolA]) hnS hinvS X1 y1 (y2.trans esp.symm) y7
    (y3.trans (Expmc.bv_ofNat_toNat _).symm) y6 y8 ?KN ?KT
  case KT =>
    intro S' m d rs t1 t2 t3 t4 t5 t6 t7 t8 tF tLF treg tNew tSh tfr tin tsep tinv
    obtain ⟨d0, -, d48, -⟩ := tSh.ok
    refine getTD impl (s.regs 30) _ d (by omega) (by omega) S' t1 t3 t4 fun S'' u1 u2 u3 u4 u5 u6 u7 => ?_
    have hN := newStk_T tSh tfr tin tinv (MemFrame.refl m []) hws
    refine J S'' m d (L ++ rs) b u1 (u2.trans (t2.trans (y2))) u3 (u5.trans (t6.trans y3))
      (u6.trans (t7.trans y4)) (u4.trans (t5.trans y5)) (u7.trans t8) tF tLF treg hN
  case KN =>
    intro S' m t1 t2 t3 t4 t5 t6 t7 t8 tF tLF treg tNew tinv
    refine getND impl (s.regs 30) _ S' t1 t3 t4 fun S2 u1 u2 u3 u4 u5 u6 u7 u8 => ?_
    have hmS : MemFrame s.mem m (R.rt ++ winA s 41504 112) :=
      hSF.trans tF fun a n h => ⟨by simp only [outside_append] at h; exact h.2, hcw a n h⟩
    have hdm : Extracted.program.DataLoaded m :=
      dataLoaded_win hdl (treg.trans hS.reg) hro hmS hw (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)
    have hma : ∀ a k w, m.accessible a k w = s.mem.accessible a k w := hmS.accessible
    have hgm : m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
      hmS.readLE _ 8 (by simp only [outside_append, winA, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, by omega⟩)
    refine noCallD impl R hno (s.regs 30) _ b L (s.regs 28).toNat s.sp.toNat m hal hb' ha (by rw [hma]; exact hw)
      hg1 (by rw [hma]; exact hg2) (by rw [hgm]; exact hg3) hwO hga hgr hLs hdm hsv tinv hb24 S2 u1
      (u2.trans (t2.trans (y2.trans esp.symm))) u3 (u5.trans (t6.trans (y3.trans (Expmc.bv_ofNat_toNat _).symm)))
      u7 (u8.trans t8) ?_
    intro S3 m' p v1 v2 v3 v4 v5 v6 v7 v8 hNN
    refine noRetD impl (s.regs 30) _ p S3 v1 v3 fun S4 w1 w2 w3 w4 w5 w6 w7 => ?_
    have hN := newStk_ND hNN hz01 hb24 (MemFrame.refl m' []) hws
    refine J S4 m' p (L ++ [(p, p + 24)]) (b - 24) w1 (w2.trans (v2.trans (u2.trans (t2.trans y2)))) w3
      (w5.trans (v6.trans (u5.trans (t6.trans y3)))) (w6.trans (v7.trans (u6.trans (t7.trans y4))))
      (w4.trans (v5.trans (u4.trans (t5.trans y5)))) (w7.trans v8) ?_ (tLF.trans hNN.lf fun _ _ h => h)
      (hNN.rg.trans treg) hN
    exact tF.trans hNN.mf fun a n h => ⟨h, h⟩

end FvModexp.Arm64.Q.NatDiv
