import FvModexp.Proofs.Amd64.NatQ.DivMBigJ
import FvModexp.Proofs.Amd64.NatQ.DivMNew

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`, `z = nil`, `z2 = u`, `u ≥ v`: `getStack()` to the return (top s42)

Twin of Arm64/NatQ/DivMGetK.lean. `bigM`: from `nat.cmp`'s return (`AtC`, `u ≥ v`): `nilGM` (to `Pool.Get`), the call
(`getCallM`); a pooled stack (`getTM`, `newStk_T`) or nil (`getNM`, `newobject(type:big.stack)` = `noCallM`, `noRetM`,
`newStk_NM`); both join at `joinA` (`J`) and continue with `joinBig`. All writes before the join lie in
`R.rt ++ [(sp - 4336, sp - 224)]` (the callee windows and the return slot).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.DivNil

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem bigM (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat) (hL : DivLarge.HypG impl R dc)
    (hget : Janus.Contracts.PoolAmd64.PoolGetLive (LibDiv.program.link impl) (cA "sync.(*Pool).Get") 4096 R
      Free.stkT StkSh)
    (hput : Janus.Contracts.PoolAmd64.PoolPutLive (LibDivFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R
      Free.stkT StkSh)
    (hno : NewobjectLiveContract64 (LibDiv.program.link impl) (cA "runtime.newobject") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {u ul uc v vl vc : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl vc s)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl) (hu64 : u < 2 ^ 64)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {S : State} (hS : AtC 0 0 0 0 u ul uc u ul uc v vl vc s S) (c : Nat) (hc : c ≤ 1)
    (hr0 : S.regs 0 = BitVec.ofNat 64 c) :
    ReachesRet (LibDiv.program.link impl) (retAddrOf s) S (RQM R b dc L u ul uc v vl s) := by
  have hce := hp.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  have hwO : Outside ((s.regs 4).toNat - 41512) (41512 + 112) R.rt := hout
  obtain ⟨hz01, -, -, -⟩ := hp.pg
  have hb24 : 24 ≤ b := by have := hp.cost; simp only [costMQ, costQ, DivLarge.costQ] at this; omega
  have hSF : MemFrame s.mem S.mem (win s 41512 112) := hS.mf
  have hLFS : LiveFrame s.mem S.mem L [] := LiveFrame.of_win hSF hLs
  -- every write between `S` and the join lies in `R.rt ++ [(t - 4336, t - 224)]`
  have hsub : ∀ a n, Outside a n (R.rt ++ win s 41512 112) →
      Outside a n (win s 41512 112) ∧ Outside a n (R.rt ++ [((s.regs 4).toNat - 4336, (s.regs 4).toNat - 224)]) := by
    intro a n h
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.2, h.1, by omega⟩
  have oK : ∀ a, ((s.regs 4).toNat - 8 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 112) →
      Outside a 8 (R.rt ++ [((s.regs 4).toNat - 4336, (s.regs 4).toNat - 224)]) := by
    intro a ha'
    have := hwO.of_sub (a := a) (n := 8) (by omega) (by omega)
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨this, by omega⟩
  have hwsJ : ∀ r ∈ [((s.regs 4).toNat - 4336, (s.regs 4).toNat - 224)], Outside r.1 (r.2 - r.1) R.rt := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hwO.of_sub (by simp only; omega) (by simp only; omega)
  have hws0 : ∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) R.rt := fun r hr => absurd hr (by simp)
  -- the continuation at `joinA` (common to both `getStack()` outcomes)
  have J : ∀ (S' : State) (d : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
      S'.rip = BitVec.ofNat 64 joinA → S'.regs 4 = s.regs 4 - 232#64 → S'.regs 3 = BitVec.ofNat 64 d →
      S'.regs 14 = s.regs 14 → S'.fsBase = s.fsBase → S'.xmm 15 = 0#128 → S'.df = false →
      MemFrame S.mem S'.mem (R.rt ++ [((s.regs 4).toNat - 4336, (s.regs 4).toNat - 224)]) →
      LiveFrame S.mem S'.mem L [] → S'.mem.regions = S.mem.regions →
      NewStk R L L1 b b1 (s.regs 14).toNat S'.mem d →
      ReachesRet (LibDiv.program.link impl) (retAddrOf s) S' (RQM R b dc L u ul uc v vl s) := by
    intro S' d L1 b1 j1 j2 j3 j4 j5 j6 j7 jF jLF jR jN
    have rd : ∀ a, ((s.regs 4).toNat - 8 ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 112) →
        S'.mem.readLE a 8 = S.mem.readLE a 8 := fun a h => jF.readLE _ 8 (oK a h)
    exact joinBig impl hap R dc hL hput hp hge hv2 hu64 hra hx0 hdf0 S' jN (hSF.trans jF hsub)
      (hLFS.trans jLF fun _ _ h => h) (jR.trans hS.reg) j1 j2 j3 j4 j5 j6 j7
      ((rd _ ⟨by omega, by omega⟩).trans hS.ra) ((rd _ ⟨by omega, by omega⟩).trans hS.bp)
      ((rd _ ⟨by omega, by omega⟩).trans hS.s1) ((rd _ ⟨by omega, by omega⟩).trans hS.s2)
      ((rd _ ⟨by omega, by omega⟩).trans hS.s3) ((rd _ ⟨by omega, by omega⟩).trans hS.s5)
      ((rd _ ⟨by omega, by omega⟩).trans hS.s6) ((rd _ ⟨by omega, by omega⟩).trans hS.s7)
      ((rd _ ⟨by omega, by omega⟩).trans hS.s8) ((rd _ ⟨by omega, by omega⟩).trans hS.s9)
      ((rd _ ⟨by omega, by omega⟩).trans hS.s10) ((rd _ ⟨by omega, by omega⟩).trans hS.s11)
      ((rd _ ⟨by omega, by omega⟩).trans hS.s12) ((rd _ ⟨by omega, by omega⟩).trans hS.s13)
  -- frames into the join frame
  have wG : ∀ a n, Outside a n (R.rt ++ [((s.regs 4).toNat - 4336, (s.regs 4).toNat - 224)]) →
      Outside a n [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232)] ∧
      Outside a n (R.rt ++ [((s.regs 4).toNat - 240 - 4096, (s.regs 4).toNat - 240),
        ((s.regs 4).toNat - 232, (s.regs 4).toNat - 224)]) := by
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨by omega, h.1, by omega, by omega⟩
  refine nilGM impl hS c hc hr0 hb' ha hw _ fun X1 y1 y2 y3 y4 y5 y6 y7 y8 yF yG yR => ?_
  have hXF1 : MemFrame s.mem X1.mem (win s 41512 112) := hSF.trans yF fun a n h => ⟨h, by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
  refine getCallM impl R hget b L s hce hp.srv hp.pg hp.inv X1 y1 y2 y4 y8 hXF1 yR _ _ ?_
  intro S' m t1 t2 t3 t4 t5 t6 t7 t8 tF tLF treg tcase
  subst t8
  have hF1 : MemFrame S.mem S'.mem (R.rt ++ [((s.regs 4).toNat - 4336, (s.regs 4).toNat - 224)]) :=
    yF.trans tF wG
  have hLF1 : LiveFrame S.mem S'.mem L [] :=
    (LiveFrame.of_win yF (fun r hr => by
      have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega)).trans tLF
      fun _ _ h => h
  have hrg1 : S'.mem.regions = S.mem.regions := by
    rw [treg]; exact yG
  have hLs1 : LiveSep L [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232)] := fun r hr => by
    have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
  have w1 : ∀ a n, Outside a n (R.rt ++ [((s.regs 4).toNat - 4336, (s.regs 4).toNat - 224)]) →
      Outside a n (R.rt ++ [((s.regs 4).toNat - 4336, (s.regs 4).toNat - 224)]) ∧
      Outside a n [((s.regs 4).toNat - 240, (s.regs 4).toNat - 232)] := fun a n h => ⟨h, by
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega⟩
  rcases tcase with ⟨e0, e3, hinv1⟩ | ⟨d, rs, e0, e3, hd, hSh, hfr, hin, -, hinv1⟩
  · have hSacc : S'.mem.accessible ((s.regs 4).toNat - 41512) (41512 + 112) true = true := by
      rw [hF1.accessible, hSF.accessible]; exact hw
    refine getNM impl _ _ hb' ha S' t1 t2 hSacc e0 e3 fun X2 v1 v2 v3 v4 v5 v6 v7 v8 vF vG vR => ?_
    have hF2 : MemFrame S.mem X2.mem (R.rt ++ [((s.regs 4).toNat - 4336, (s.regs 4).toNat - 224)]) :=
      hF1.trans vF w1
    have hinv2 : R.inv b L (s.regs 14).toNat (view R.rt L X2.mem) := RtInv.inv_frame' vF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      left; exact hwO.of_sub (by simp only; omega) (by simp only; omega)) hinv1
    refine noCallM impl R hno hce hp.srv (hSF.trans hF2 hsub) hinv2 hb24 v1 v2 (v4.trans t4) v8 vR _ _
      fun S3 p x1 x2 x3 x4 x5 x6 x7 x8 _ hNN => ?_
    refine noRetM impl _ _ p S3 x1 x8 fun S4 z1 z2 z3 z4 z5 z6 z7 z8 z9 => ?_
    have hN := newStk_NM hNN hz01 hb24 (MemFrame.refl S3.mem []) hws0
    rw [← z9] at hN
    refine J S4 p (L ++ [(p, p + 24)]) (b - 24) z1 (z2.trans x2) z8 (z4.trans x4)
      (z5.trans (x5.trans (v5.trans (t6.trans y5)))) (z6.trans (x6.trans (v6.trans (t5.trans y6))))
      (z7.trans (x7.trans (v7.trans (t7.trans y7)))) ?_ ?_ ?_ hN
    · rw [z9]; exact hF2.trans hNN.mf fun a n h => ⟨h, (wG a n h).2⟩
    · rw [z9]; exact (hLF1.trans (LiveFrame.of_win vF hLs1) fun _ _ h => h).trans hNN.lf fun _ _ h => h
    · rw [z9]; exact hNN.rg.trans (vG.trans hrg1)
  · obtain ⟨d0, -⟩ := hSh.ok
    refine getTM impl _ _ d hd (by omega) S' t1 e0 e3 fun S'' u1 u2 u3 u4 u5 u6 u7 u8 u9 => ?_
    have hN := newStk_T hSh hfr hin hinv1 (MemFrame.refl S'.mem []) hws0
    rw [← u9] at hN
    refine J S'' d (L ++ rs) b u1 (u2.trans t2) u8 (u4.trans t4) (u5.trans (t6.trans y5)) (u6.trans (t5.trans y6))
      (u7.trans (t7.trans y7)) (by rw [u9]; exact hF1) (by rw [u9]; exact hLF1) (by rw [u9]; exact hrg1) hN

end FvModexp.Amd64.Q.NatDiv
