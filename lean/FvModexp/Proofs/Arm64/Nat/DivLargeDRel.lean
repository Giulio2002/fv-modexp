import FvModexp.Proofs.Arm64.Nat.DivLargeQRel

set_option autoImplicit false

/-!
# `divLarge` (arm64): the state after the division call (`fn + 0x450`) — relations (pure)

`Mem.frameS`: `Mem` across a frame that also writes `q`'s array and the stack (header + free part): the stack array may
be a new one `(w2, c2)` (a division callee's `stk.nat` grew it), `len` is unchanged. `AtD`: the state at the join after
`q.divBasic(stk, u, v)` / `q.divRecursive(stk, u, v)`: `q = U / V`, `u = (U mod V)·2^sh`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (outside_of_inRanges)

namespace FvModexp.Arm64.DivLarge

/-- `q`'s array is old (`zp`) or fresh: outside the old ranges -/
theorem qarr_out {R : RtInv} {zp zc st vp vl il : Nat} {s : State} {t w1 c1 : Nat} {L1 Lq : List (Nat × Nat)}
    {lenS P C qp qc : Nat} {M : Memory} (hQ : QArr R zp zc st vp vl il s t w1 c1 L1 Lq lenS P C qp qc M)
    {a n : Nat} (h1 : Outside a n R.rt) (h2 : Outside a n (ar zp zc)) : a + n ≤ qp ∨ qp + 8 * qc ≤ a := by
  rcases hQ.ror with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
  · exact ar_out h2 (by have := hQ.cap; omega)
  · exact outside_of_inRanges h1 hin

theorem qarr_liveOut {R : RtInv} {zp zc st vp vl il : Nat} {s : State} {t w1 c1 : Nat} {L L1 Lq : List (Nat × Nat)}
    {lenS P C qp qc : Nat} {M : Memory} (hQ : QArr R zp zc st vp vl il s t w1 c1 L1 Lq lenS P C qp qc M)
    (hx : ∀ r ∈ L, r ∈ L1) {a n : Nat} (hin : InRanges a n L) (h2 : Outside a n (ar zp zc)) :
    a + n ≤ qp ∨ qp + 8 * qc ≤ a := by
  rcases hQ.ror with ⟨rfl, rfl⟩ | ⟨-, -, hap⟩
  · exact ar_out h2 (by have := hQ.cap; omega)
  · obtain ⟨r, hr, i1, i2⟩ := hin
    have := hap r (hx r hr); unfold Apart at this; omega

theorem out6 {a n p q p' q' : Nat} {rt sc w k : List (Nat × Nat)} (h1 : Outside a n rt) (h2 : Outside a n sc)
    (h3 : Outside a n w) (h4 : a + n ≤ p ∨ q ≤ a) (h5 : a + n ≤ p' ∨ q' ≤ a) (h6 : Outside a n k) :
    Outside a n (rt ++ sc ++ w ++ [(p, q), (p', q')] ++ k) := by
  simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩, h6⟩

theorem out3 {a n p q p' q' : Nat} {w k : List (Nat × Nat)} (h1 : Outside a n w) (h2 : a + n ≤ p ∨ q ≤ a)
    (h3 : a + n ≤ p' ∨ q' ≤ a) (h4 : Outside a n k) : Outside a n (w ++ [(p, q), (p', q')] ++ k) := by
  simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨h1, h2, h3⟩, h4⟩

theorem out3_parts {a n p q p' q' : Nat} {w k : List (Nat × Nat)} (h : Outside a n (w ++ [(p, q), (p', q')] ++ k)) :
    Outside a n w ∧ (a + n ≤ p ∨ q ≤ a) ∧ (a + n ≤ p' ∨ q' ≤ a) ∧ Outside a n k := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at h; exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩

theorem out6_parts {a n p q p' q' : Nat} {rt sc w k : List (Nat × Nat)}
    (h : Outside a n (rt ++ sc ++ w ++ [(p, q), (p', q')] ++ k)) :
    Outside a n rt ∧ Outside a n sc ∧ Outside a n w ∧ (a + n ≤ p ∨ q ≤ a) ∧ (a + n ≤ p' ∨ q' ≤ a) ∧ Outside a n k := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2.1, h.1.2.2, h.2⟩

theorem outT {a n x y p q p' q' : Nat} {rt sc wa k : List (Nat × Nat)} (h1 : Outside a n rt) (h2 : Outside a n sc)
    (h3 : a + n ≤ x ∨ y ≤ a) (h4 : Outside a n wa) (h5 : a + n ≤ p ∨ q ≤ a) (h6 : a + n ≤ p' ∨ q' ≤ a)
    (h7 : Outside a n k) : Outside a n ((rt ++ sc ++ [(x, y)]) ++ (rt ++ wa ++ [(p, q), (p', q')] ++ k)) := by
  simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h1, h4⟩, h5, h6⟩, h7⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`Mem` across a frame writing `u`'s and `q`'s arrays and the stack** (pure); the stack header afterwards is
`(w2, len, c2)` -/
theorem Mem.frameS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk P C : Nat}
    {M M' : Memory} (hM : Mem R L zp zc st up uc ip il ic vp vl vc s t w1 c1 Lk bk M)
    (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M) {lenS qp qc : Nat}
    (hQ : QArr R zp zc st vp vl il s t w1 c1 L1 Lk lenS P C qp qc M)
    (hf : MemFrame M M' (R.rt ++ scrA s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C), (qp, qp + 8 * qc)] ++
      stkWs s.mem st))
    (hlf : LiveFrame M M' L (wsL zp zc up uc vl t ++ [(P, P + 8 * C), (qp, qp + 8 * qc)] ++ stkWs s.mem st))
    {w2 c2 : Nat} (hw2 : M'.readLE st 8 = w2) (hl2 : M'.readLE (st + 8) 8 = stLen s.mem st + StackNat.rnd vl)
    (hc2 : M'.readLE (st + 16) 8 = c2)
    {Lk' : List (Nat × Nat)} {bk' : Nat} (hinv : R.inv bk' Lk' (s.regs 28).toNat (view R.rt Lk' M')) :
    Mem R L zp zc st up uc ip il ic vp vl vc s t w2 c2 Lk' bk' M' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hstk : ∀ a n, s.sp.toNat - 41264 ≤ a → a + n ≤ s.sp.toNat + 112 → Outside a n (stkWs s.mem st) := by
    intro a n h1 h2
    have hsw := hl.sw
    have hfw := hE.pre.fw
    simp only [win, outside_cons, outside_nil, and_true] at hfw
    simp only [stkWs, outside_cons, outside_nil, and_true]; omega
  -- a frame slot (outside the scratch) keeps its value
  have rdw : ∀ a, s.sp.toNat - 312 ≤ a → a + 8 ≤ s.sp.toNat + 112 → Outside a 8 (scrA s) → M'.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2 h3
    have hpw := hU.pw
    have hqw := hQ.pw
    refine hf.readLE _ _ (out6 (hout.of_sub (by omega) (by omega)) h3 (outside_wsL (by have := hl.tw; omega)
      (fun h => by have := hl.zw h; omega) (fun h => by have := hl.uw h; omega)) (by omega) (by omega)
      (hstk _ _ (by omega) (by omega)))
  have so : ∀ a, (s.sp.toNat - 312 ≤ a ∧ a + 8 ≤ s.sp.toNat - 296) ∨
      (s.sp.toNat - 192 ≤ a ∧ a + 8 ≤ s.sp.toNat - 184) ∨ (s.sp.toNat - 176 ≤ a ∧ a + 8 ≤ s.sp.toNat - 144) ∨
      (s.sp.toNat - 136 ≤ a ∧ a + 8 ≤ s.sp.toNat - 120) ∨ (s.sp.toNat - 104 ≤ a ∧ a + 8 ≤ s.sp.toNat - 88) ∨
      (s.sp.toNat - 40 ≤ a ∧ a + 8 ≤ s.sp.toNat + 112) → Outside a 8 (scrA s) := by
    intro a h; simp only [scrA, outside_cons, outside_nil, and_true]; omega
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23,
    m24, -, -, -, mvs, mfr, mlf, -⟩ := hM
  refine ⟨(rdw _ (by omega) (by omega) (so _ (by omega))).trans m1, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m2,
    ?_, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m4, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m5,
    (rdw _ (by omega) (by omega) (so _ (by omega))).trans m6, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m7,
    (rdw _ (by omega) (by omega) (so _ (by omega))).trans m8, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m9,
    (rdw _ (by omega) (by omega) (so _ (by omega))).trans m10, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m11,
    (rdw _ (by omega) (by omega) (so _ (by omega))).trans m12, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m13,
    (rdw _ (by omega) (by omega) (so _ (by omega))).trans m14, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m15,
    (rdw _ (by omega) (by omega) (so _ (by omega))).trans m16, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m17,
    (rdw _ (by omega) (by omega) (so _ (by omega))).trans m18, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m19,
    (rdw _ (by omega) (by omega) (so _ (by omega))).trans m20, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m21,
    (rdw _ (by omega) (by omega) (so _ (by omega))).trans m22, (rdw _ (by omega) (by omega) (so _ (by omega))).trans m23,
    (rdw _ (by omega) (by omega) (so _ (by omega))).trans m24, hw2, hl2, hc2, ?_, ?_, ?_, hinv⟩
  · have hpw := hU.pw
    have hqw := hQ.pw
    rw [hf.readLE _ _ (out6 (hout.of_sub (by omega) (by omega))
      (by simp only [scrA, outside_cons, outside_nil, and_true]; omega) (outside_wsL (by have := hl.tw; omega)
      (fun h => by have := hl.zw h; omega) (fun h => by have := hl.uw h; omega)) (by omega) (by omega)
      (hstk _ _ (by omega) (by omega)))]; exact m3
  · intro a n h1 h2
    have hvh := hE.pre.vo.2.2.2.1
    have hsv := hE.pre.svv
    have hpv := hU.pv; have hqv := hQ.pv
    have hlc := hE.pre.sti.1.2.2.2.2.2.1
    unfold Apart at hsv hpv hqv
    have hvW : Outside a n (wsL zp zc up uc vl t) := outside_wsL (by have := hl.tv; omega)
      (fun h => by have := hl.zv h; omega) (fun h => by have := hl.uv h; omega)
    have hvS : Outside a n (stkWs s.mem st) := by
      simp only [stkWs, outside_cons, outside_nil, and_true]; omega
    rw [← mvs a n h1 h2]
    rcases hvh.sub h1 h2 with hi | ho
    · exact hlf.readLE a n hi (out3 hvW (by omega) (by omega) hvS)
    · exact hf.readLE a n (out6 ho (by simp only [scrA, outside_cons, outside_nil, and_true]; have := hl.vw; omega)
        hvW (by omega) (by omega) hvS)
  · refine (mfTrans mfr hf).mono fun a n ho => ?_
    have ho0 := ho
    simp only [outside_append] at ho
    obtain ⟨⟨⟨hrt, hwa⟩, hws⟩, hst⟩ := ho
    simp only [winA, outside_cons, outside_nil, and_true] at hwa
    have hP := uarr_out hE hU hrt (wsL_parts hws).2.2
    have hq := qarr_out hQ hrt (wsL_parts hws).2.1
    rw [outside_append]
    exact ⟨ho0, out6 hrt (by simp only [scrA, outside_cons, outside_nil, and_true]; omega) hws hP hq hst⟩
  · refine ⟨fun a n hin hws => ?_⟩
    rw [outside_append] at hws
    have hP := uarr_liveOut hE hU hin (wsL_parts hws.1).2.2
    have hq := qarr_liveOut hQ (fun r hr => hE.ext.mem_old hr) hin (wsL_parts hws.1).2.1
    rw [hlf.readLE a n hin (out3 hws.1 hP hq hws.2)]
    exact mlf.readLE a n hin (by rw [outside_append]; exact hws)

/-- the callee window one frame (304) down lies in `scrB`'s first two ranges (small context: frameX's `omega` took 38 s) -/
theorem scrB_winA {s X : State} {a n K A : Nat} (h : Outside a n (scrB s)) (hspn : X.sp.toNat = s.sp.toNat - 304)
    (hK : K ≤ 40960) (hA : A ≤ 96) (h0 : 41264 ≤ s.sp.toNat) : Outside a n (winA X K A) := by
  simp only [scrB, outside_cons] at h
  obtain ⟨h1, h2, -⟩ := h
  simp only [winA, outside_cons, outside_nil, and_true]; rw [hspn]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the frames from `joinQ` (`S`) over the call preparation (`X`: `scrB` slots, `q`'s array) and a division callee
(window `K / A` at `SP' = SP - 304`, writes `q[0:qn]`, `u`, the stack) (pure) -/
theorem frameX {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lq bq P C sh qp qc S) {X : State}
    (hspn : X.sp.toNat = s.sp.toNat - 304)
    (hA : MemFrame S.mem X.mem (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)]))
    (hAL : LiveFrame S.mem X.mem L [(qp, qp + 8 * qc)])
    {K A qn : Nat} (hK : K ≤ 40960) (hAb : A ≤ 96) (hqn : qn ≤ qc) {M' : Memory}
    (hC : MemFrame X.mem M' (R.rt ++ winA X K A ++ [(qp, qp + 8 * qn), (P, P + 8 * (il + 1))] ++ stkWs X.mem st))
    (hCL : LiveFrame X.mem M' Lq ([(qp, qp + 8 * qn), (P, P + 8 * (il + 1))] ++ stkWs X.mem st)) :
    MemFrame S.mem M' (R.rt ++ scrB s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C), (qp, qp + 8 * qc)] ++
      stkWs s.mem st) ∧
    LiveFrame S.mem M' L (wsL zp zc up uc vl t ++ [(P, P + 8 * C), (qp, qp + 8 * qc)] ++ stkWs s.mem st) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hM := hS.mem.mem
  have hcap := hS.ua.cap
  have hlc := hE.pre.sti.1.2.2.2.2.2.1
  have hc1 := hE.c1len
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have rdX : ∀ a, st ≤ a → a + 8 ≤ st + 24 → X.mem.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 => by
    have hqs := hS.qa.ps; unfold Apart at hqs
    have hsw := hl.sw
    rcases hE.pre.sti.1.2.1.sub h1 h2 with hi | ho
    · exact hAL.readLE a 8 hi (by simp only [outside_cons, outside_nil, and_true]; omega)
    · exact hA.readLE a 8 (by
        simp only [scrB, outside_append, outside_cons, outside_nil, and_true]; exact ⟨⟨ho, by omega⟩, by omega⟩)
  have hW : stW X.mem st = w1 := by simp only [stW]; rw [rdX _ (by omega) (by omega)]; exact hM.hw
  have hLn : stLen X.mem st = stLen s.mem st + StackNat.rnd vl := by
    simp only [stLen]; rw [rdX _ (by omega) (by omega)]; exact hM.hlen
  have hCp : stCap X.mem st = c1 := by simp only [stCap]; rw [rdX _ (by omega) (by omega)]; exact hM.hcap
  -- the stack ranges at `X` lie in the old ones or in `R.rt`
  have hstk : ∀ a n, Outside a n R.rt → Outside a n (stkWs s.mem st) → Outside a n (stkWs X.mem st) := by
    intro a n h1 h2
    simp only [stkWs, hW, hLn, hCp, outside_cons, outside_nil, and_true] at h2 ⊢
    refine ⟨h2.1, ?_⟩
    rcases hE.arr with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · omega
    · have := outside_of_inRanges h1 hin; omega
  refine ⟨(mfTrans hA hC).mono fun a n ho => ?_, ⟨fun a n hin ho => ?_⟩⟩
  · obtain ⟨hrt, hsc, hws, hP, hq, hst⟩ := out6_parts ho
    exact outT hrt hsc hq (scrB_winA hsc hspn hK hAb hsp0) (by omega) (by omega) (hstk a n hrt hst)
  · obtain ⟨hws, hP, hq, hst⟩ := out3_parts ho
    have hstX : Outside a n (stkWs X.mem st) := by
      simp only [stkWs, hW, hLn, hCp, outside_cons, outside_nil, and_true] at hst ⊢
      refine ⟨hst.1, ?_⟩
      rcases hE.arr with ⟨rfl, rfl⟩ | ⟨-, hap⟩
      · omega
      · obtain ⟨r, hr, i1, i2⟩ := hin; have := hap r hr; unfold Apart at this; omega
    rw [hCL.readLE a n (hS.ext3.inRanges_old (hE.ext.inRanges_old hin)) (by
      rw [outside_append]; exact ⟨by simp only [outside_cons, outside_nil, and_true]; omega, hstX⟩)]
    exact hAL.readLE a n hin (by simp only [outside_cons, outside_nil, and_true]; exact hq)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `MemU` across a frame writing `u`'s and `q`'s arrays and the stack (the `scrB` slots, not `shift`) (pure) -/
theorem MemU.frameS {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk P C sh : Nat}
    {M M' : Memory} (hM : MemU R L zp zc st up uc ip il ic vp vl vc s t w1 c1 Lk bk P C sh M)
    (hU : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C M) {lenS qp qc : Nat}
    (hQ : QArr R zp zc st vp vl il s t w1 c1 L1 Lk lenS P C qp qc M)
    (hf : MemFrame M M' (R.rt ++ scrB s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C), (qp, qp + 8 * qc)] ++
      stkWs s.mem st))
    (hlf : LiveFrame M M' L (wsL zp zc up uc vl t ++ [(P, P + 8 * C), (qp, qp + 8 * qc)] ++ stkWs s.mem st))
    {w2 c2 : Nat} (hw2 : M'.readLE st 8 = w2) (hl2 : M'.readLE (st + 8) 8 = stLen s.mem st + StackNat.rnd vl)
    (hc2 : M'.readLE (st + 16) 8 = c2)
    {Lk' : List (Nat × Nat)} {bk' : Nat} (hinv : R.inv bk' Lk' (s.regs 28).toNat (view R.rt Lk' M')) :
    MemU R L zp zc st up uc ip il ic vp vl vc s t w2 c2 Lk' bk' P C sh M' := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hstk : ∀ a n, s.sp.toNat - 41264 ≤ a → a + n ≤ s.sp.toNat + 112 → Outside a n (stkWs s.mem st) := by
    intro a n h1 h2
    have hsw := hl.sw
    have hfw := hE.pre.fw
    simp only [win, outside_cons, outside_nil, and_true] at hfw
    simp only [stkWs, outside_cons, outside_nil, and_true]; omega
  have rdw : ∀ a, s.sp.toNat - 192 ≤ a → a + 8 ≤ s.sp.toNat - 96 → Outside a 8 (scrB s) → M'.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2 h3
    have hpw := hU.pw
    have hqw := hQ.pw
    refine hf.readLE _ _ (out6 (hout.of_sub (by omega) (by omega)) h3 (outside_wsL (by have := hl.tw; omega)
      (fun h => by have := hl.zw h; omega) (fun h => by have := hl.uw h; omega)) (by omega) (by omega)
      (hstk _ _ (by omega) (by omega)))
  refine ⟨Mem.frameS hE hM.mem hU hQ (hf.mono fun a n ho => ?_) hlf hw2 hl2 hc2 hinv,
    (rdw _ (by omega) (by omega) (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)).trans hM.sC,
    (rdw _ (by omega) (by omega) (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)).trans hM.sL,
    (rdw _ (by omega) (by omega) (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)).trans hM.sP,
    (rdw _ (by omega) (by omega) (by simp only [scrB, outside_cons, outside_nil, and_true]; omega)).trans hM.ssh, ?g⟩
  case g =>
    have hga := hE.pre.ce.2.2.2.2.1; have hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt := hE.pre.ce.2.2.2.2.2.1
    have hpg := hU.pg; have hqg := hQ.pg
    have hgs : Outside ((s.regs 28).toNat + 16) 8 (stkWs s.mem st) := by
      have := hE.pre.sti.2.2.1; have hlc := hE.pre.sti.1.2.2.2.2.2.1
      unfold Apart at this
      simp only [stkWs, outside_cons, outside_nil, and_true]
      refine ⟨by omega, ?_⟩
      by_cases hc : 0 < stCap s.mem st
      · have := (hE.pre.sti.2.2.2 hc).2; unfold Apart at this; omega
      · have := hE.pre.w0 (by omega); rw [this]; omega
    unfold Apart at hga hpg hqg
    rw [hf.readLE _ _ (out6 hgr (by simp only [scrB, outside_cons, outside_nil, and_true]; omega) (g_wsL hE)
      (by omega) (by omega) hgs)]
    exact hM.grd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := out6_parts ho
  refine out6 h1 ?_ h3 h4 h5 h6
  simp only [scrA, scrB, outside_cons, outside_nil, and_true] at h2 ⊢
  omega

/-- the join after the division call (`fn + 0x450`) -/
abbrev joinD : Nat := segAddr Extracted.program fn + 0x450

/-- the state at `joinD`: `q[0:m+1] = U / V`, `u = (U mod V)·2^sh`; the stack array is `(w2, c2)` (the entry one, or a
fresh one apart from `Lq`); `b - c ≤ b2` (the budget of the whole function is paid except nothing) -/
structure AtD (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat)
    (s : State) (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (Lq : List (Nat × Nat)) (P C sh qp qc : Nat)
    (L2 : List (Nat × Nat)) (b2 w2 c2 : Nat) (S : State) : Prop where
  pc : S.pc = BitVec.ofNat 64 joinD
  sp : S.sp = s.sp - 304#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 312#64
  r18 : S.regs 18 = s.regs 18
  mem : MemU R L zp zc st up uc ip il ic vp vl vc s t w2 c2 L2 b2 P C sh S.mem
  sq0 : S.mem.readLE (s.sp.toNat - 64) 8 = qp
  sq1 : S.mem.readLE (s.sp.toNat - 56) 8 = il - vl + 1
  sq2 : S.mem.readLE (s.sp.toNat - 48) 8 = qc
  ua : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C S.mem
  qa : QArr R zp zc st vp vl il s t w1 c1 L1 L2 (stLen s.mem st + StackNat.rnd vl) P C qp qc S.mem
  ext3 : LiveExt R L1 Lq
  ext4 : LiveExt R Lq L2
  bud : b - c ≤ b2
  arr2 : (w2 = w1 ∧ c2 = c1) ∨ (InRanges w2 (8 * c2) R.rt ∧ ApartAll w2 (8 * c2) Lq)
  live2 : NatLive S.mem R L2 w2 c2
  c2len : stLen s.mem st + StackNat.rnd vl ≤ c2
  c2b : c2 < 2 ^ 40
  sh63 : sh ≤ 63
  qval : natVal S.mem qp (il - vl + 1) = natVal s.mem ip il / natVal s.mem vp vl
  rval : natVal S.mem P (il + 1) = natVal s.mem ip il % natVal s.mem vp vl * 2 ^ sh
  reg : S.mem.regions = s.mem.regions
  arrL2 : ¬(w2 = w1 ∧ c2 = c1) → (w2, w2 + 8 * c2) ∈ L2 ∧ 0 < c2
  /-- `q`'s array is held by `Lq` (the live set after both `make`s; a grown stack array is apart from `Lq`, `arr2`) -/
  qL : Held R Lq qp (8 * qc)

end FvModexp.Arm64.DivLarge
