import FvModexp.Proofs.Arm64.Exp.EvPP
import FvModexp.Proofs.Arm64.Exp.EvEnt
import FvModexp.Proofs.Arm64.Exp.EvCalls
import FvModexp.Proofs.Common.ExpmcWin

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): from the entry to the return of `m1 = stk.nat(n/64 + 1)` (`nat1R`) (agent infra)

`seg1` = `entA` (prologue) ∘ `tzLoop` (`n = tz M`) ∘ `entB` (defer record, `stk.nat` arguments) ∘ the call of
`(*stack).nat` (`StackNat.HypL`); the continuation gets the shared context `WC` (live set `L1`, level
`ℓ₀ + rnd(n/64 + 1)`), the slots `ESl`, `224 = ml - n/64`, the scratch nat `m1` (`Scr`) and the budget.
Helpers: `wc_init` (the context after the function's own frame writes), `win_out0` (`WC.win_out` without `0 < ℓ`,
from `stCap = 0 → stW = 0`), `keepC` (a callee frame keeps the slots `[sp - 8, sp + 8)` and `[sp + 88, sp + 448)`),
`tz_lt`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

theorem tz_lt {X ml : Nat} (h0 : 0 < X) (h : X < 2 ^ (64 * ml)) : Exp.tz X < 64 * ml := by
  have hs := (Exp.tz_spec h0).1
  have hq : 0 < X / 2 ^ Exp.tz X := by
    rcases Nat.eq_zero_or_pos (X / 2 ^ Exp.tz X) with e | e
    · rw [e, Nat.mul_zero] at hs; omega
    · exact e
  have : 2 ^ Exp.tz X ≤ X := by
    calc 2 ^ Exp.tz X ≤ 2 ^ Exp.tz X * (X / 2 ^ Exp.tz X) := Nat.le_mul_of_pos_right _ hq
      _ = X := hs.symm
  exact (Nat.pow_lt_pow_iff_right (by omega)).1 (Nat.lt_of_le_of_lt this h)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State}

theorem EPre.cap0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) :
    stCap s.mem st = 0 → stW s.mem st = 0 :=
  hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2

/-- the context after the function's own writes (frame `FW sp`) at the entry level -/
theorem wc_init (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    (hF : MemFrame s.mem M (FW sp)) (hrg : M.regions = s.mem.regions) :
    WC R L K g sp st zp zc s.mem M L b (stLen s.mem st) := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hLs := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinv := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hsok := hP.stk0
  unfold Apart at hstw
  have hFW : ∀ a k, Outside a k (R.rt ++ WN sp K ++ ZS zp zc st s.mem) → Outside a k (FW sp) := by
    intro a k ho
    simp only [WN, FW, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  have hhd : Outside st 24 (FW sp) := by simp only [FW, outside_cons, outside_nil, and_true]; omega
  have e0 : stW M st = stW s.mem st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e1 : stLen M st = stLen s.mem st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  have e2 : stCap M st = stCap s.mem st := hF.readLE _ _ (hhd.of_sub (by omega) (by omega))
  refine ⟨hF.mono fun a k ho => hFW a k ho, LiveFrame.of_win hF (fun r hr => by
      have := hLs r hr; simp only [FW, outside_cons, outside_nil, and_true] at this ⊢; omega), hrg,
    LiveExt.refl R L, Expmc.inv_frame hF ?_ hinv, stkOK_hdr hsok hF e0 e1 e2 (LiveExt.refl R L), e1, Nat.le_refl _,
    hsok.2.2.2.2.2.1, Or.inl ⟨e0, e2⟩, fun hn => absurd ⟨e0, e2⟩ hn⟩
  intro r hr
  right
  simp only [FW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hout.of_sub (show sp - K ≤ sp - 8 by omega) (show sp - 8 + (sp + 328 - (sp - 8)) ≤ sp - K + (K + 448) by omega)
  · exact hout.of_sub (show sp - K ≤ sp + 344 by omega)
      (show sp + 344 + (sp + 448 - (sp + 344)) ≤ sp - K + (K + 448) by omega)

variable {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- the window is outside the runtime ranges and the stack's writable ranges (any level) -/
theorem win_out0 (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    ∀ a k, sp - K ≤ a → a + k ≤ sp + 448 → Outside a k (R.rt ++ stkWs M st) := by
  intro a k h1 h2
  rcases Nat.eq_zero_or_pos ℓ with h0 | h0
  · have hout := hP.win_rt
    have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have harr := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hK := hP.1.2.2.2.2.2.2.2.2.1
    have hc0 := hP.cap0
    rw [outside_append]
    refine ⟨hout.of_sub (by omega) (by omega), ?_⟩
    simp only [stkWs, outside_cons, outside_nil, and_true]
    unfold Apart at hstw
    refine ⟨by omega, ?_⟩
    rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rcases Nat.eq_zero_or_pos (stCap s.mem st) with c0 | c0
      · have := hc0 c0; rw [e1, e2, this, c0]; omega
      · have := (harr c0).1
        rw [← e1, ← e2] at this; unfold Apart at this; omega
    · have := hin.apart (hout.of_sub (a := a) (n := k) (by omega) (by omega)); unfold Apart at this
      have := h.sok.2.2.2.2.2.1; omega
  · exact h.win_out hP h0 a k h1 h2

/-- a callee frame (runtime, the callee window `[sp - stk, sp - 8) ∪ [sp + 8, sp + above)`, extra ranges `zs`
apart from the window, the stack's writable ranges) keeps the slots `[sp - 8, sp + 8)` and `[sp + 88, sp + 448)` -/
theorem keepC (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {M' : Memory} {stk above : Nat} {zs : List (Nat × Nat)}
    (hF : MemFrame M M' (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ zs ++ stkWs M st))
    (hstk : stk ≤ K) (habove : above ≤ 88)
    (hzs : ∀ a k, sp - K ≤ a → a + k ≤ sp + 448 → Outside a k zs) :
    ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 88 ≤ a ∧ a + k ≤ sp + 448) → M'.readLE a k = M.readLE a k := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  intro a k ha
  refine hF.readLE a k ?_
  have h1 := win_out0 hP h a k (by omega) (by omega)
  have h2 := hzs a k (by omega) (by omega)
  rw [outside_append] at h1
  rw [outside_append, outside_append, outside_append]
  refine ⟨⟨⟨h1.1, ?_⟩, h2⟩, h1.2⟩
  simp only [outside_cons, outside_nil, and_true]
  omega

end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the entry to `nat1R`** (see the module doc) -/
theorem seg1 {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibNE.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (haN : aboveN ≤ 88)
    (ret0 : BitVec 64) (Q : State → Prop)
    (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zl zc xp xl xc yp yl yc mp ml mc ret : Nat) (s : State)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hkN : stkN ≤ K)
    (hM : 0 < natVal s.mem mp ml)
    (hbud : stackNatCost (stLen s.mem st) (a1 (Exp.tz (natVal s.mem mp ml))) ≤ b)
    (hl16 : stLen s.mem st + a1 (Exp.tz (natVal s.mem mp ml)) + 3 ≤ 2 ^ 16)
    (hr48 : ret < 2 ^ 48) (hzl : zl < 2 ^ 64)
    (hpc : s.pc = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc)
    (h3 : s.regs 3 = BitVec.ofNat 64 st) (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 xl)
    (h6 : s.regs 6 = BitVec.ofNat 64 xc) (h7 : s.regs 7 = BitVec.ofNat 64 yp) (h8 : s.regs 8 = BitVec.ofNat 64 yl)
    (h9 : s.regs 9 = BitVec.ofNat 64 yc) (h10 : s.regs 10 = BitVec.ofNat 64 mp)
    (h11 : s.regs 11 = BitVec.ofNat 64 ml) (h12 : s.regs 12 = BitVec.ofNat 64 mc)
    (h30 : s.regs 30 = BitVec.ofNat 64 ret)
    (K1 : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 p : Nat), S.pc = BitVec.ofNat 64 nat1R →
      S.sp = BitVec.ofNat 64 sp → S.regs 28 = BitVec.ofNat 64 g → S.regs 29 = BitVec.ofNat 64 (sp - 8) →
      S.regs 18 = s.regs 18 → S.regs 0 = BitVec.ofNat 64 p →
      S.regs 1 = BitVec.ofNat 64 (a1 (Exp.tz (natVal s.mem mp ml))) →
      S.regs 2 = BitVec.ofNat 64 (a1 (Exp.tz (natVal s.mem mp ml))) →
      WC R L K g sp st zp zc s.mem S.mem L1 b1
        (stLen s.mem st + StackNat.rnd (a1 (Exp.tz (natVal s.mem mp ml)))) →
      ESl S.mem sp st (s.regs 29) ret zp zc xp xl xc yp yl yc mp ml mc (stLen s.mem st)
        (Exp.tz (natVal s.mem mp ml)) →
      S.mem.readLE (sp + 224) 8 = a2 ml (Exp.tz (natVal s.mem mp ml)) →
      Scr R L L1 s.mem S.mem st p (a1 (Exp.tz (natVal s.mem mp ml))) →
      p = stW S.mem st + 8 * stLen s.mem st →
      b - stackNatCost (stLen s.mem st) (a1 (Exp.tz (natVal s.mem mp ml))) ≤ b1 →
      ReachesRet (LibNE.program.link impl) ret0 S Q) :
    ReachesRet (LibNE.program.link impl) ret0 s Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hacc0 := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hg1 := hP.1.2.2.1
  have hg2 := hP.1.2.2.2.1
  have hg3 := hP.1.2.2.2.2.1
  have hml0 := hP.2.2.2.2.2.1
  have hml := hP.2.2.2.2.2.2.1
  have hxp := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxc := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzp := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hy48 := hP.2.2.2.2.2.2.2.2.2.1
  have hx48 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyl := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hstw := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmo := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsok := hP.stk0
  obtain ⟨hmO, hmacc, hm48, -, -, hyp, hyc, hmp, hmc, -⟩ := hmo
  have hmw := hmO.2.1
  unfold Apart at hstw hmw
  have hst48 := hsok.2.2.2.1
  have hst24 := hsok.2.2.1
  generalize hX : natVal s.mem mp ml = X at *
  have hXl : X < Exp.B ^ ml := by
    have := Memory.readLE_lt s.mem mp (8 * ml)
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
    rw [← hX, Exp.B_def, ← Nat.pow_mul, show 64 * ml = 8 * (8 * ml) by omega]; exact this
  have hXl' : X < 2 ^ (64 * ml) := by rw [Exp.B_def, ← Nat.pow_mul] at hXl; exact hXl
  have htz := tz_lt hM hXl'
  refine entA ret0 Q sp g zp zl zc st xp xl xc yp yl yc mp ml mc ret (s.regs 29) s.mem hal (by omega) hsp2
    (Memory.accessible_mono _ hacc0 (by omega) (by omega)) hg1 hg2 (by omega) hml0 (by omega) hr48 hzp hzl
    (by omega) hxp (by omega) hxc hyp (by omega) hyc hmp hmc (by omega) s hpc hP.1.1 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 h11 h12 hP.1.2.1 rfl h30 rfl ?_
  intro S1 M1 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 hF1 hrg1 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  have hmr : ∀ j, j < ml → M1.readLE (mp + 8 * j) 8 = Exp.wd X j := by
    intro j hj
    rw [hF1.readLE _ _ (by simp only [FW, outside_cons, outside_nil, and_true]; omega), ← hX]
    exact Expmc.readLE_wd _ _ _ _ hj
  refine tzLoop ret0 Q mp ml X M1 S1.regs S1.sp hmr (by rw [hF1.accessible]; exact hmacc) hm48 hM hXl (by omega)
    c5 c6 ?_ (ml - 0) 0 S1 rfl (Nat.zero_le _) (fun j hj => absurd hj (by omega)) c1 rfl
    (fun _ _ _ => rfl) c3 c10
  intro S2 d1 d2 d3 d4 d5
  have e3 : S2.regs 3 = BitVec.ofNat 64 st := (d3 3 (by omega) (by omega)).trans c4
  have e11 : S2.regs 11 = BitVec.ofNat 64 ml := (d3 11 (by omega) (by omega)).trans c6
  have e28 : S2.regs 28 = BitVec.ofNat 64 g := (d3 28 (by omega) (by omega)).trans c8
  have e29 : S2.regs 29 = BitVec.ofNat 64 (sp - 8) := (d3 29 (by omega) (by omega)).trans c9
  have e18 : S2.regs 18 = s.regs 18 := (d3 18 (by omega) (by omega)).trans c7
  have hsp' : S2.sp = BitVec.ofNat 64 sp := d2.trans c2
  have hl0 : M1.readLE (st + 8) 8 = stLen s.mem st :=
    hF1.readLE _ _ (by simp only [FW, outside_cons, outside_nil, and_true]; omega)
  refine entB ret0 Q sp g st ml (Exp.tz X) (stLen s.mem st) M1 hal (by omega) hsp2
    (by rw [hF1.accessible]; exact Memory.accessible_mono _ hacc0 (by omega) (by omega))
    (by rw [hF1.accessible]; exact Memory.accessible_weaken _ hst24) hst48 (by omega) hl0 (by omega) (by omega) (by omega) S2 d1 hsp' d4 e3 e11
    e28 e29 d5 ?_
  intro S3 M3 f1 f2 f3 f4 f5 f6 f7 f8 f9 hF3 hrg3 r368 r432 r184 r224 r296 r304 r312 r320
  have hF13 : MemFrame s.mem M3 (FW sp) := hF1.trans hF3 fun a k h => by
    simp only [FW, FB, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hB : ∀ o, (o = 0 ∨ o = 344 ∨ o = 360 ∨ o = 376 ∨ o = 384 ∨ o = 392 ∨ o = 400 ∨ o = 408 ∨ o = 416 ∨ o = 424 ∨
      o = 440) → M3.readLE (sp + o) 8 = M1.readLE (sp + o) 8 := fun o ho =>
    hF3.readLE _ _ (by simp only [FB, outside_cons, outside_nil, and_true]; omega)
  have hB8 : M3.readLE (sp - 8) 8 = M1.readLE (sp - 8) 8 :=
    hF3.readLE _ _ (by simp only [FB, outside_cons, outside_nil, and_true]; omega)
  have hw0 := wc_init hP hF13 (hrg3.trans hrg1)
  have hpre := snPre hP hw0 hkN haN f2 f7 f9 (by simp only [a1]; omega) (by simp only [a1]; omega) hbud
  refine CallNE.stkNatCallL hap hns hsn (ra_ev hap hnf 47 (by decide)) f1 f5 f3 f4 (by omega)
    (by simp only [a1]; omega) (by decide) hpre ?_
  intro s' g1 g2 g3 g4 g5 g6 hpost
  have hS3 : S3.sp.toNat = sp := by rw [f2, BitVec.toNat_ofNat]; omega
  have hg3' : (S3.regs 28).toNat = g := by rw [f7, BitVec.toNat_ofNat]; omega
  obtain ⟨L2, b2, hb2, hw2, hsc, hz0, hz1, hz2, hF⟩ :=
    WC.stkNat hP hw0 hkN haN hS3 hg3' f9 (g6.trans (by rw [f9])) (by simp only [a1]; omega) hpost
  have hk := keepC hP hw0 (zs := []) (by simpa only [List.append_nil] using hF) hkN haN
    (fun _ _ _ _ => by simp only [outside_nil])
  refine K1 s' L2 b2 _ g1 (g2.trans f2) (g3.trans f7) (g4.trans f8) (g5.trans (f6.trans e18)) hz0 hz1 hz2 hw2 ?_
    ((hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans r224) hsc ?_ hb2
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hk _ _ (Or.inl ⟨by omega, by omega⟩), hB8]; exact q1
    · rw [hk _ _ (Or.inl ⟨by omega, by omega⟩), show sp = sp + 0 by rfl, hB 0 (by omega)]; exact q2
    · exact (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans r320
    · exact (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans r296
    · exact (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans r304
    · exact (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans r312
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩), hB 344 (by omega)]; exact q3
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩), hB 360 (by omega)]; exact q4
    · exact (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans r368
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩), hB 376 (by omega)]; exact q5
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩), hB 384 (by omega)]; exact q6
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩), hB 392 (by omega)]; exact q7
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩), hB 400 (by omega)]; exact q8
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩), hB 408 (by omega)]; exact q9
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩), hB 416 (by omega)]; exact q10
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩), hB 424 (by omega)]; exact q11
    · exact (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans r432
    · rw [hk _ _ (Or.inr ⟨by omega, by omega⟩), hB 440 (by omega)]; exact q12
    · exact (hk _ _ (Or.inr ⟨by omega, by omega⟩)).trans r184
  · rfl

end FvModexp.Arm64.ExpEven
