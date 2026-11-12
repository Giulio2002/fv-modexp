import FvModexp.Proofs.Arm64.Exp.IExpPost
import FvModexp.Proofs.Arm64.Exp.IExpAtN
import FvModexp.Proofs.Arm64.Exp.IExpP
import FvModexp.Proofs.Arm64.Exp.IExpB
import FvModexp.Proofs.Arm64.Exp.IExpC
import FvModexp.Proofs.Arm64.Exp.IExpL

/-!
# `(*Int).exp` (arm64): `z.exp(z, y, m, false)` returns `z = z^y mod m` (`RunIface.ExpSpec`, local form `ExpSpecX`)

Composition: segment A (entry → alias test), B (alias test → join), C (→ `nat.expNN`'s entry; its precondition by
`preNF_of`), the call of `nat.expNN` (`ExpN.ensNilF` on `LibNE`, a `Summary` of `LibExp`), `atN_of` at its return,
segment D (header stores, write barrier, `RET`) and `post_of`.

`ExpSpecX` = `RunIface.ExpSpec` with the precondition's extra conjunct `ExpX` (top's FINAL `PoolG` + `IntOK` cap bound,
`m ≠ nil`, `z`'s header apart from the write-barrier flag) and the result's cap bound in the post (`IntOK`'s new
conjunct) — the mechanical switch to top's text when `RunIface` has it.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Arm64.IExp

open FvModexp.Arm64.RunIface (IntPre IntPost IntV IntLenLe OneG maxW ExpBudget lenW)

/-- `RunIface.ExpSpec` with `ExpX` in the pre and the result's cap bound in the post (see the module doc) -/
def ExpSpecX (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64),
    Ensures ((Extracted.program.onlySegments RunIface.namesExp).link impl)
      (segAddr Extracted.program (RunIface.P ++ "(*Int).exp")) [z, z, y, mm, 0#64]
      (fun s => IntPre R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above [z.toNat, y.toNat, mm.toNat] s ∧ 0 < IntV s.mem mm.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ IntLenLe s.mem mm.toNat maxW ∧
        OneG R L s.mem (win s stk above) [z.toNat, y.toNat, mm.toNat] ∧
        ExpX R s.mem (win s stk above) z.toNat y.toNat mm.toNat)
      (fun s s' => s'.regs 0 = z ∧
        IntPost R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above z.toNat (IntV s.mem z.toNat ^ IntV s.mem y.toNat % IntV s.mem mm.toNat) s s' ∧
        s'.mem.readLE (z.toNat + 24) 8 < 2 ^ 40)

set_option maxRecDepth 20000 in
/-- the return address of the `expNN` call (fn+0x2dc, in `(*Int).exp`'s segment) is outside `LibNE` -/
theorem raN_ret (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments LibNE.names).link impl) raN :=
  CallW.retAddr_restrict hap (cs := Extracted.seg5)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 183
    (by decide) (by decide) (by decide)

theorem log2_lt64 {m : Memory} {p n : Nat} (hn : 0 < n) : Nat.log2 (natVal m p n) < 64 * n := by
  rcases Nat.eq_zero_or_pos (natVal m p n) with h | h
  · rw [h]; simp only [Nat.log2_zero]; omega
  · refine (Nat.log2_lt (by omega)).2 ?_
    have := Memory.readLE_lt m p (8 * n)
    simp only [natVal]
    calc m.readLE p (8 * n) < 256 ^ (8 * n) := this
      _ = 2 ^ (64 * n) := by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `nat.expNN` (`ensNilF`, on `LibNE`) as a `Summary` of `LibExp` at the call of `(*Int).exp` (`x = z`) -/
theorem nSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : ExpN.DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {stkE : Nat} {needE : Nat → Nat → Nat → Nat} {costE : Nat → Nat → Nat → Nat → Nat}
    (hEv : ExpEven.EvenSum impl R stkE 112 needE costE) (hstkE : stkE ≤ K + 1056)
    (hget : PoolGetLive (LibNE.program.link impl) ExpN.getA 4096 R Free.stkT StkSh)
    (hno : NewobjectLiveContract (LibNE.program.link impl) ExpN.noA 4096 R)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true)
    (hn11R : nsR.contains Extracted.seg11.name = false) (hKR : stkR ≤ K + 1056)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc yp yl yc mp n mc : Nat) :
    Summary (LibExp.program.link impl) fnN
      (fun s => RetAddr ((Extracted.program.onlySegments LibNE.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 0,
          BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl,
          BitVec.ofNat 64 yc, BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc, BitVec.ofNat 64 0] ∧
        ExpN.PreNF R b L K costF needR costR (ExpN.addN needS needE) needP (ExpN.addC costS costE) costP
          zp zl zc 0 zp zl zc yp yl yc mp n mc 0 s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        ExpN.PostN R b L K costF costR (ExpN.addC costS costE) costP zp zc zp zl yp yl mp n s s') := by
  have hS := Ensures.toSummaryIn (ExpN.ensNilF impl hap R H hEv hstkE hget hno hput hRem hnsR hn11R hKR b L
    zp zl zc 0 zp zl zc yp yl yc mp n mc 0) (noExit_restrict hap LibNE.names) (codeIn_restrict_mono hap ne_sub)
  rw [← LibExp.eq_only, show segAddr Extracted.program ExpN.fn = fnN by decide] at hS
  exact hS

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`(*Int).exp`** (arm64) as `Run` calls it: `z.exp(z, y, m, false)` returns `z` with `z = z^y mod m`
(`ExpSpecX`). Premises: `nat.expNN`'s callees (`DHyps`: division, slow / power-of-two paths, runtime contracts;
`hEv`: `nat.expNNEven`; `hRem`: `nat.rem`; the pool / `newobject` contracts), the write barrier, the stack sizes
(`expNN`'s `K + 1632 ≤ stk`, the barrier's 4096 bytes below `(*Int).exp`'s frame) and the callees' needs and
costs within `RunIface.ExpBudget` for operands of at most 128 words (`hneed`, `hbud`). -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : ExpN.DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {stkE : Nat} {needE : Nat → Nat → Nat → Nat} {costE : Nat → Nat → Nat → Nat → Nat}
    (hEv : ExpEven.EvenSum impl R stkE 112 needE costE) (hstkE : stkE ≤ K + 1056)
    (hget : PoolGetLive (LibNE.program.link impl) ExpN.getA 4096 R Free.stkT StkSh)
    (hno : NewobjectLiveContract (LibNE.program.link impl) ExpN.noA 4096 R)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true)
    (hn11R : nsR.contains Extracted.seg11.name = false) (hKR : stkR ≤ K + 1056)
    (hwb : WbLiveContract (LibExp.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {stk above : Nat} (hK : K + 1632 ≤ stk) (hK4 : 4304 ≤ K) (hK20 : K + 288 ≤ 2 ^ 20) (h4416 : 4416 ≤ stk)
    (hab : 48 ≤ above)
    (hneed : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      needR xl n ≤ 2 ^ 16 ∧ ExpN.addN needS needE xl yl n ≤ 2 ^ 16 ∧ needP xl yl lm ≤ 2 ^ 16)
    (hbud : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      24 + (makeCost 1 + makeCost n + costR 0 xl n + ExpN.addC costS costE 0 xl yl n + costP 0 xl yl lm +
        ExpOdd.OBud costF n xl yl 0) ≤ ExpBudget (max (max xl yl) n) yl ∧
      24 + ExpN.NCost costF costR (ExpN.addC costS costE) costP xl yl n 0 lm ≤ ExpBudget (max (max xl yl) n) yl) :
    ExpSpecX impl R stk above := by
  intro b L z y mm
  rw [namesExp_eq, ← LibExp.eq_only, show segAddr Extracted.program (RunIface.P ++ "(*Int).exp") = fnI by decide]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  obtain ⟨hIP, hm0, hlz, hly, hlm, hone, hx⟩ := hpre
  have hIP' := hIP
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hstk, hab48, hacc⟩, -, hrt, -, -, hLs, -⟩, hsv, hG, -, -, hops, hpw⟩ := hIP'
  have hoz := hops z.toNat (by simp)
  have hoy := hops y.toNat (by simp)
  have hom := hops mm.toNat (by simp)
  clear hops
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hpw
  obtain ⟨⟨-, ⟨hzmA, -, -, hzmArr⟩⟩, -⟩ := hpw
  obtain ⟨⟨hz0, -, hz48, hzacc, hzH, hzL, -, -, hzap, -⟩, hzW, -, -, -⟩ := hoz
  obtain ⟨⟨hy0, -, hy48, hyacc, -, -, -, -, -⟩, hyW, -, -, -⟩ := hoy
  obtain ⟨⟨-, -, hm48, hmacc, -, hmL, -, -, -⟩, hmW, -, -, -⟩ := hom
  have hx' := hx
  obtain ⟨-, -, -, -, hmA0, hwbz⟩ := hx'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwbacc, -, hwbw⟩ := id hG
  have hok : R.ok (cA "runtime.gcWriteBarrier2") [2] := hsv.2.2.2.2.2.1 _
  -- the operand headers
  generalize hzp : s.mem.readLE (z.toNat + 8) 8 = zp at hzL hzmArr
  generalize hzc : s.mem.readLE (z.toNat + 24) 8 = zc at hzL hzmArr
  generalize hzl : s.mem.readLE (z.toNat + 16) 8 = zl
  generalize hyp : s.mem.readLE (y.toNat + 8) 8 = yp
  generalize hyl : s.mem.readLE (y.toNat + 16) 8 = yl
  generalize hyc : s.mem.readLE (y.toNat + 24) 8 = yc
  generalize hmp : s.mem.readLE (mm.toNat + 8) 8 = mp at hmL hzmArr
  generalize hmn : s.mem.readLE (mm.toNat + 16) 8 = n
  generalize hmc : s.mem.readLE (mm.toNat + 24) 8 = mc at hmL hzmArr
  have hzl128 : zl ≤ 128 := by have := hlz; simp only [IntLenLe, maxW] at this; rw [hzl] at this; exact this
  have hyl128 : yl ≤ 128 := by have := hly; simp only [IntLenLe, maxW] at this; rw [hyl] at this; exact this
  have hn128 : n ≤ 128 := by have := hlm; simp only [IntLenLe, maxW] at this; rw [hmn] at this; exact this
  have hn0 : 0 < n := by
    have := hm0; simp only [IntV] at this; rw [hmp, hmn] at this
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp only [natVal_zero] at this; omega
    · exact h
  have hB : ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
      (lenW s.mem y.toNat) = ExpBudget (max (max zl yl) n) yl := by
    simp only [lenW]; rw [hzl, hyl, hmn]
  have hlm64 := log2_lt64 (m := s.mem) (p := mp) hn0
  obtain ⟨hnR, hnS, hnP⟩ := hneed zl yl n _ hzl128 hyl128 hn0 hn128 hlm64
  obtain ⟨hbP, hbC⟩ := hbud zl yl n _ hzl128 hyl128 hn0 hn128 hlm64
  rw [← hB] at hbP hbC
  have hst : stk ≤ s.sp.toNat := hstk
  have hsp0 : s.sp = BitVec.ofNat 64 s.sp.toNat := (Expmc.bv_ofNat_toNat _).symm
  have h280 : s.regs 28 = BitVec.ofNat 64 (s.regs 28).toNat := (Expmc.bv_ofNat_toNat _).symm
  have hzS : z.toNat + 32 ≤ s.sp.toNat - 328 ∨ s.sp.toNat + 48 ≤ z.toNat := by
    simp only [win, outside_cons, outside_nil, and_true] at hzW; omega
  have hmS : mm.toNat + 32 ≤ s.sp.toNat - 328 ∨ s.sp.toNat + 48 ≤ mm.toNat := by
    simp only [win, outside_cons, outside_nil, and_true] at hmW; omega
  have hali : zc = 0 ∨ mc = 0 ∨ ExpN.lastA zp zc ≠ ExpN.lastA mp mc := by
    rcases Nat.eq_zero_or_pos zc with h1 | h1
    · exact Or.inl h1
    rcases Nat.eq_zero_or_pos mc with h2 | h2
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ?_)
    have ha := hzmArr h1 h2; unfold Apart at ha
    have hz' := (hzL h1).2.2.2; have hm' := (hmL h2).2.2.2
    simp only [ExpN.lastA]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  -- segment A
  refine returns_of_reaches (runA impl ret hret _ s.sp.toNat (s.regs 28).toNat ret z.toNat y.toNat mm.toNat
    zp zl zc yp yl yc (s.regs 29) s.mem hal (by omega) (by omega)
    (Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) hr48 hz48
    (Memory.accessible_weaken _ hzacc) hzS hy48 (Memory.accessible_weaken _ hyacc)
    (by simp only [win, outside_cons, outside_nil, and_true] at hyW; omega)
    (fun h => hmA0 h) mm.isLt (by intro h; have := hzmA; unfold Apart at this; omega) hzp hzl hzc hy0 hyp hyl hyc
    s h_pc hsp0 (h_x0.trans (Expmc.bv_ofNat_toNat _).symm) (h_x1.trans (Expmc.bv_ofNat_toNat _).symm)
    (h_x2.trans (Expmc.bv_ofNat_toNat _).symm) (h_x3.trans (Expmc.bv_ofNat_toNat _).symm) h_x4 h280 rfl h_lr rfl ?KA)
  intro S1 M1 p1 sp1 a0 a1 a2 a3 a4 a7 a8 a9 a14 a15 a16 a18 a28 a29 a30 hm1 hF1 hrg1 r1 r2 r3 r4 r5 r6 r7 r8
  have rd1 : ∀ a k, (a + k ≤ s.sp.toNat - 328 ∨ s.sp.toNat + 48 ≤ a) → M1.readLE a k = s.mem.readLE a k :=
    fun a k h => hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hac1 : ∀ a k w, M1.accessible a k w = s.mem.accessible a k w := hF1.accessible
  have ez8 : M1.readLE (z.toNat + 8) 8 = zp := (rd1 _ _ (by omega)).trans hzp
  have ez16 : M1.readLE (z.toNat + 16) 8 = zl := (rd1 _ _ (by omega)).trans hzl
  have ez24 : M1.readLE (z.toNat + 24) 8 = zc := (rd1 _ _ (by omega)).trans hzc
  have em8 : M1.readLE (mm.toNat + 8) 8 = mp := (rd1 _ _ (by omega)).trans hmp
  have em16 : M1.readLE (mm.toNat + 16) 8 = n := (rd1 _ _ (by omega)).trans hmn
  have em24 : M1.readLE (mm.toNat + 24) 8 = mc := (rd1 _ _ (by omega)).trans hmc
  -- segment B
  refine runB impl ret hret _ z.toNat mm.toNat zp zc mp mc M1 hz48
    (by rw [hac1]; exact Memory.accessible_weaken _ hzacc) hm48
    (by rw [hac1]; exact Memory.accessible_weaken _ hmacc) ez8 ez24 em8 em24 hali S1 p1 a0 a3 hm1 ?KB
  intro S2 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q14 q15 q16 q17 q18 q28 q29 q30 qm
  -- segment C
  refine runC impl ret hret _ s.sp.toNat z.toNat mm.toNat zp zl zc mp n mc M1 hal (by omega) (by omega)
    (by rw [hac1]; exact Memory.accessible_mono _ hacc (by omega) (by omega)) hz48
    (by rw [hac1]; exact Memory.accessible_weaken _ hzacc) hzS hm48
    (by rw [hac1]; exact Memory.accessible_weaken _ hmacc) ez8 ez16 ez24 em8 em16 em24 S2 q1 (q2.trans sp1)
    (q3.trans a0) (q7.trans a4) q17 qm ?KC
  intro S3 M3 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c18 c28 c29 c30 cm hFC hrgC f128 f120 f80
  have hF3 : MemFrame s.mem M3 [(s.sp.toNat - 328, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)] :=
    hF1.trans hFC fun a k h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢; exact ⟨h, by omega, by omega⟩
  have hF3' : MemFrame s.mem S3.mem [(s.sp.toNat - 328, s.sp.toNat + 48)] := by
    rw [cm]; exact hF3.mono fun a k h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hrg3 : S3.mem.regions = s.mem.regions := by rw [cm, hrgC, hrg1]
  have h283 : S3.regs 28 = s.regs 28 := c28.trans (q28.trans a28)
  have hsp3 : S3.sp = BitVec.ofNat 64 (s.sp.toNat - 320) := c2
  have hP := preNF_of (needS := ExpN.addN needS needE) (costS := ExpN.addC costS costE) hIP hm0 hlz hly hlm hone hx
    hK hK4 hK20 hab hzp hzl hzc hyp hyl hyc hmp hmn hmc hnR hnS hnP hbP hsp3 h283 hF3' hrg3
  -- the call of `nat.expNN`
  refine Reaches.call_regions ((nSum impl hap R H hEv hstkE hget hno hput hRem hnsR hn11R hKR b L zp zl zc yp yl yc
    mp n mc).withExit hret) c1 ⟨?_, ⟨c3, c4, c5, c6, c7.trans (q14.trans a14), c8.trans (q15.trans a15),
      c9.trans (q16.trans a16), c10.trans (q8.trans a7), c11.trans (q9.trans a8), c12.trans (q10.trans a9), c13, c14,
      c15, c16, trivial⟩, hP⟩ fun S4 hpc4 hq hrg4 => ?_
  · rw [c30, BitVec.toNat_ofNat]; exact raN_ret impl hap
  obtain ⟨⟨sp4, r28_4, r29_4, r18_4⟩, hpost⟩ := hq
  obtain ⟨hslot, p, l, c, b', L', e0, e1, e2, hA⟩ := atN_of hIP hK hab hzp hzl hzc hyp hyl hmp hmn hbC hsp3 h283
    (by rw [cm]; exact hF3) hpost
  have hac4 : ∀ a k w, S4.mem.accessible a k w = s.mem.accessible a k w := hA.mf.accessible
  have hzH' : Held R L' z.toNat 32 := hA.ext.held hzH
  have hng : S4.mem.readLE z.toNat 1 = 0 := by
    rw [AtN.hdr hA hzH hzW hzap _ _ (Nat.le_refl _) (by omega)]; exact hz0
  have s8 : S4.mem.readLE (s.sp.toNat + 8) 8 = z.toNat := by
    rw [hslot _ _ (Or.inr ⟨by omega, by omega⟩), cm, hFC.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)]; exact r3
  have s16 : S4.mem.readLE (s.sp.toNat + 16) 8 = z.toNat := by
    rw [hslot _ _ (Or.inr ⟨by omega, by omega⟩), cm, hFC.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)]; exact r4
  have sfp : S4.mem.readLE (s.sp.toNat - 328) 8 = (s.regs 29).toNat := by
    rw [hslot _ _ (Or.inl ⟨by omega, by omega⟩), cm, hFC.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)]; exact r1
  have slr : S4.mem.readLE (s.sp.toNat - 320) 8 = ret := by
    rw [hslot _ _ (Or.inl ⟨by omega, by omega⟩), cm, hFC.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)]; exact r2
  have hLs' : LiveSep L' [(s.sp.toNat - 4416, s.sp.toNat + 48)] := by
    refine ExpN.liveSep_ext hA.ext (fun r hr => ?_) (fun r hr => ?_)
    · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
    · simp only [List.mem_singleton] at hr; subst hr; simp only
      exact hrt.of_sub (by omega) (by omega)
  -- segment D
  refine runD impl R hwb ret hret _ s.sp.toNat z.toNat p l c (s.regs 29) b' L' S4 hal (by omega) (by omega)
    (by rw [hac4]; exact Memory.accessible_mono _ hacc (by omega) (by omega)) (hrt.of_sub (by omega) (by omega))
    hLs' (by rw [hac4]; exact hwbacc) (by unfold Apart at hwbz; omega)
    (by simp only [win, outside_cons, outside_nil, and_true] at hwbw; omega) hz48 (by rw [hac4]; exact hzacc)
    (by simp only [win, outside_cons, outside_nil, and_true] at hzW; omega) hzH' hok
    (by rw [r28_4, h283]; exact hA.inv) hA.p64 (by have := hA.lc; have := hA.c40; omega) (by have := hA.c40; omega)
    (hpc4.trans c30) (sp4.trans hsp3) e0 e1 e2 (r29_4.trans (c29.trans (q29.trans a29))) s8 s16 sfp slr hng ?KF
  intro s4 Mw hMw hLw hIw hm4 hsp4 h04 h184 h284 h294
  have h28s : s4.regs 28 = s.regs 28 := h284.trans (r28_4.trans h283)
  obtain ⟨hPost, hcap⟩ := post_of hIP h4416 hab hA hMw hLw (by rw [r28_4, h283] at hIw; exact hIw) s4 hm4
  exact ⟨⟨hsp4.trans hsp0.symm, h28s, h294, h184.trans (r18_4.trans (c18.trans (q18.trans a18)))⟩,
    h04.trans (Expmc.bv_ofNat_toNat _), hPost, hcap⟩

end FvModexp.Arm64.IExp
