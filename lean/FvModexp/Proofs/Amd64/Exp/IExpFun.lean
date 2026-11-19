import FvModexp.Proofs.Amd64.Exp.IExpPost
import FvModexp.Proofs.Amd64.Exp.IExpAtN
import FvModexp.Proofs.Amd64.Exp.IExpP
import FvModexp.Proofs.Amd64.Exp.IExpN
import FvModexp.Proofs.Amd64.Exp.IExpB
import FvModexp.Proofs.Amd64.Exp.IExpC

/-!
# `(*Int).exp` (amd64; agent expmc s77, twin of the arm64 IExpFun): `z.exp(z, y, m, false)` returns `z = z^y mod m`

Composition: segment A (entry → alias test), B (alias test → join), C (→ `nat.expNN`'s entry; its precondition by
`preNF_of`), the call of `nat.expNN` (`ExpN.ensNilF` on `LibNE`, a `Summary` of `LibExpI`: `nSum`), `atN_of` at its
return, segment D (header stores, write barrier, `RET`) and `post_of`.

`ExpSpecA` = `RunIface.ExpSpec` with the precondition's extra conjunct `ExpA` (as divmc's `IMod.ModSpecA` for `Mod`):
`hasADX` readable and the `natOne` word apart from the threshold globals `gA` — facts amd64 `nat.expNN`'s callees
need (coordinator DECISION "amd64 exp-chain extra pre facts", `ExpN.XG`) which `ExpSpec`'s text does not provide;
both are discharged at Run's exp call from the concrete `hasADX` / `natOne` / `gA` addresses. `ExpSpec → ExpSpecA`
is trivial (`ExpSpecA.of_spec`), so `ExpSpecA` is the weaker-pre form of the same contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Amd64.IExp

open FvModexp.Amd64.RunIface (IntPre IntPost IntV IntLenLe OneG maxW ExpBudget lenW PoolG ModX)

/-- the two extra entry facts of amd64 `(*Int).exp` (see the module doc) -/
def ExpA (m : Janus.Arm64.Memory) : Prop :=
  m.accessible Callees.adxAddr 1 false = true ∧ Apart (m.readLE RunIface.natOneA 8) 8 RunIface.gA 32

/-- `RunIface.ExpSpec` with `ExpA` as an extra precondition conjunct -/
def ExpSpecA (impl : List Amd64.Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64),
    Ensures ((Extracted.program.onlySegments RunIface.namesExp).link impl)
      (segAddr Extracted.program (RunIface.P ++ "(*Int).exp")) [z, z, y, mm, 0#64]
      (fun s => (IntPre R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above [z.toNat, y.toNat, mm.toNat] s ∧ 0 < IntV s.mem mm.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ IntLenLe s.mem mm.toNat maxW ∧
        OneG R L s.mem (win s stk above) [z.toNat, y.toNat, mm.toNat] ∧
        PoolG R s.mem (win s stk above) ∧ mm.toNat ≠ 0 ∧ Apart z.toNat 32 RunIface.wbA 4 ∧ ModX s.mem z.toNat) ∧
        ExpA s.mem)
      (fun s s' => s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ s'.regs 0 = z ∧
        IntPost R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above z.toNat (IntV s.mem z.toNat ^ IntV s.mem y.toNat % IntV s.mem mm.toNat) s s')

/-- `ExpSpec` is the stronger contract -/
theorem ExpSpecA.of_spec {impl : List Amd64.Segment} {R : RtInv} {stk above : Nat}
    (h : RunIface.ExpSpec impl R stk above) : ExpSpecA impl R stk above :=
  fun b L z y mm ret hret s hs hpre => h b L z y mm ret hret s hs hpre.1

theorem log2_lt64 {m : Janus.Arm64.Memory} {p n : Nat} (hn : 0 < n) : Nat.log2 (natVal m p n) < 64 * n := by
  rcases Nat.eq_zero_or_pos (natVal m p n) with h | h
  · rw [h]; simp only [Nat.log2_zero]; omega
  · refine (Nat.log2_lt (by omega)).2 ?_
    have := Janus.Arm64.Memory.readLE_lt m p (8 * n)
    simp only [natVal]
    calc m.readLE p (8 * n) < 256 ^ (8 * n) := this
      _ = 2 ^ (64 * n) := by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`(*Int).exp`** (amd64) as `Run` calls it: `z.exp(z, y, m, false)` returns `z` with `z = z^y mod m`
(`ExpSpecA`). Premises: `nat.expNN`'s callees (`DHyps`: division, slow / power-of-two paths, runtime contracts;
`hRem`: `nat.rem`; `hEv`: `nat.expNNEven`; the `newobject` / pool contracts), the write barrier, the stack sizes
(`expNN`'s `K + 0x5d0 ≤ stk`, the barrier's 4096 bytes below `(*Int).exp`'s frame: `0x1138 ≤ stk`) and the callees'
needs and costs within `RunIface.ExpBudget` for operands of at most 128 words (`hneed`, `hbud`; the windows' division
bound `costD xl yl n` is chosen per operand size, TIGHT COSTS). -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : ExpN.DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true) (hnfR : nsR.contains ExpN.fn = false)
    (hKR : stkR ≤ K + 0x388) (hEv : ∀ xl yl n, ExpN.EvH impl R K needS costS xl yl n)
    (hno0 : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput0 : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (hwb : WbLiveContract64 (LibExpI.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {stk above : Nat} (hK : K + 0x5d0 ≤ stk) (hK4 : 41640 ≤ K) (hK20 : K + 0x98 ≤ 2 ^ 20) (h1138 : 0x1138 ≤ stk)
    (hab : 0x30 ≤ above)
    (hneed : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      needR xl n ≤ 2 ^ 16 ∧ needS xl yl n ≤ 2 ^ 16 ∧ needP xl yl lm ≤ 2 ^ 16)
    (hbud : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      24 + (makeCost 1 + max (costR 0 xl n) (makeCost n + max (costS 0 xl yl n) (costP 0 xl yl lm))) ≤
        ExpBudget (max (max xl yl) n) yl ∧
      ExpOdd.OBud costF n (costD xl yl n) xl yl 0 (ExpBudget (max (max xl yl) n) yl - 24 - makeCost n) ∧
      24 + ExpN.NCost (costD xl yl n) costR costS costP xl yl n 0 lm ≤ ExpBudget (max (max xl yl) n) yl) :
    ExpSpecA impl R stk above := by
  intro b L z y mm
  rw [namesExp_eq, ← LibExpI.eq_only, show segAddr Extracted.program (RunIface.P ++ "(*Int).exp") = fnI by decide]
  janus64_ensures_old [FvModexp.Amd64.RunIface.IntPre, FvModexp.Amd64.RunIface.lenW, FvModexp.Amd64.RunIface.IntV, FvModexp.Amd64.RunIface.IntLenLe, FvModexp.Amd64.RunIface.maxW, FvModexp.Amd64.RunIface.OneG, FvModexp.Amd64.win, FvModexp.Amd64.RunIface.PoolG, FvModexp.Amd64.RunIface.wbA, FvModexp.Amd64.RunIface.ModX, FvModexp.Amd64.IExp.ExpA, FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Exp.B, FvModexp.Amd64.RunIface.IntOK, FvModexp.natVal, FvModexp.Amd64.RunIface.natOneA, FvModexp.Amd64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.NatNorm]
  intro ret hret s hs hpre
  janus64_intro hs
  have hr48 := hret.user
  obtain ⟨⟨hIP, hm0, hlz, hly, hlm, hone, hpool, hmA0, hwbz, hzX⟩, hadx, hoG⟩ := hpre
  have hIP' := hIP
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hstk0, hab48, hacc⟩, hal, -, hrt, -, -, hLs, -, -⟩, hsv, hG, -, -, hops, hpw⟩ := hIP'
  simp only [regSP, regG, stackguard0, stackguard0Offset] at hstk0 hab48 hacc hg1 hg2 hg3 hal
  have hoz := hops z.toNat (by simp)
  have hoy := hops y.toNat (by simp)
  have hom := hops mm.toNat (by simp)
  clear hops
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hpw
  obtain ⟨⟨-, ⟨hzmA, -, -, hzmArr⟩⟩, -⟩ := hpw
  obtain ⟨⟨hz0, -, hz48, hzacc, hzH, hzL, -, -, hzap, -⟩, hzW, -, -, -, -, -⟩ := hoz
  obtain ⟨⟨hy0, -, hy48, hyacc, -, -, -, -, -, -⟩, hyW, -, -, -, -, -⟩ := hoy
  obtain ⟨⟨-, -, hm48, hmacc, -, hmL, -, -, -, -⟩, hmW, -, -, -, -, -⟩ := hom
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
  obtain ⟨hbP, hbO, hbC⟩ := hbud zl yl n _ hzl128 hyl128 hn0 hn128 hlm64
  rw [← hB] at hbP hbO hbC
  generalize ht : (s.regs 4).toNat = t at hstk0 hab48 hacc hg3 hal
  have hsp0 : s.regs 4 = BitVec.ofNat 64 t := by rw [← ht, Expmc.bv_ofNat_toNat]
  have hst : stk ≤ t := hstk0
  have hzS : z.toNat + 32 ≤ t - stk ∨ t + above ≤ z.toNat := by
    simp only [win, ht, outside_cons, outside_nil, and_true] at hzW; omega
  have hyS : y.toNat + 32 ≤ t - stk ∨ t + above ≤ y.toNat := by
    simp only [win, ht, outside_cons, outside_nil, and_true] at hyW; omega
  have hmS : mm.toNat + 32 ≤ t - stk ∨ t + above ≤ mm.toNat := by
    simp only [win, ht, outside_cons, outside_nil, and_true] at hmW; omega
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
  refine returns_of_reaches (runA impl ret hret _ t (s.regs 14).toNat z.toNat y.toNat mm.toNat
    zp zl zc yp yl yc s.mem (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) hz48
    (Janus.Arm64.Memory.accessible_weaken _ hzacc) (by omega) hy48 (Janus.Arm64.Memory.accessible_weaken _ hyacc)
    (by omega) (fun h => hmA0 (by rw [h])) mm.isLt (by intro h; have := hzmA; unfold Apart at this; omega)
    hzp hzl hzc hy0 hyp hyl hyc
    s h_rip hsp0 (h_a0.trans (Expmc.bv_ofNat_toNat _).symm) (h_a1.trans (Expmc.bv_ofNat_toNat _).symm)
    (h_a2.trans (Expmc.bv_ofNat_toNat _).symm) (h_a3.trans (Expmc.bv_ofNat_toNat _).symm) h_a4
    (Expmc.bv_ofNat_toNat _).symm rfl ?KA)
  intro S1 M1 p1 sp1 a0 a3 a7 a6 a2 a11 a12 a13 a15 a1 a5 a14 afs adf ax am hF1 hrg1 r1 r2 r3 r4 r5 r6 r7
  have rd1 : ∀ a k, (a + k ≤ t - 0x130 ∨ t + 0x30 ≤ a) → M1.readLE a k = s.mem.readLE a k :=
    fun a k h => hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hac1 : ∀ a k w, M1.accessible a k w = s.mem.accessible a k w := hF1.accessible
  have ez8 : M1.readLE (z.toNat + 8) 8 = zp := (rd1 _ _ (by omega)).trans hzp
  have ez16 : M1.readLE (z.toNat + 16) 8 = zl := (rd1 _ _ (by omega)).trans hzl
  have ez24 : M1.readLE (z.toNat + 24) 8 = zc := (rd1 _ _ (by omega)).trans hzc
  have em8 : M1.readLE (mm.toNat + 8) 8 = mp := (rd1 _ _ (by omega)).trans hmp
  have em16 : M1.readLE (mm.toNat + 16) 8 = n := (rd1 _ _ (by omega)).trans hmn
  have em24 : M1.readLE (mm.toNat + 24) 8 = mc := (rd1 _ _ (by omega)).trans hmc
  have hacX : M1.accessible (t + 0x10) 8 false = true := by
    rw [hac1]; exact Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
  -- segment B
  refine runB impl ret hret _ t z.toNat mm.toNat zp zc mp mc M1 (by omega) (by omega) hz48
    (by rw [hac1]; exact Janus.Arm64.Memory.accessible_weaken _ hzacc) hm48
    (by rw [hac1]; exact Janus.Arm64.Memory.accessible_weaken _ hmacc)
    hacX r3
    ez8 ez24 em8 em24 hali S1 p1 sp1 a0 a3 a7 am ?KB
  intro S2 q1 q4 q0 q1' q3 q5 q6 q7 q11 q12 q13 q14 q15 q2 q8 qfs qdf qx qm
  -- segment C
  refine runC impl ret hret _ t z.toNat mm.toNat zp zl zc yp yl yc mp n mc M1 (by omega) (by omega)
    (by rw [hac1]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hz48
    (by rw [hac1]; exact Janus.Arm64.Memory.accessible_weaken _ hzacc) (by omega) hm48
    (by rw [hac1]; exact Janus.Arm64.Memory.accessible_weaken _ hmacc) ez8 ez16 ez24 em8 em16 em24
    (hyp ▸ Janus.Arm64.Memory.readLE_lt _ _ _) (hyl ▸ Janus.Arm64.Memory.readLE_lt _ _ _)
    (hyc ▸ Janus.Arm64.Memory.readLE_lt _ _ _) S2 q1 (q4.trans sp1)
    (q0.trans a0) q2 (q6.trans a6) (q15.trans a15) (q13.trans a13) (q1'.trans a1) qm ?KC
  intro S3 M3 c1 c_sp c0 c3 c1' c7 c6 c8 c9 c10 c5 c14 cfs cdf cx cm hFC hrgC r_ra f1 f2 f3 f4 f5 f6 g1 g2 g3
  have hF3 : MemFrame s.mem M3 [(t - 0x138, t), (t + 8, t + 0x30)] :=
    hF1.trans hFC fun a k h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢; exact ⟨⟨by omega, h.2⟩, by omega, by omega, by omega⟩
  have hrg3 : S3.mem.regions = s.mem.regions := by rw [cm, hrgC, hrg1]
  have h143 : S3.regs 14 = s.regs 14 := c14.trans (q14.trans a14)
  have hsp3 : S3.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x138) := by rw [ht]; exact c_sp
  have hP := preNF_of (costF := costF) (costD := costD zl yl n) (needR := needR) (costR := costR) (needS := needS)
    (needP := needP) (costS := costS) (costP := costP) hIP hm0 hlz hly hlm hone hpool hzX hadx hoG
    hK hK4 hK20 hab hzp hzl hzc hyp hyl hyc hmp hmn hmc hnR hnS hnP hbP (by
      have := hbO; rwa [hB] at this ⊢) hsp3 h143 (cfs.trans (qfs.trans afs))
    (cx.trans (qx.trans (ax.trans h_x15))) (cdf.trans (qdf.trans (adf.trans h_df)))
    (by rw [ht, cm]; exact hF3) hrg3 (by rw [ht, cm]; exact f1) (by rw [ht, cm]; exact f2) (by rw [ht, cm]; exact f3)
    (by rw [ht, cm]; exact f4) (by rw [ht, cm]; exact f5) (by rw [ht, cm]; exact f6)
  -- the call of `nat.expNN`
  refine Reaches.call_regions ((nSum impl hap R H hRem hnsR hnfR hKR hEv hno0 hget0 hput0 b L
    zp zl zc 0 zp zl zc yp yl yc mp n mc 0).withExit hret) c1 ⟨?_, cx.trans (qx.trans (ax.trans h_x15)), ?_,
      cdf.trans (qdf.trans (adf.trans h_df)), hP⟩ fun S4 hpc4 hq hrg4 => ?_
  · rw [c_sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), cm, r_ra]; exact raN_ret impl hap
  · simp [ArgsFrom64, argReg, intArgRegs, c0, c3, c1', c7, c6, c8, c9, c10, q8, a2, q11, q12, a11, a12]
  obtain ⟨⟨sp4, rbp4, r14_4, x15_4⟩, hpost⟩ := hq
  have hfs4 := hpost.1
  have hdf4 := hpost.2.1
  obtain ⟨hslot, p, l, c, b', L', e0, e1, e2, hA⟩ := atN_of hIP hK hab hzp hzl hzc hyp hyl hmp hmn hbC hsp3 h143
    (by rw [ht, cm]; exact hF3) hpost
  rw [ht] at hslot
  have hac4 : ∀ a k w, S4.mem.accessible a k w = s.mem.accessible a k w := hA.mf.accessible
  have hzH' : Held R L' z.toNat 32 := hA.ext.held hzH
  have hng : S4.mem.readLE z.toNat 1 = 0 := by
    rw [AtN.hdr hA hzH hzW hzap _ _ (Nat.le_refl _) (by omega)]; exact hz0
  have s8 : S4.mem.readLE (t + 8) 8 = z.toNat := by
    rw [hslot _ _ (by omega) (by omega), cm, hFC.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)]; exact r2
  have s16 : S4.mem.readLE (t + 0x10) 8 = z.toNat := by
    rw [hslot _ _ (by omega) (by omega), cm, hFC.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)]; exact r3
  have sfp : S4.mem.readLE (t - 8) 8 = (s.regs 5).toNat := by
    rw [hslot _ _ (by omega) (by omega), cm, hFC.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega)]; exact r1
  have slr : S4.mem.readLE t 8 = ret := by
    rw [hslot _ _ (by omega) (by omega), cm, hFC.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega), hF1.readLE _ _ (by
      simp only [outside_cons, outside_nil, and_true]; omega), ← ht]; exact h_ret
  have hLs' : LiveSep L' [(t - 0x1138, t + 0x30)] := by
    refine DivNil.liveSep_ext hA.ext (fun r hr => ?_) (fun r hr => ?_)
    · have := hLs r hr; simp only [win, ht, outside_cons, outside_nil, and_true] at this ⊢; omega
    · simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [← ht] at hst ⊢; exact hrt.of_sub (by omega) (by omega)
  have hsp4 : S4.regs 4 = BitVec.ofNat 64 (t - 0x130) := by
    have e : (S4.regs 4).toNat = ((S3.regs 4).toNat + 8) % 2 ^ 64 := by rw [sp4, BitVec.toNat_add]; rfl
    apply BitVec.eq_of_toNat_eq
    rw [e, c_sp, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  have hpc4' : S4.rip = BitVec.ofNat 64 raN := by
    rw [hpc4]; simp only [retAddrOf]; rw [c_sp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), cm, r_ra]
  -- segment D
  have d1 : S4.mem.accessible (t - 0x1138) (0x1138 + 0x30) true = true := by
    rw [hac4]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have d2 : Outside (t - 0x1138) (0x1138 + 0x30) R.rt := by
    rw [← ht] at hst ⊢; exact hrt.of_sub (by omega) (by omega)
  have d3 : S4.mem.accessible RunIface.wbA 4 false = true := by rw [hac4]; exact hwbacc
  have d4 : RunIface.wbA + 4 ≤ z.toNat ∨ z.toNat + 32 ≤ RunIface.wbA := hwbz.symm
  have d5 : S4.mem.accessible z.toNat 32 true = true := by rw [hac4]; exact hzacc
  have d6 : z.toNat + 32 ≤ t - 0x1138 ∨ t + 0x30 ≤ z.toNat := by omega
  have d7 : R.inv b' L' (S4.regs 14).toNat (view R.rt L' S4.mem) := by rw [r14_4, h143]; exact hA.inv
  have d8 : l < 2 ^ 64 := by have := hA.lc; have := hA.c40; omega
  have d9 : c < 2 ^ 64 := by have := hA.c40; omega
  have d10 : 0x1140 ≤ t := by omega
  have d11 : t + 0x30 ≤ 2 ^ 48 := by omega
  refine runD impl R hwb ret hret _ t z.toNat p l c (s.regs 5).toNat b' L' S4 hal d10 d11 d1 d2
    hLs' d3 d4 hz48 d5 d6 hzH' hok d7 hA.p64 d8 d9 hpc4' hsp4 e0 e1 e2 s8 s16 sfp slr hng ?KF
  intro s4 Mw hMw hLw hIw hm4 hsp4' h04 h54 h144 hfs4' hdf4' hx4
  have h14s : s4.regs 14 = s.regs 14 := h144.trans (r14_4.trans h143)
  have hMw' : MemFrame (hdrW S4.mem z.toNat l c) Mw
      (R.rt ++ [((s.regs 4).toNat - 0x1138, (s.regs 4).toNat - 0x130)]) := by rw [ht]; exact hMw
  have hPost := post_of hIP h1138 hab hA hMw' hLw (by rw [r14_4, h143] at hIw; exact hIw) s4 hm4
  refine ⟨⟨?_, ?_, h14s, hx4.trans (x15_4.trans (cx.trans (qx.trans ax)))⟩,
    hfs4'.trans (hfs4.trans (cfs.trans (qfs.trans afs))), hdf4'.trans (hdf4.trans (cdf.trans (qdf.trans adf))),
    h04.trans (Expmc.bv_ofNat_toNat _), hPost.1⟩
  · show s4.regs 4 = s.regs 4 + 8#64
    rw [hsp4', hsp0]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · show s4.regs 5 = s.regs 5
    rw [h54, Expmc.bv_ofNat_toNat]

end FvModexp.Amd64.IExp
