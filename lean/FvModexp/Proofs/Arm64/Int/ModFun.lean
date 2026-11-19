import FvModexp.Proofs.Arm64.Int.ModA2
import FvModexp.Proofs.Arm64.Int.ModB
import FvModexp.Proofs.Arm64.Int.ModP
import FvModexp.Proofs.Arm64.Int.ModPost
import FvModexp.Proofs.Arm64.Exp.CallW

/-!
# `(*Int).Mod` (arm64): `z.Mod(z, y)` returns `z = z mod y` (`ModSpecX` = `RunIface.ModSpec` + `ModX`)

Composition: segment A1 (entry → alias join), A2 (→ `nat.div`'s entry, through `QuoRem`'s prologue; its precondition
by `divPre_of`), the call of `nat.div` (premise `DivHypM`, an `Ensures` on `onlySegments nsD`, moved to `LibMod` by
`Ensures.toSummaryIn`), segment B (QuoRem's stores, `gcWriteBarrier4`, `RET`s) and `atD_of` / `post_of`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Arm64.IMod

open FvModexp.Arm64.RunIface (IntPre IntPost IntV IntLenLe maxW ModBudget lenW)

set_option maxRecDepth 20000 in
/-- the return address of the `nat.div` call (`QuoRem`+0x5c) is outside any program without `QuoRem` -/
theorem raD_ret (impl : List Segment) (hap : ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains Extracted.seg6.name = false) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) raD :=
  CallW.retAddr_restrict hap (cs := Extracted.seg6)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn 23
    (by decide) (by decide) (by decide)

/-- an opaque wrapper: `omega` does not case-split on a boxed disjunction -/
structure Box (P : Prop) : Prop where
  unbox : P

theorem bv_toNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem bv_mod (n : Nat) : BitVec.ofNat 64 n = BitVec.ofNat 64 (n % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`(*Int).Mod`** (arm64) as `Run` calls it: `z.Mod(z, y)` returns `z` with `z = z mod y`, `y` unchanged
(`ModSpecX`). Premises: `nat.div` as `QuoRem` calls it (`DivHypM`: `stk == nil`, `z2 = u`; on any program `nsD ⊆
namesMod` without `QuoRem`, window `stkD + 304 ≤ stk`, `aboveD ≤ 120`), the 4-slot write barrier, the stack (the
barrier's 4096 bytes below QuoRem's frame) and `div`'s cost within `ModBudget` for operands of at most 128 words. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {nsD : List String} {stkD aboveD : Nat} {cost : Nat → Nat → Nat}
    (hD : DivHypM impl R nsD stkD aboveD cost)
    (hnsD : ∀ x, nsD.contains x = true → LibMod.names.contains x = true)
    (hnsQ : nsD.contains Extracted.seg6.name = false)
    (hwb : WbLiveContract (LibMod.program.link impl) (cA "runtime.gcWriteBarrier4") 4096 R 4)
    {stk above : Nat} (hstkD : stkD + 304 ≤ stk) (habD : aboveD ≤ 120) (h4448 : 4448 ≤ stk) (hab : 32 ≤ above)
    (hbud : ∀ ul vl, ul ≤ 128 → vl ≤ 128 → cost ul vl ≤ ModBudget (max ul vl)) :
    ModSpecX impl R stk above := by
  intro b L z y
  rw [namesMod_eq, ← LibMod.eq_only, show segAddr Extracted.program (RunIface.P ++ "(*Int).Mod") = fnM by decide]
  janus_ensures_old [FvModexp.Arm64.RunIface.IntPre, FvModexp.Arm64.RunIface.lenW, FvModexp.Arm64.RunIface.IntV, FvModexp.Arm64.RunIface.IntLenLe, FvModexp.Arm64.RunIface.maxW, FvModexp.Arm64.RunIface.PoolG, FvModexp.Arm64.win, FvModexp.Arm64.IMod.ModX, FvModexp.Arm64.CallEnv, FvModexp.Arm64.RunIface.Globals, FvModexp.Arm64.RunIface.IntOK, FvModexp.natVal, FvModexp.Arm64.RunIface.stackPoolA, Janus.Spec.Pool.newOffset, FvModexp.Arm64.RunIface.gA, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.RunIface.wbA, FvModexp.NatLive, FvModexp.NatNorm]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  obtain ⟨hIP, hyv, hlz, hly, hpool, hX⟩ := hpre
  have hIP' := hIP
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hstk, hab48, hacc⟩, -, hrt, hgap, -, hLs, -⟩, hsv, hG, -, -, hops, hpw⟩ := hIP'
  have hoz := hops z.toNat (by simp)
  have hoy := hops y.toNat (by simp)
  clear hops
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
    and_true] at hpw
  obtain ⟨⟨hzyH, -, -, hzyArr⟩, -⟩ := hpw
  obtain ⟨⟨hz0, -, hz48, hzacc, hzH, hzL, -, -, hzap, -⟩, hzW, hzO, -, -⟩ := hoz
  obtain ⟨⟨-, -, hy48, hyacc, hyH, hyL, -, -, -, -⟩, hyW, -, -, -⟩ := hoy
  have hok : R.ok (cA "runtime.gcWriteBarrier4") [4] := hsv.2.2.2.2.2.2.1 _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwbacc, -, hwbw⟩ := id hG
  generalize hzp : s.mem.readLE (z.toNat + 8) 8 = zp at hzL hzyArr hzap hzO
  generalize hzc : s.mem.readLE (z.toNat + 24) 8 = zc at hzL hzyArr hzap hzO
  generalize hzl : s.mem.readLE (z.toNat + 16) 8 = zl
  generalize hyp : s.mem.readLE (y.toNat + 8) 8 = yp at hyL hzyArr
  generalize hyl : s.mem.readLE (y.toNat + 16) 8 = yl
  generalize hyc : s.mem.readLE (y.toNat + 24) 8 = yc at hyL hzyArr
  have hzl128 : zl ≤ 128 := by have := hlz; simp only [IntLenLe, maxW] at this; rw [hzl] at this; exact this
  have hyl128 : yl ≤ 128 := by have := hly; simp only [IntLenLe, maxW] at this; rw [hyl] at this; exact this
  have hB : ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) = ModBudget (max zl yl) := by
    simp only [lenW]; rw [hzl, hyl]
  have hcost : cost zl yl ≤ ModBudget (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) := by
    rw [hB]; exact hbud zl yl hzl128 hyl128
  have hst : stk ≤ s.sp.toNat := hstk
  have hsp0 : s.sp = BitVec.ofNat 64 s.sp.toNat := (Expmc.bv_ofNat_toNat _).symm
  have h280 : s.regs 28 = BitVec.ofNat 64 (s.regs 28).toNat := (Expmc.bv_ofNat_toNat _).symm
  have hzS : z.toNat + 32 ≤ s.sp.toNat - stk ∨ s.sp.toNat + above ≤ z.toNat := by
    simp only [win, outside_cons, outside_nil, and_true] at hzW; omega
  have hyS : y.toNat + 32 ≤ s.sp.toNat - stk ∨ s.sp.toNat + above ≤ y.toNat := by
    simp only [win, outside_cons, outside_nil, and_true] at hyW; omega
  have hgS : (s.regs 28).toNat + 24 ≤ s.sp.toNat - stk ∨ s.sp.toNat + above ≤ (s.regs 28).toNat + 16 := by
    unfold Apart at hgap; omega
  unfold Apart at hzyH
  have hali : zc = 0 ∨ yc = 0 ∨ lastA zp zc ≠ lastA yp yc := by
    rcases Nat.eq_zero_or_pos zc with h1 | h1
    · exact Or.inl h1
    rcases Nat.eq_zero_or_pos yc with h2 | h2
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ?_)
    have ha := hzyArr h1 h2; unfold Apart at ha
    have hz' := (hzL h1).2.2.2; have hy' := (hyL h2).2.2.2
    simp only [lastA]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  -- segment A1
  refine returns_of_reaches (runA1 impl ret hret _ s.sp.toNat (s.regs 28).toNat ret z.toNat y.toNat
    zp zc yp yc (s.regs 29) s.mem hal (by omega) (by omega)
    (Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) hr48 hz48
    (Memory.accessible_weaken _ hzacc) (by omega) hy48 (Memory.accessible_weaken _ hyacc) (by omega)
    (by omega) hzp hzc hyp hyc hali
    s h_pc hsp0 (h_x0.trans (Expmc.bv_ofNat_toNat _).symm) (h_x1.trans (Expmc.bv_ofNat_toNat _).symm)
    (h_x2.trans (Expmc.bv_ofNat_toNat _).symm) h280 rfl h_lr rfl ?KA)
  intro S1 M1 a1pc a1sp a10 a11 a12 a14 a118 a128 a129 a130 hm1 hF1 hrg1 r1 r2 r3
  have rd1 : ∀ a k, (a + k ≤ s.sp.toNat - 184 ∨ s.sp.toNat + 16 ≤ a) → M1.readLE a k = s.mem.readLE a k :=
    fun a k h => hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hac1 : ∀ a k w, M1.accessible a k w = s.mem.accessible a k w := hF1.accessible
  -- segment A2
  refine runA2 impl ret hret _ s.sp.toNat (s.regs 28).toNat z.toNat y.toNat zp zl zc yp yl yc M1 hal (by omega)
    (by omega) (by rw [hac1]; exact Memory.accessible_mono _ hacc (by omega) (by omega)) hg1
    (by rw [hac1]; exact hg2) (by rw [rd1 _ _ (by omega)]; omega) (by omega) hz48
    (by rw [hac1]; exact Memory.accessible_weaken _ hzacc) (by omega) hy48
    (by rw [hac1]; exact Memory.accessible_weaken _ hyacc) (by omega)
    ((rd1 _ _ (by omega)).trans hzp) ((rd1 _ _ (by omega)).trans hzl) ((rd1 _ _ (by omega)).trans hzc)
    ((rd1 _ _ (by omega)).trans hyp) ((rd1 _ _ (by omega)).trans hyl) ((rd1 _ _ (by omega)).trans hyc)
    S1 a1pc a1sp a10 a11 a12 a14 (a128.trans h280) a129 hm1 ?KB
  intro S3 M3 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c18 c28 c29 c30 cm hFC hrgC f312 f304 f168 f160
    f152 f144 f64
  have hF3 : MemFrame s.mem M3 [(s.sp.toNat - 312, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)] :=
    hF1.trans hFC fun a k h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  rw [← cm] at hF3
  have hrg3 : S3.mem.regions = s.mem.regions := by rw [cm, hrgC, hrg1]
  have h283 : S3.regs 28 = s.regs 28 := c28.trans a128
  have hsp3 : S3.sp.toNat = s.sp.toNat - 304 := by rw [c2, BitVec.toNat_ofNat]; omega
  have hP := divPre_of (cost := cost) hIP hyv hpool hX hstkD (by omega) habD hab hzp hzl hzc hyp hyl hyc hzl128
    hyl128 hcost hsp3 h283 hrg3 hF3
  -- the call of `nat.div`
  have hzp64 : zp < 2 ^ 64 := hzp ▸ Memory.readLE_lt _ _ _
  have hzl64 : zl < 2 ^ 64 := hzl ▸ Memory.readLE_lt _ _ _
  have hzc64 : zc < 2 ^ 64 := hzc ▸ Memory.readLE_lt _ _ _
  have hyp64 : yp < 2 ^ 64 := hyp ▸ Memory.readLE_lt _ _ _
  have hyl64 : yl < 2 ^ 64 := hyl ▸ Memory.readLE_lt _ _ _
  have hyc64 : yc < 2 ^ 64 := hyc ▸ Memory.readLE_lt _ _ _
  have hS := Ensures.toSummaryIn (hD b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc)) (noExit_restrict hap nsD)
    (codeIn_restrict_mono hap hnsD)
  rw [← LibMod.eq_only, show segAddr Extracted.program ExpHyp.fnDiv = fnD by decide] at hS
  simp only [bv_toNat hzp64, bv_toNat hzl64, bv_toNat hzc64, bv_toNat hyp64, bv_toNat hyl64, bv_toNat hyc64] at hS
  refine Reaches.call_regions (hS.withExit hret) c1 ⟨?_, ⟨c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
    trivial⟩, hP⟩ fun S4 hpc4 hq hrg4 => ?_
  · rw [c30, BitVec.toNat_ofNat]; exact raD_ret impl hap hnsQ
  obtain ⟨⟨sp4, r28_4, r29_4, r18_4⟩, q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L', b', hr, hrt', hMF, hLF⟩ := hq
  have hx := hrt'.1
  have hS4 : S4.sp.toNat = s.sp.toNat - 304 := by rw [sp4]; exact hsp3
  have h284 : S4.regs 28 = s.regs 28 := r28_4.trans h283
  have hz' : 0 < zc → zp + 8 * zc ≤ s.sp.toNat - stk ∨ s.sp.toNat + above ≤ zp := fun h => by
    have := hzO h; simp only [win, outside_cons, outside_nil, and_true] at this; exact this
  -- what `div` keeps: its frame misses the slots `[t - 312, t - 296)` and `[t - 184, t + 16)`
  have hslot : ∀ a k, ((s.sp.toNat - 312 ≤ a ∧ a + k ≤ s.sp.toNat - 296) ∨
      (s.sp.toNat - 184 ≤ a ∧ a + k ≤ s.sp.toNat + 16)) → S4.mem.readLE a k = S3.mem.readLE a k := by
    intro a k h
    refine Memory.readLE_congr fun i hi => FvModexp.ByteFrame.MemFrame.byte hMF ?_
    rw [outside_append, outside_append]
    refine ⟨⟨hrt.of_sub (by omega) (by omega), ?_⟩, ?_⟩
    · simp only [winA, hsp3, outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]
      rcases Nat.eq_zero_or_pos zc with h0 | h0
      · subst h0; omega
      · have := hz' h0; omega
  have rdA : ∀ a k, (a + k ≤ s.sp.toNat - 184 ∨ s.sp.toNat + 16 ≤ a) →
      (a + k ≤ s.sp.toNat - 312 ∨ s.sp.toNat - 296 ≤ a) → (a + k ≤ s.sp.toNat - 168 ∨ s.sp.toNat - 136 ≤ a) →
      (a + k ≤ s.sp.toNat - 88 ∨ s.sp.toNat - 40 ≤ a) → S3.mem.readLE a k = s.mem.readLE a k := by
    intro a k h1 h2 h3 h4
    rw [cm, hFC.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact rd1 a k h1
  have s168 : S4.mem.readLE (s.sp.toNat - 168) 8 = s.sp.toNat - 72 := by
    rw [hslot _ _ (Or.inr ⟨by omega, by omega⟩), cm]; exact f168
  have s160 : S4.mem.readLE (s.sp.toNat - 160) 8 = z.toNat := by
    rw [hslot _ _ (Or.inr ⟨by omega, by omega⟩), cm]; exact f160
  have s152 : S4.mem.readLE (s.sp.toNat - 152) 8 = y.toNat := by
    rw [hslot _ _ (Or.inr ⟨by omega, by omega⟩), cm]; exact f152
  have s144 : S4.mem.readLE (s.sp.toNat - 144) 8 = z.toNat := by
    rw [hslot _ _ (Or.inr ⟨by omega, by omega⟩), cm]; exact f144
  have sfq : S4.mem.readLE (s.sp.toNat - 312) 8 = s.sp.toNat - 184 := by
    rw [hslot _ _ (Or.inl ⟨by omega, by omega⟩), cm]; exact f312
  have slq : S4.mem.readLE (s.sp.toNat - 304) 8 = raQ := by
    rw [hslot _ _ (Or.inl ⟨by omega, by omega⟩), cm]; exact f304
  have rdC : ∀ a k, (a + k ≤ s.sp.toNat - 312 ∨ s.sp.toNat - 296 ≤ a) →
      (a + k ≤ s.sp.toNat - 168 ∨ s.sp.toNat - 136 ≤ a) → (a + k ≤ s.sp.toNat - 88 ∨ s.sp.toNat - 40 ≤ a) →
      M3.readLE a k = M1.readLE a k := fun a k h2 h3 h4 =>
    hFC.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have sfp : S4.mem.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat := by
    rw [hslot _ _ (Or.inr ⟨by omega, by omega⟩), cm, rdC _ _ (by omega) (by omega) (by omega)]; exact r1
  have slr : S4.mem.readLE (s.sp.toNat - 176) 8 = ret := by
    rw [hslot _ _ (Or.inr ⟨by omega, by omega⟩), cm, rdC _ _ (by omega) (by omega) (by omega)]; exact r2
  have s8 : S4.mem.readLE (s.sp.toNat + 8) 8 = z.toNat := by
    rw [hslot _ _ (Or.inr ⟨by omega, by omega⟩), cm, rdC _ _ (by omega) (by omega) (by omega)]; exact r3
  clear rdA
  have hzS4 : z.toNat + 32 ≤ s.sp.toNat - 4400 ∨ s.sp.toNat + 32 ≤ z.toNat := by
    clear hyS hgS hzyH hali; rcases hzS with h | h <;> omega
  have hyS4 : y.toNat + 32 ≤ s.sp.toNat - 4400 ∨ s.sp.toNat + 32 ≤ y.toNat := by
    clear hzS hgS hzyH hali; rcases hyS with h | h <;> omega
  have bzS := Box.mk hzS4
  have byS := Box.mk hyS4
  have bzy := Box.mk hzyH
  have bzW := Box.mk hzS
  have h4400 : 4400 ≤ stk := by omega
  clear hzS hyS hgS hzyH hali hzS4 hyS4
  -- `z`'s header (neg byte) is kept by `div`
  have hzb : ∀ i, i < 32 → S4.mem.bytes (z.toNat + i) = s.mem.bytes (z.toNat + i) := by
    intro i hi
    have hZ : Outside (z.toNat + i) 1 [(zp, zp + 8 * zc)] := by
      simp only [outside_cons, outside_nil, and_true]
      rcases Nat.eq_zero_or_pos zc with h0 | h0
      · subst h0; omega
      · have := hzap h0; unfold Apart at this; omega
    have e3 : S3.mem.bytes (z.toNat + i) = s.mem.bytes (z.toNat + i) :=
      FvModexp.ByteFrame.MemFrame.byte hF3 (by
        have := bzS.unbox; simp only [outside_cons, outside_nil, and_true]; omega)
    rw [← e3]
    rcases hzH with hi' | ho
    · exact FvModexp.ByteFrame.LiveFrame.byte hLF (hi'.sub (by omega) (by omega)) hZ
    · refine FvModexp.ByteFrame.MemFrame.byte hMF ?_
      rw [outside_append, outside_append]
      refine ⟨⟨ho.of_sub (by omega) (by omega), ?_⟩, hZ⟩
      have := bzW.unbox; simp only [winA, hsp3, outside_cons, outside_nil, and_true]; omega
  have hng : S4.mem.readLE z.toNat 1 = 0 := by
    rw [Memory.readLE_congr (m' := s.mem) fun i hi => by have := hzb i (by omega); exact this]; exact hz0
  have hr64 : r < 2 ^ 64 := by
    obtain ⟨-, -, -, -, hnl, hd⟩ := hr
    rcases Nat.eq_zero_or_pos rc with h0 | h0
    · rcases hd with ⟨rfl, -⟩ | ⟨h1, -⟩
      · exact hzp64
      · omega
    · have := (hnl h0).2.2.2; omega
  have hrc40 : rc < 2 ^ 40 := hr.2.2.2.1
  have hrlc : rl ≤ rc := hr.2.2.1
  have hacc4 : ∀ a k w, S4.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hMF.accessible, hF3.accessible]
  have hLs4 : LiveSep L' [(s.sp.toNat - 4400, s.sp.toNat + 32)] := by
    refine hx.liveSep (fun r hr => ?_) (fun r hr => ?_)
    · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
    · simp only [List.mem_singleton] at hr; subst hr; simp only
      exact hrt.of_sub (by omega) (by omega)
  have hrt44 : Outside (s.sp.toNat - 4400) (4400 + 32) R.rt := hrt.of_sub (by omega) (by omega)
  have hinv4 : R.inv b' L' (S4.regs 28).toNat (view R.rt L' S4.mem) := by rw [r28_4]; exact hrt'.2.2
  -- segment B
  refine runB impl R hwb ret hret _ s.sp.toNat z.toNat y.toNat (q % 2 ^ 64) (ql % 2 ^ 64) (qc % 2 ^ 64) r rl rc
    (s.regs 29) b' L' S4 hal (by omega) (by omega)
    (by rw [hacc4]; exact Memory.accessible_mono _ hacc (by omega) (by omega)) hrt44 hLs4
    (by rw [hacc4]; exact hwbacc) (by simp only [win, outside_cons, outside_nil, and_true] at hwbw; omega)
    hz48 (by rw [hacc4]; exact hzacc) bzS.unbox (hx.held hzH) hy48 (by rw [hacc4]; exact Memory.accessible_weaken _ hyacc) byS.unbox
    (hx.held hyH) bzy.unbox hok hinv4 (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    hr64 (by omega) (by omega) (hpc4.trans c30) (by rw [sp4, c2])
    (e0.trans (bv_mod q)) (e1.trans (bv_mod ql)) (e2.trans (bv_mod qc)) e3 e4 e5 (r29_4.trans c29)
    s168 s160 s152 s144 sfq slq sfp slr s8 hng ?KF
  intro s4 Mw qn ql' rl' hm hql hrl hMw hLw hIw hsp4 h04 h184 h284 h294
  subst hql hrl
  have hA := atD_of hIP h4400 hab hstkD habD hzp hzl hzc hyp hyl hcost hsp3 h283 hF3 hr hrt' hMF hLF hr64 hMw hLw
    (by rw [r28_4, h283] at hIw; exact hIw)
  obtain ⟨hPost, hyv'⟩ := post_of hIP h4400 hab hA s4 hm
  exact ⟨⟨hsp4.trans hsp0.symm, h284.trans (r28_4.trans h283), h294, h184.trans (r18_4.trans (c18.trans a118))⟩,
    h04.trans (Expmc.bv_ofNat_toNat _), hPost, hyv'⟩

end FvModexp.Arm64.IMod
