import FvModexp.Proofs.Amd64.Exp.NSlowP
import FvModexp.Proofs.Amd64.Exp.OddEns
import FvModexp.Proofs.Common.StkFrame

/-!
# `nat.expNN` (amd64): the odd-modulus path — `z.expNNOdd(stk, x, y, m)` (nat.go:708-710) to expNN's return (agent
expmc s71; twin of `Arm64.ExpN.oddPath`)

From `expNNOdd`'s entry (`NDisp.disp`'s `KO`, `m[0]` odd, after the make: context `ZM`): `ExpOdd.ens` (on `LibOdd`,
which leaves out `nat.expNN`) at `K - 8` with `ExpOdd.PreD` at the entry (`opre_at`: `EPreA`'s window
`[sp - 8 - (K - 8), sp + 0x3f8)` = `[sp - K, sp + 0x3f8)` lies in expNN's `[sp - K, sp + 0x510)`, same `sp`),
`ExpOdd.PostD` as a `CPostG` (`cpostG_odd`), then `callC`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Amd64.ExpN

/-- `ExpOdd.OBud` is monotone in the budget (as asm's `EvNP.OBud.mono`) -/
theorem oBud_mono {costF : Nat → Nat → Nat → Nat} {n costD xl ylen l b b' : Nat}
    (h : ExpOdd.OBud costF n costD xl ylen l b) (hb : b ≤ b') : ExpOdd.OBud costF n costD xl ylen l b' := by
  unfold ExpOdd.OBud at h ⊢
  by_cases hy : 1 < ylen
  · simp only [hy, ↓reduceIte] at h ⊢; exact ⟨W4En.XnB.mono h.1 (by omega), by omega⟩
  · simp only [hy, ↓reduceIte] at h ⊢; exact ⟨W2En.XnB.mono h.1 (by omega), by omega⟩

set_option maxRecDepth 20000 in
/-- an entry operand (`NE` at `M0`, `L`) as an `expNNOdd` operand (`OE` at the callee memory `M`, `L1`, `K - 8`) -/
theorem oe_at {R : RtInv} {L L1 : List (Nat × Nat)} {sp K st a k : Nat} {M0 M : Memory} (hO : NE R L sp K st M0 a k)
    (hx : LiveExt R L L1) (hK : 8 ≤ K) (ew : stW M st = stW M0 st) (el : stLen M st = stLen M0 st)
    (ec : stCap M st = stCap M0 st) :
    W4En.OE R L1 sp (K - 8) st M a k := by
  obtain ⟨hH, hw, hst, hfr⟩ := hO
  refine ⟨hx.held hH, by unfold Apart at hw ⊢; omega, hst, ?_⟩
  show Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
  rw [ew, el, ec]; exact hfr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `ExpW4.EPreA` at `expNNOdd`'s entry (`RSP = sp + 0x388`, `K - 8`) from `NPre` and the make's context -/
theorem opre_at {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat} {s S : State} {L1 : List (Nat × Nat)}
    {b1 zq zcq mk : Nat}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hZ : ZM R b L g fs sp K zp zc st xp xl yp yl mp n s.mem S.mem L1 b1 zq zcq mk)
    (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x388)) (h14 : S.regs 14 = BitVec.ofNat 64 g)
    (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0)
    (r0 : S.mem.readLE (sp + 0x390) 8 = yp) (r1 : S.mem.readLE (sp + 0x398) 8 = yl)
    (r3 : S.mem.readLE (sp + 0x3a8) 8 = mp) (r4 : S.mem.readLE (sp + 0x3b0) 8 = n)
    (r5 : S.mem.readLE (sp + 0x3b8) 8 = mc) :
    ExpW4.EPreA R b1 L1 (K - 8) g fs sp st zq zcq xp xl xc yp yl mp n mc S := by
  obtain ⟨⟨-, -, -, -, -, hK1, hK2, hce, hsv⟩, hgl, -, hty, hadx, -, -, -, -, -, -, -,
    hn, hn128, hnm, hmc, hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, -, hxO, hxa, hx48, hxN, hxl, hxlc, hxc, -, -,
    -, -, hgO, -, -, -, hsok, hstw, hstg, hstf, harr, hc0, -, hwbA, hstfr, -, -, hrnd, -⟩ := hP
  obtain ⟨hF, hLF, hrg, hx, -, -, hinv1, ⟨hzc40, hzL, hzA⟩, -, hnz, hzq⟩ := hZ
  have hce0 := hce
  obtain ⟨hal, hK0, hA0, hacc, -, -, -, -, hga, -, -, -, -, -, -, -, -, -, f6⟩ := hce0
  have hSs : (S.regs 4).toNat = sp + 0x388 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  -- the call environment
  have hws : ∀ r ∈ wN sp K, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr _
    simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have ce1 := CallW.CEnv.frame hce hF hrg hws
    (by unfold Apart at hga; simp only [wN, outside_cons, outside_nil, and_true]; omega)
    (by unfold Apart at f6; simp only [wN, outside_cons, outside_nil, and_true]; omega)
  have ce2 := cenv_ext (ExpOdd.cenv_rebase ce1 (x' := sp - 8) (K' := K - 8) (A' := 0x400) (by omega)
    (by omega) (by omega) (by omega)) hx
  -- the stack header
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF hF (by unfold Apart at hstw ⊢; omega)
  have ew : stW S.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S.mem st = stCap s.mem st := rdh 16 (by omega)
  have nrm : ∀ {p k c : Nat}, NE R L sp K st s.mem p (8 * c) → k ≤ c → NatNorm s.mem p k → NatNorm S.mem p k := by
    intro p k c hO hkc hN
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact Or.inl hk0
    rcases hN with h0 | h1
    · exact Or.inl h0
    · right
      rw [rd_held (held_sub hO.1 (by omega) (by omega)) hLF hF (by have := hO.2.1; unfold Apart at this ⊢; omega)]
      exact h1
  -- the globals
  have hgl' : RunIface.Globals R S.mem [(sp - 8 - (K - 8), sp + 0x3f8)] := by
    obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt', hgw', hwbacc, hwbrt, hwbw⟩ := hgl
    have hgA : Outside RunIface.gA 32 (R.rt ++ wN sp K) := by
      simp only [wN, outside_append, outside_cons, outside_nil, and_true] at hgw' ⊢
      exact ⟨hgrt', by omega, by omega⟩
    have hrd : ∀ k, k + 8 ≤ 32 → S.mem.readLE (RunIface.gA + k) 8 = s.mem.readLE (RunIface.gA + k) 8 :=
      fun k hk => hF.readLE _ _ (hgA.of_sub (by omega) (by omega))
    refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt', ?_,
      by rw [hF.accessible]; exact hwbacc, hwbrt, ?_⟩
    · rw [e8, hrd 8 (by omega), ← e8]; exact h40
    · rw [e16, hrd 16 (by omega), ← e16]; exact h12
    · rw [e24, hrd 24 (by omega), ← e24]; exact h80
    · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
      show S.mem.readLE RunIface.gA 8 = 40; rw [this]; exact h40'
    · simp only [outside_cons, outside_nil, and_true] at hgw' ⊢; omega
    · simp only [outside_cons, outside_nil, and_true] at hwbw ⊢; omega
  have hzc0 : 0 < zcq := by omega
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := hzA hzc0
  obtain ⟨zl8, zlH, zlacc, zl48⟩ := hzL hzc0
  refine ⟨⟨hSsp, h14, hfs, hx15, hdf, hal, by omega, by omega, ce2, hsv⟩, hgl', hty,
    by rw [hF.accessible]; exact hadx, hn, hn128, hnm, hmc,
    oe_at hmO hx (by omega) ew el ec, by rw [hF.accessible]; exact hma, hm48, nrm hmO (Nat.le_refl _) hmN,
    oe_at hyO hx (by omega) ew el ec, by rw [hF.accessible]; exact hya, hy48, nrm hyO (Nat.le_refl _) hyN,
    by omega, by omega,
    oe_at hxO hx (by omega) ew el ec, by rw [hF.accessible]; exact hxa, hx48, nrm hxO hxlc hxN, by omega, hxl, hxlc,
    hxc, hzq, hzc40, fun _ => ⟨⟨zlH, by unfold Apart at z1 ⊢; omega, z4, z5⟩, zlacc, zl48, zl8,
      by unfold Apart at z2 ⊢; omega, by unfold Apart at z3 ⊢; omega, z9, z8⟩,
    oe_at hgO hx (by omega) ew el ec, stkOK_hdr hsok hF ew el ec hx, by unfold Apart at hstw ⊢; omega,
    hstg, hstf, ?_, hwbA, ?_, by rw [el]; exact hrnd, r0, r1, r3, r4, r5, hinv1⟩
  · rw [ec, ew]; intro hc
    obtain ⟨a1, a2, a3⟩ := harr hc
    exact ⟨by unfold Apart at a1 ⊢; omega, a2, a3⟩
  · show Apart st 24 (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact hstfr

/-- `ExpOdd.PostD` (callee entry `S`, `K - 8`) as the `CPostG` `post_call` consumes -/
theorem cpostG_odd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K costD : Nat}
    {zp zc st xp xl yp yl mp n : Nat} {S s' : State}
    (h : ExpOdd.PostD R b L K costD zp zc st xp xl yp yl mp n S s') :
    s'.fsBase = S.fsBase ∧ s'.df = S.df ∧
    CPostG R b L (K + 0x390) 112 zp zc st (natVal S.mem xp xl ^ natVal S.mem yp yl % natVal S.mem mp n)
      (ExpOdd.OCost n xl yl costD (stLen S.mem st)) S s' := by
  obtain ⟨hfs, hdf, p, l, c, q0, q1, q2, hv, hN, hlc, hc, L', b', hx, hb, hinv, hlive, hof, hsb, hF, hLF, hRS⟩ := h
  exact ⟨hfs, hdf, p, l, c, q0, q1, q2, L', b', ⟨hv, hN, hlc, ⟨hc.2, by have := (hlive hc.1).2.2.2; omega⟩, hlive,
    Or.inr hof⟩, ⟨hx, hb, hinv⟩, hsb, hF, hLF, hRS⟩

theorem odd_sub : ∀ x, ExpOdd.names.contains x = true → LibN.names.contains x = true := by
  have h : ExpOdd.names.Sublist LibN.names := by decide +kernel
  intro x hx
  simp only [List.contains_iff_mem] at hx ⊢
  exact h.subset hx

theorem odd_nf : ExpOdd.names.contains fn = false := by decide +kernel

theorem m_gt1 {M : Memory} {mp n : Nat} (hn : 0 < n) (hN : NatNorm M mp n) (h1 : ¬(n = 1 ∧ M.readLE mp 8 = 1)) :
    1 < natVal M mp n := by
  by_cases hn1 : n = 1
  · subst hn1
    rcases hN with h | h
    · omega
    · simp only [natVal, Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h ⊢
      have : M.readLE mp 8 ≠ 1 := fun e => h1 ⟨rfl, e⟩
      omega
  · have := FvModexp.SubMod2N.natVal_lower M mp n hN hn
    have h2 : 2 ^ 64 ≤ 2 ^ (64 * (n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the odd-modulus path from `expNNOdd`'s entry to expNN's return -/
theorem oddPath (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (nsD : List String) (stkD : Nat) {costF : Nat → Nat → Nat → Nat} (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW4 : nsD.contains W4Loop.fn = false) (hnsW2 : nsD.contains W2Loop.fn = false)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K costD : Nat} (hKD : stkD + 0x80 ≤ K) {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow bp : Nat} {s S : State}
    {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hZ : ZM R b L g fs sp K zp zc st xp xl yp yl mp n s.mem S.mem L1 b1 zq zcq mk)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hm0 : s.mem.readLE mp 8 % 2 = 1) (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1))
    (hpc : S.rip = BitVec.ofNat 64 oddA) (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x388))
    (hA : DArgs S sp zq zcq st xp xl xc yp yl yc mp n mc) (h14 : S.regs 14 = s.regs 14)
    (hfsS : S.fsBase = s.fsBase) (hdfS : S.df = s.df) (hx15 : S.xmm 15 = 0)
    (hra : S.mem.readLE (sp + 0x388) 8 = oddR)
    (hbp : S.mem.readLE (sp + 0x490) 8 = bp) (hrv : S.mem.readLE (sp + 0x498) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq S.mem M0 (sp + 0x498))
    (hEk : EpiK impl ret0 F (sp + 0x498) bp (S.regs 14) M0
      (Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs4, hs14, hsfs, -, hsdf, hK1, hK2, hce, -⟩, -, -, -, -, -, -, -, -, -, -, -,
    hn, hn128, -, hmc, hmO, -, hm48, hmN, hyO, -, hy48, hyN, hyl, hyc, hxO, -, hx48, hxN, hxl, hxlc, hxc, -, -, -, -,
    -, -, hst0, hst48, hsok, hstw, -, -, harr, hc0, -, -, -, -, -, -, -, -, -, -, hob, -⟩ := hP'
  obtain ⟨hal, hK0, hA0, hacc, hg1, -, -, hwrt, -, -, hLs, -⟩ := hce
  have hZ' := hZ
  obtain ⟨hF0, hLF0, hrg, hx1, hb1, hmk', hinv1, hZQ, hZA, hnz, hzq⟩ := hZ'
  have hs : (s.regs 4).toNat = sp + 0x498 := by rw [hs4, BitVec.toNat_ofNat]; omega
  have hSs : (S.regs 4).toNat = sp + 0x388 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  have hg : (s.regs 14).toNat = g := by rw [hs14, BitVec.toNat_ofNat]; omega
  have hrw := rw_of hK0 hwrt
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF0 hF0 (by unfold Apart at hstw ⊢; omega)
  have ew : stW S.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S.mem st = stCap s.mem st := rdh 16 (by omega)
  have hrdx : natVal S.mem xp xl = natVal s.mem xp xl :=
    rd_held (held_sub hxO.1 (Nat.le_refl _) (by omega)) hLF0 hF0 (by have := hxO.2.1; unfold Apart at this ⊢; omega)
  have hrdy : natVal S.mem yp yl = natVal s.mem yp yl := rd_held hyO.1 hLF0 hF0 hyO.2.1
  have hrdm : natVal S.mem mp n = natVal s.mem mp n := rd_held hmO.1 hLF0 hF0 hmO.2.1
  have hzc40 := hZQ.1
  have hE := ExpOdd.ens impl hap R hclr hmv hmk hgr hwb nsD stkD costF hDiv hnsD hnsW4 hnsW2 b1 L1 (K - 8)
    (by omega) costD zq n zcq st xp xl xc yp yl mp n mc
  obtain ⟨a0, a3, a1, a7, a6, a8, a9, r0, r1, r2, r3, r4, r5⟩ := hA
  have hS14 : S.regs 14 = BitVec.ofNat 64 g := h14.trans hs14
  have hSfs : S.fsBase.toNat = fs := by rw [hfsS]; exact hsfs
  have hSg : (S.regs 14).toNat = g := by rw [h14]; exact hg
  refine callC impl hap odd_sub odd_nf ret0 hret F hs hK0 (by omega) hA0 hLs hrw hsok hstw hF0 hLF0 hx1
    hb1 hZA (by omega : K - 8 + 0x390 ≤ K + 0x388) h14 hfsS hdfS ?_ ?_ (Or.inr (Or.inr (Or.inl rfl)))
    (by simp [numIntRegs]) hE (by rw [hpc, show segAddr Extracted.program ExpOdd.fn = oddA by decide]) hSsp hra hx15 (hdfS.trans hsdf) ?_ ?_
    (fun s' h => cpostG_odd h)
    (by rw [ec, ew]; intro hc; exact (harr hc).1) (by rw [ec, ew]; exact hc0)
    (by rw [el, ec]; exact hsok.2.2.2.2.2.1)
    (by rw [hF0.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hbp hrv hsl hEk
  · rw [hrdx, hrdy, hrdm]
  · rw [el]; unfold NCost; omega
  · simp [ArgsFrom64, argReg, intArgRegs, a0, a3, a1, a7, a6, a8, a9]
  · unfold ExpOdd.PreD
    rw [hSs, hSg, hSfs, show sp + 0x388 - 0x388 = sp by omega, el, hrdm]
    refine ⟨opre_at hP hZ hSsp hS14 hSfs hx15 (hdfS.trans hsdf) hxl0 hyl0 r0 r1 r3 r4 r5, by omega, by omega,
      ?_, by rw [ec, ew]; exact hc0, by omega, by rw [val_mod2 hn]; exact hm0, m_gt1 hn hmN hm1,
      oBud_mono hob (by omega)⟩
    have := (hZQ.2.2 (by omega)).1
    unfold Apart at this ⊢; omega

end FvModexp.Amd64.ExpN
