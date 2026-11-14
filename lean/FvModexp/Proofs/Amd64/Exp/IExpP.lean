import FvModexp.Proofs.Amd64.Exp.NNilD
import FvModexp.Proofs.Amd64.Exp.NOddP
import FvModexp.Proofs.Amd64.Top.RunIface
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# `(*Int).exp` (amd64; agent expmc s77, twin of the arm64 IExpP): `nat.expNN`'s precondition at the call (pure)

`preNF_of`: from `RunIface.ExpSpec`'s precondition at the entry state `s` (`t = RSP`; operands `z = x`, `y`, `m`), the
two extra entry facts of `ExpSpecA` (`hasADX` readable, the `natOne` word apart from the threshold globals `gA`) and a
state `S3` at `nat.expNN`'s entry (`RSP = t - 0x138`, memory changed only in segments A-C's frame
`[t - 0x138, t) ∪ [t + 8, t + 0x30)`, the stack arguments `y`, `m` at `t - 0x130 …`), `ExpN.PreNF` with `x = z`
(`stk = nil`, `slow = false`). `expNN`'s window `[t - 0x5d0 - K, t - 0xc0)` lies in `ExpSpec`'s window when
`K + 0x5d0 ≤ stk`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts FvModexp

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Amd64.IExp

open FvModexp.Amd64.RunIface (IntOK IntPre IntV IntLenLe OneG Globals maxW PoolG ModX)

/-- the threshold globals and the write-barrier flag survive a frame they are outside of (copy of asm's
`Q.NatRem.globals_win`, Amd64/NatQ/RemDvPre.lean, to keep the rem chain out of this module) -/
theorem globals_winI {R : RtInv} {m m' : Janus.Arm64.Memory} {w w' ws : List (Nat × Nat)} (h : Globals R m w)
    (hF : MemFrame m m' ws) (hg : Outside RunIface.gA 32 ws) (hw : ∀ a n, Outside a n w → Outside a n w') :
    Globals R m' w' := by
  obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := h
  have hrd : ∀ k, k + 8 ≤ 32 → m'.readLE (RunIface.gA + k) 8 = m.readLE (RunIface.gA + k) 8 := fun k hk =>
    hF.readLE _ _ (hg.of_sub (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt, hw _ _ hgw,
    by rw [hF.accessible]; exact hwbacc, hwbrt, hw _ _ hwbw⟩
  · rw [e8, hrd 8 (by omega), ← e8]; exact h40
  · rw [e16, hrd 16 (by omega), ← e16]; exact h12
  · rw [e24, hrd 24 (by omega), ← e24]; exact h80
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
    show m'.readLE RunIface.gA 8 = 40; rw [this]; exact h40'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- a callee's `CEnv` (window `[sp - K, sp + A)` inside the caller's) at a state whose memory differs from the
caller's entry memory only inside the caller's window -/
theorem cenv_in {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk above sp K A : Nat} {M : Janus.Arm64.Memory}
    (hce : CallEnv R L s stk above) (hF : MemFrame s.mem M (win s stk above)) (hrg : M.regions = s.mem.regions)
    (h1 : (s.regs 4).toNat - stk ≤ sp - K) (hKs : K ≤ sp) (h2 : sp + A ≤ (s.regs 4).toNat + above)
    (h3 : sp ≤ (s.regs 4).toNat) (hal : sp % 8 = 0) (hst : K + ((s.regs 4).toNat - sp) ≤ stk) :
    CallW.CEnv R L (s.regs 14).toNat s.fsBase.toNat sp K A M := by
  obtain ⟨⟨hgw, hgr, hgb⟩, ⟨hb', ha, hw⟩, -, hd, hout, hga, hgrt, hLs, hro, ⟨⟨hfb, hfr, hfg⟩, hfrt, hfw⟩⟩ := hce
  simp only [stackguard0, regG, stackguard0Offset, regSP] at hgw hgr hgb hb' ha hw hfg
  simp only [win] at hF hLs
  generalize (s.regs 4).toNat = t at *
  generalize (s.regs 14).toNat = g at *
  have hac : ∀ a k w, M.accessible a k w = s.mem.accessible a k w := hF.accessible
  unfold Apart at hga hfw
  refine ⟨hal, hKs, by omega, by rw [hac]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega),
    by omega, by rw [hac]; exact hgr, ?_, hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgrt, ?_,
    FvModexp.dataLoaded_frame64 hd hrg hro (hF.mono fun a k h => by rw [outside_append] at h; exact h.2)
      (fun r hr _ => by
        simp only [List.mem_singleton] at hr; subst hr; simp only
        exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)), hro,
    hfb.1, hfb.2, by rw [hac]; exact hfr, ?_, hfrt, by unfold Apart; omega⟩
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; omega
  · intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hfg

/-- an operand array (pointer `p`, length `l`, capacity `c` of a held `*Int`, outside the window `[lo, hi)`) at a memory
`M` that differs from `m` only inside `[lo, hi)`: `PreNil`'s facts for its length and its capacity, and its value -/
theorem opnd_pre {R : RtInv} {L : List (Nat × Nat)} {m M : Janus.Arm64.Memory} {p l c lo hi sp K : Nat}
    (hlive : NatLive m R L p c) (hlc : l ≤ c) (hnorm : NatNorm m p l)
    (hout : 0 < c → Outside p (8 * c) [(lo, hi)]) (h1 : lo ≤ sp - K) (h2 : sp + 0x510 ≤ hi) (hKs : K ≤ sp)
    (hF : MemFrame m M [(lo, hi)]) :
    (0 < c → ExpN.NE0 R L sp K p (8 * c) ∧ M.accessible p (8 * c) false = true ∧ p + 8 * c ≤ 2 ^ 48) ∧
      NatNorm M p l ∧ natVal M p l = natVal m p l := by
  have hrd : 0 < c → ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M.readLE a k = m.readLE a k := fun hc a k e1 e2 => by
    have ho := hout hc
    simp only [outside_cons, outside_nil, and_true] at ho
    exact hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨fun hc => ?_, ?_, ?_⟩
  · obtain ⟨-, hH, hacc, h48⟩ := hlive hc
    have ho := hout hc
    simp only [outside_cons, outside_nil, and_true] at ho
    exact ⟨⟨hH, by unfold Apart; omega⟩, by rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_weaken _ hacc, h48⟩
  · rcases Nat.eq_zero_or_pos l with hl0 | hl0
    · exact Or.inl hl0
    rcases hnorm with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hrd (by omega) _ _ (by omega) (by omega)]; exact h)
  · rcases Nat.eq_zero_or_pos l with hl0 | hl0
    · subst hl0; rfl
    · exact hrd (by omega) _ _ (Nat.le_refl _) (by omega)

/-- `NE0` for a sub-range -/
theorem ne0_sub {R : RtInv} {L : List (Nat × Nat)} {sp K p k k' : Nat} (h : ExpN.NE0 R L sp K p k) (hk : k' ≤ k) :
    ExpN.NE0 R L sp K p k' :=
  ⟨Held.sub h.1 (Nat.le_refl _) (by omega), by have := h.2; unfold Apart at this ⊢; omega⟩

/-- an opaque wrapper: hides a fact from `omega`'s case splits -/
structure BoxI (P : Prop) : Prop where
  unbox : P

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNN`'s precondition** at `(*Int).exp`'s call (`x = z`, `stk = nil`, `slow = false`) -/
theorem preNF_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above K : Nat}
    {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {s : State} {zA yA mA : Nat}
    (hpre : IntPre R b B L stk above [zA, yA, mA] s) (hm0 : 0 < IntV s.mem mA)
    (hlz : IntLenLe s.mem zA maxW) (hly : IntLenLe s.mem yA maxW) (hlm : IntLenLe s.mem mA maxW)
    (hone : OneG R L s.mem (win s stk above) [zA, yA, mA]) (hpool : PoolG R s.mem (win s stk above))
    (hzX : ModX s.mem zA) (hadx : s.mem.accessible MontHyp.hasADX 1 false = true)
    (hoG : Apart (s.mem.readLE EvenHyp.natOneA 8) 8 RunIface.gA 32)
    (hK : K + 0x5d0 ≤ stk) (hK4 : 41640 ≤ K) (hK20 : K + 0x98 ≤ 2 ^ 20) (hab : 0x30 ≤ above)
    {zp zl zc yp yl yc mp n mc : Nat}
    (ez8 : s.mem.readLE (zA + 8) 8 = zp) (ez16 : s.mem.readLE (zA + 16) 8 = zl)
    (ez24 : s.mem.readLE (zA + 24) 8 = zc)
    (ey8 : s.mem.readLE (yA + 8) 8 = yp) (ey16 : s.mem.readLE (yA + 16) 8 = yl)
    (ey24 : s.mem.readLE (yA + 24) 8 = yc)
    (em8 : s.mem.readLE (mA + 8) 8 = mp) (em16 : s.mem.readLE (mA + 16) 8 = n)
    (em24 : s.mem.readLE (mA + 24) 8 = mc)
    (hnR : needR zl n ≤ 2 ^ 16) (hnS : needS zl yl n ≤ 2 ^ 16)
    (hnP : needP zl yl (Nat.log2 (natVal s.mem mp n)) ≤ 2 ^ 16)
    (hbud : 24 + (makeCost 1 + max (costR 0 zl n) (makeCost n + max (costS 0 zl yl n)
      (costP 0 zl yl (Nat.log2 (natVal s.mem mp n))))) ≤ B)
    (hob : ExpOdd.OBud costF n costD zl yl 0 (B - 24 - makeCost n))
    {S3 : State} (hsp : S3.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x138)) (h14 : S3.regs 14 = s.regs 14)
    (hfs : S3.fsBase = s.fsBase) (hx3 : S3.xmm 15 = 0) (hdf3 : S3.df = false)
    (hF : MemFrame s.mem S3.mem [((s.regs 4).toNat - 0x138, (s.regs 4).toNat),
      ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x30)]) (hrg : S3.mem.regions = s.mem.regions)
    (a1 : S3.mem.readLE ((s.regs 4).toNat - 0x130) 8 = yp) (a2 : S3.mem.readLE ((s.regs 4).toNat - 0x128) 8 = yl)
    (a3 : S3.mem.readLE ((s.regs 4).toNat - 0x120) 8 = yc) (a4 : S3.mem.readLE ((s.regs 4).toNat - 0x118) 8 = mp)
    (a5 : S3.mem.readLE ((s.regs 4).toNat - 0x110) 8 = n) (a6 : S3.mem.readLE ((s.regs 4).toNat - 0x108) 8 = mc) :
    ExpN.PreNF R b L K costF costD needR costR needS needP costS costP zp zl zc 0 zp zl zc yp yl yc mp n mc 0 S3 := by
  have hce := hpre.1
  obtain ⟨⟨-, ⟨hstk, hab48, -⟩, hal, -, hrt, -, -, hLs, hro, -⟩, hsv, hG, hBb, hinv, hops, -⟩ := hpre
  obtain ⟨op, ⟨hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11⟩, hoA⟩ := hone
  obtain ⟨h0rt, hpl, hplR, hplW⟩ := hpool
  unfold ModX at hzX
  have hnB := BoxI.mk (And.intro hn1 (And.intro hn2 (And.intro hn3 hn4)))
  have hpB := BoxI.mk hpl
  clear hn1 hn2 hn3 hn4 hpl
  have hoz := hops zA (by simp)
  have hoy := hops yA (by simp)
  have hom := hops mA (by simp)
  have hAz := hoA zA (by simp)
  clear hops hoA
  simp only [regSP] at hstk hab48 hal
  have hFw : MemFrame s.mem S3.mem (win s stk above) := hF.mono fun a k h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hcev := BoxI.mk (cenv_in (sp := (s.regs 4).toNat - 0x5d0) (K := K) (A := 0x510) hce hFw hrg
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  clear hce hFw
  simp only [win] at hn7 hn11 hplW hoz hoy hom hLs hG
  generalize ht : (s.regs 4).toNat = t at *
  generalize hg : (s.regs 14).toNat = g at *
  obtain ⟨⟨-, -, hz48, hzacc, -, hzL, hzlc, hzN, -, hzc40⟩, -, hzO, -, hzG, -, hzT⟩ := hoz
  obtain ⟨⟨-, -, -, -, -, hyL, hylc, hyN, -, -⟩, -, hyO, -, -, -, -⟩ := hoy
  obtain ⟨⟨-, -, -, -, -, hmL, hmlc, hmN, -, hmc40⟩, -, hmO, -, -, -, -⟩ := hom
  simp only [IntLenLe, maxW, ez8, ez16, ez24] at hzL hzlc hzN hzO hzG hzT hAz hlz hzc40 hzX
  simp only [IntLenLe, maxW, ey8, ey16, ey24] at hyL hylc hyN hyO hly
  simp only [RunIface.IntV, IntLenLe, maxW, em8, em16, em24] at hmL hmlc hmN hmO hlm hmc40 hm0
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd hm0 (by rw [natVal_zero]; omega)
    · exact h
  have hzp : zp < 2 ^ 64 := ez8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyc : yc < 2 ^ 64 := ey24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  clear ez8 ez16 ez24 ey8 ey16 ey24 em8 em16 em24
  have hst : stk ≤ t := hstk
  have hrd : ∀ a k, (a + k ≤ t - stk ∨ t + above ≤ a) → S3.mem.readLE a k = s.mem.readLE a k := fun a k h =>
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hac : ∀ a k w, S3.mem.accessible a k w = s.mem.accessible a k w := fun a k w => hF.accessible a k w
  have e1 : (S3.regs 4).toNat - 0x498 = t - 0x5d0 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have e2 : (S3.regs 14).toNat = g := by rw [h14]; exact hg
  have e3 : S3.fsBase.toNat = s.fsBase.toNat := by rw [hfs]
  have hF1 : MemFrame s.mem S3.mem [(t - stk, t + above)] := hF.mono fun a k h => by
    simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hmP := BoxI.mk <| opnd_pre (sp := t - 0x5d0) (K := K) hmL hmlc hmN hmO (by omega) (by omega) (by omega) hF1
  have hyP := BoxI.mk <| opnd_pre (sp := t - 0x5d0) (K := K) hyL hylc hyN hyO (by omega) (by omega) (by omega) hF1
  have hzP := BoxI.mk <| opnd_pre (sp := t - 0x5d0) (K := K) hzL hzlc hzN hzO (by omega) (by omega) (by omega) hF1
  have hXF : NHyp.XFacts R L zp zl zc :=
    ⟨⟨hzlc, hzc40, fun h => ⟨(hzL h).2.1, (hzL h).2.2.2⟩⟩, fun h => by
      have := hzX (by omega); unfold Apart at this ⊢; omega⟩
  have hoG3 : Apart (S3.mem.readLE EvenHyp.natOneA 8) 8 RunIface.gA 32 := by
    have := hn7; simp only [outside_cons, outside_nil, and_true] at this
    have eO : EvenHyp.natOneA = RunIface.natOneA := rfl
    rw [hrd _ _ (by rw [eO]; omega)]; exact hoG
  unfold ExpN.PreNF ExpN.PreNil
  rw [e1, e2, e3]
  have r1 : t - 0x5d0 + 0x4a0 = t - 0x130 := by omega
  have r2 : t - 0x5d0 + 0x4a8 = t - 0x128 := by omega
  have r3 : t - 0x5d0 + 0x4b0 = t - 0x120 := by omega
  have r4 : t - 0x5d0 + 0x4b8 = t - 0x118 := by omega
  have r5 : t - 0x5d0 + 0x4c0 = t - 0x110 := by omega
  have r6 : t - 0x5d0 + 0x4c8 = t - 0x108 := by omega
  rw [r1, r2, r3, r4, r5, r6, hmP.unbox.2.2]
  refine ⟨⟨⟨hsp.trans (by congr 1; omega), h14.trans (by rw [← hg, Expmc.bv_ofNat_toNat]), e3, hx3, hdf3, hK4, hK20,
      hcev.unbox, hsv⟩, ?_, ?_, RoOut.out' hro 1 (by decide) (by decide), RoOut.out' hro 1 (by decide) (by decide),
    by rw [hac]; exact hadx, rfl, a1, a2, a3, a4, a5, a6, hn0, by omega, hmlc, hmc40,
    ne0_sub (hmP.unbox.1 (by omega)).1 (by omega),
    Janus.Arm64.Memory.accessible_mono _ (hmP.unbox.1 (by omega)).2.1 (Nat.le_refl _) (by omega),
    by have := (hmP.unbox.1 (by omega)).2.2; omega, hmP.unbox.2.1,
    fun h => ne0_sub (hyP.unbox.1 (by omega)).1 (by omega),
    fun h => Janus.Arm64.Memory.accessible_mono _ (hyP.unbox.1 (by omega)).2.1 (Nat.le_refl _) (by omega), fun h => by have := (hyP.unbox.1 (by omega)).2.2; omega,
    hyP.unbox.2.1, by omega, hyc,
    fun h => (hzP.unbox.1 (by omega)).1, fun h => (hzP.unbox.1 (by omega)).2.1,
    fun h => (hzP.unbox.1 (by omega)).2.2, hzP.unbox.2.1, by omega, hzlc, hzc40,
    hzp, ⟨hzlc, rfl, rfl, rfl⟩, hzc40, fun h => Or.inl ⟨h, rfl⟩, fun h => ?_, ?_, fun h => ?_, rfl, ?_,
    by omega, hnR, hnS, hnP, by omega,
    FvModexp.Amd64.ExpN.oBud_mono hob (by omega), ?_, hoG3⟩, hXF⟩
  · -- globals
    have hgw := hG.2.2.2.2.2.2.2.2.2.1
    simp only [outside_cons, outside_nil, and_true] at hgw
    exact globals_winI hG hF (by simp only [outside_cons, outside_nil, and_true]; omega) fun a k h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  · -- the pool's `New` word
    simp only [outside_cons, outside_nil, and_true] at hplW
    refine ⟨h0rt, ?_, hplR, by simp only [outside_cons, outside_nil, and_true]; omega⟩
    rw [hrd _ _ (by omega)]; exact hpB.unbox
  · -- z's array vs the guard and TLS words
    have h1 := hzG h; have h2 := hzT h
    unfold Apart at h1 h2 ⊢; omega
  · -- `gA`
    obtain ⟨-, -, -, -, -, -, -, -, hgrt', hgw, -, -, -⟩ := id hG
    simp only [outside_cons, outside_nil, and_true] at hgw
    exact ⟨Or.inr hgrt', by unfold Apart; omega⟩
  · -- `natOne`
    obtain ⟨a5, a6⟩ := hAz.2.2 h
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hnB.unbox
    have eO : EvenHyp.natOneA = RunIface.natOneA := rfl
    have h7 := hn7; simp only [outside_cons, outside_nil, and_true] at h7
    have h11 := hn11; simp only [outside_cons, outside_nil, and_true] at h11
    unfold Apart at a5 a6
    refine ⟨op, ?_, ?_, ?_, ?_, by rw [eO, hac]; exact hn5, by rw [eO]; exact hn6, ?_, by rw [hac]; exact hn8, hn9,
      hn10, ?_⟩
    · rw [eO, hrd RunIface.natOneA 8 (by omega)]; exact hn1
    · rw [eO, hrd (RunIface.natOneA + 8) 8 (by omega)]; exact hn2
    · rw [eO, hrd (RunIface.natOneA + 16) 8 (by omega)]; exact hn3
    · rw [hrd op 8 (by omega)]; exact hn4
    · rw [eO]; simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]; omega
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hwb, -, -⟩ := id hG
    rw [hac]; exact hwb
  · exact Expmc.inv_frame hF (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inr (hrt.of_sub (by omega) (by simp only; omega))
      · exact Or.inr (hrt.of_sub (by simp only; omega) (by simp only; omega))) hinv

end FvModexp.Amd64.IExp
