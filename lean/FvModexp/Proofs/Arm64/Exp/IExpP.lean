import FvModexp.Proofs.Arm64.Exp.NFunNE
import FvModexp.Proofs.Arm64.Top.RunIface

/-!
# `(*Int).exp` (arm64): `nat.expNN`'s precondition at the call (pure)

`preNF_of`: from `RunIface.ExpSpec`'s precondition at the entry state `s` (`t = SP`; operands `z = x`, `y`, `m`) and a
state `S3` at `nat.expNN`'s entry (`SP = t - 320`, memory changed only in `(*Int).exp`'s frame `[t - 328, t + 48)`),
`ExpN.PreNF` with `x = z` (`stk = nil`, `slow = false`). `expNN`'s window `[t - 1632 - K, t - 200)` lies in `ExpSpec`'s
window when `K + 1632 ≤ stk`.

`PoolG` / `ExpX`: the facts top's FINAL `ExpSpec` adds (NOTES-conventions "[top s19] ANSWER": `PoolG`, `IntOK`'s cap
bound) plus `m ≠ nil` (the code's `m != nil` test, int.go:589) and `z`'s header apart from the write-barrier flag
(segment D stores into it, then reads the flag), stated locally until `RunIface` has them.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts FvModexp

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Arm64.IExp

open FvModexp.Arm64.RunIface (IntOK IntPre IntV IntLenLe OneG Globals maxW)

/-- `stackPool`'s `New` word (top's `RunIface.PoolG`, s19 text verbatim; `Free.poolA = RunIface.stackPoolA`) -/
def PoolG (R : RtInv) (m : Memory) (w : List (Nat × Nat)) : Prop :=
  Outside 0 1 R.rt ∧ m.readLE (Free.poolA + newOffset) 8 = 0 ∧ Outside (Free.poolA + newOffset) 8 R.rt ∧
    Outside (Free.poolA + newOffset) 8 w

/-- the extra precondition facts of `(*Int).exp` beyond today's `RunIface.ExpSpec` (local; see the module doc) -/
def ExpX (R : RtInv) (m : Memory) (w : List (Nat × Nat)) (z y mm : Nat) : Prop :=
  PoolG R m w ∧ m.readLE (z + 24) 8 < 2 ^ 40 ∧ m.readLE (y + 24) 8 < 2 ^ 40 ∧ m.readLE (mm + 24) 8 < 2 ^ 40 ∧
    mm ≠ 0 ∧ Apart z 32 RunIface.wbA 4 ∧ RunIface.ModX m z

/-- the threshold globals and the write-barrier flag survive a frame that keeps them (adapted from divmc's
`NatSqr.globals_frame`, Arm64/Nat/SqrKPre.lean) -/
theorem globals_frameI {R : RtInv} {m m' : Memory} {w w' ws : List (Nat × Nat)} (h : Globals R m w)
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

/-- an operand array (pointer `p`, length `l`, capacity `c` of a held `*Int`, outside the window `[lo, hi)`) at a memory
`M` that differs from `m` only inside `[lo, hi)`: `PreNil`'s facts for it (guarded by `0 < l`) and its value -/
theorem opnd_pre {R : RtInv} {L : List (Nat × Nat)} {m M : Memory} {p l c lo hi sp K : Nat}
    (hlive : NatLive m R L p c) (hlc : l ≤ c) (hnorm : NatNorm m p l)
    (hout : 0 < c → Outside p (8 * c) [(lo, hi)]) (h1 : lo ≤ sp - K) (h2 : sp + 1432 ≤ hi) (hKs : K ≤ sp)
    (hF : MemFrame m M [(lo, hi)]) :
    (0 < l → ExpN.NE0 R L sp K p (8 * l)) ∧ (0 < l → M.accessible p (8 * l) false = true) ∧
      (0 < l → p + 8 * l ≤ 2 ^ 48) ∧ NatNorm M p l ∧ natVal M p l = natVal m p l := by
  rcases Nat.eq_zero_or_pos l with hl0 | hl0
  · subst hl0
    exact ⟨fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0),
      fun h => absurd h (Nat.lt_irrefl 0), Or.inl rfl, rfl⟩
  have hc : 0 < c := by omega
  obtain ⟨-, hH, hacc, h48⟩ := hlive hc
  have ho := hout hc
  simp only [outside_cons, outside_nil, and_true] at ho
  have hrd : ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M.readLE a k = m.readLE a k := fun a k e1 e2 =>
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨fun _ => ⟨hH.sub (Nat.le_refl _) (by omega), by unfold Apart; omega⟩,
    fun _ => by rw [hF.accessible]; exact Memory.accessible_sub _ hacc (Or.inr rfl) (Nat.le_refl _) (by omega),
    fun _ => by omega, ?_, hrd _ _ (Nat.le_refl _) (by omega)⟩
  rcases hnorm with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [hrd _ _ (by omega) (by omega)]; exact h)

/-- an opaque wrapper: hides a fact from `omega`'s case splits -/
structure BoxI (P : Prop) : Prop where
  unbox : P

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNN`'s precondition** at `(*Int).exp`'s call (`x = z`, `stk = nil`, `slow = false`) -/
theorem preNF_of {R : RtInv} {b B : Nat} {L : List (Nat × Nat)} {stk above K : Nat}
    {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {s : State} {zA yA mA : Nat}
    (hpre : IntPre R b B L stk above [zA, yA, mA] s) (hm0 : 0 < IntV s.mem mA)
    (hlz : IntLenLe s.mem zA maxW) (hly : IntLenLe s.mem yA maxW) (hlm : IntLenLe s.mem mA maxW)
    (hone : OneG R L s.mem (win s stk above) [zA, yA, mA]) (hx : ExpX R s.mem (win s stk above) zA yA mA)
    (hK : K + 1632 ≤ stk) (hK4 : 4304 ≤ K) (hK20 : K + 288 ≤ 2 ^ 20) (hab : 48 ≤ above)
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
      (max (costP 0 zl yl (Nat.log2 (natVal s.mem mp n))) (ExpOdd.OBud costF n zl yl 0)))) ≤ B)
    {S3 : State} (hsp : S3.sp = BitVec.ofNat 64 (s.sp.toNat - 320)) (h28 : S3.regs 28 = s.regs 28)
    (hF : MemFrame s.mem S3.mem [(s.sp.toNat - 328, s.sp.toNat + 48)]) (hrg : S3.mem.regions = s.mem.regions) :
    ExpN.PreNF R b L K costF needR costR needS needP costS costP zp zl zc 0 zp zl zc yp yl yc mp n mc 0 S3 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hstk, hab48, hacc⟩, hd, hrt, hgap, hgrt, hLs, hro⟩, hsv, hG, hBb, hinv, hops, hpw⟩ :=
    hpre
  obtain ⟨op, ⟨hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11⟩, hoA⟩ := hone
  obtain ⟨⟨h0rt, hpool, hpoolR, hpoolW⟩, hzc40, hyc40, hmc40, hmA0, -, hzX⟩ := hx
  unfold RunIface.ModX at hzX
  have hnB := BoxI.mk (And.intro hn1 (And.intro hn2 (And.intro hn3 hn4)))
  have hpB := BoxI.mk hpool
  generalize hgw0 : s.mem.readLE ((s.regs 28).toNat + 16) 8 = gw at hg3
  have hgw := BoxI.mk hgw0
  clear hgw0
  clear hn1 hn2 hn3 hn4 hpool
  have hoz := hops zA (by simp)
  have hoy := hops yA (by simp)
  have hom := hops mA (by simp)
  have hAz := hoA zA (by simp)
  clear hops hoA hpw
  simp only [win] at hn7 hn11 hpoolW hoz hoy hom hLs hG
  generalize ht : s.sp.toNat = t at *
  generalize hg : (s.regs 28).toNat = g at *
  obtain ⟨⟨-, -, hz48, hzacc, -, hzL, hzlc, hzN, -⟩, -, hzO, -, hzG⟩ := hoz
  obtain ⟨⟨-, -, -, -, -, hyL, hylc, hyN, -⟩, -, hyO, -, -⟩ := hoy
  obtain ⟨⟨-, -, -, -, -, hmL, hmlc, hmN, -⟩, -, hmO, -, -⟩ := hom
  simp only [IntLenLe, maxW, ez8, ez16, ez24] at hzL hzlc hzN hzO hzG hAz hlz hzc40 hzX
  simp only [IntLenLe, maxW, ey8, ey16, ey24] at hyL hylc hyN hyO hly hyc40
  simp only [RunIface.IntV, IntLenLe, maxW, em8, em16, em24] at hmL hmlc hmN hmO hlm hmc40 hm0
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd hm0 (by rw [natVal_zero]; omega)
    · exact h
  have hzp : zp < 2 ^ 64 := ez8 ▸ Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := ez24 ▸ Memory.readLE_lt _ _ _
  have hyp : yp < 2 ^ 64 := ey8 ▸ Memory.readLE_lt _ _ _
  have hyc : yc < 2 ^ 64 := ey24 ▸ Memory.readLE_lt _ _ _
  clear ez8 ez16 ez24 ey8 ey16 ey24 em8 em16 em24
  -- frames
  have hst : stk ≤ t := hstk
  have hw1 : t - stk ≤ t - 1632 - K := by omega
  have hw2 : t - 1632 + 1432 ≤ t + above := by omega
  have hFw : ∀ a k, (a + k ≤ t - stk ∨ t + above ≤ a) → s.mem.readLE a k = s.mem.readLE a k := fun _ _ _ => rfl
  have hrd : ∀ a k, (a + k ≤ t - stk ∨ t + above ≤ a) → S3.mem.readLE a k = s.mem.readLE a k := fun a k h =>
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hac : ∀ a k w, S3.mem.accessible a k w = s.mem.accessible a k w := fun a k w => hF.accessible a k w
  have e1 : S3.sp.toNat - 1312 = t - 1632 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have e2 : (S3.regs 28).toNat = g := by rw [h28]; exact hg
  have hF' : MemFrame s.mem S3.mem [(t - 1632 - K - 4096, t + above)] :=
    hF.mono fun a k h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  have hmP := BoxI.mk <| opnd_pre (sp := t - 1632) (K := K) hmL hmlc hmN (fun h => by
    have := hmO h; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega) (by omega) (by omega) (by omega)
    (hF.mono (rs' := [(t - stk, t + above)]) fun a k h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have hyP := BoxI.mk <| opnd_pre (sp := t - 1632) (K := K) hyL hylc hyN (fun h => by
    have := hyO h; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega) (by omega) (by omega) (by omega)
    (hF.mono (rs' := [(t - stk, t + above)]) fun a k h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  have hzP := BoxI.mk <| opnd_pre (sp := t - 1632) (K := K) hzL hzlc hzN (fun h => by
    have := hzO h; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega) (by omega) (by omega) (by omega)
    (hF.mono (rs' := [(t - stk, t + above)]) fun a k h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  clear hF' hFw
  have hwout : Outside (t - 1632 - K) (K + 1432) R.rt := hrt.of_sub (by omega) (by omega)
  -- `x = z`'s operand facts (`XFacts`: `IntOK`, `NatLive`, `ModX`)
  have hXF : NHyp.XFacts R L zp zl zc :=
    ⟨⟨hzlc, hzc40, fun h => ⟨(hzL h).2.1, (hzL h).2.2.2⟩⟩, fun h => by
      have := hzX (by omega); unfold Apart at this ⊢; omega⟩
  unfold ExpN.PreNF
  rw [e1, e2]
  refine ⟨?_, hXF⟩
  refine ⟨⟨hsp.trans (by congr 1; omega), h28.trans (by rw [← hg, Expmc.bv_ofNat_toNat]), hg1, by rw [hac]; exact hg2,
    ?_, ?_, by omega, hK4, by omega, by omega,
    by rw [hac]; exact Memory.accessible_mono _ hacc (by omega) (by omega), ?_, ?_, ?_, hsv⟩,
    hK20, ?_, ⟨hro, h0rt⟩, RoOut.out' hro 1 (by decide) (by decide), rfl, hn0, by omega, hmlc, hmc40,
    hmP.unbox.1 hn0, hmP.unbox.2.1 hn0, hmP.unbox.2.2.1 hn0, hmP.unbox.2.2.2.1,
    hyP.unbox.1, hyP.unbox.2.1, hyP.unbox.2.2.1, hyP.unbox.2.2.2.1, by omega, ⟨hyc, hyp⟩,
    hzP.unbox.1, hzP.unbox.2.1, hzP.unbox.2.2.1, hzP.unbox.2.2.2.1, by omega, hzp, hzc,
    hzp, ⟨hzlc, rfl, rfl, rfl⟩, hzc40, ⟨fun h => (hzG h).symm, fun h => ?_⟩, fun h => Or.inl ⟨h, rfl⟩, ?_,
    fun h => ?_, rfl, ?_, ?_, hnR, hnS, ?_, ?_, ?_, ?_, ?_⟩
  · -- the guard word
    rw [hrd _ _ (by unfold Apart at hgap; omega), hgw.unbox]; omega
  · simp only [outside_cons]; exact ⟨by unfold Apart at hgap; omega, hgrt⟩
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only; rw [show t - 1632 + 1432 - (t - 1632 - K) = K + 1432 by omega]; exact hwout
  · intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  · exact dataLoaded_frame hd hrg hro (hF.mono fun a k h => by
      rw [outside_append] at h; exact h.2) (fun r hr _ => by
        simp only [List.mem_singleton] at hr; subst hr; simp only
        exact Memory.accessible_mono _ hacc (by omega) (by omega))
  · -- globals
    obtain ⟨-, -, -, -, -, -, -, -, -, hgw, -, -, -⟩ := id hG
    simp only [outside_cons, outside_nil, and_true] at hgw
    exact globals_frameI hG hF (by simp only [outside_cons, outside_nil, and_true]; omega) fun a k h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
  · -- z's array
    obtain ⟨-, hH, -, -⟩ := hzL h
    have := hzO h; simp only [outside_cons, outside_nil, and_true] at this
    exact ⟨hH, by unfold Apart; omega⟩
  · -- `gA`
    obtain ⟨-, -, -, -, -, -, -, -, hgrt', hgw, -, -, -⟩ := id hG
    simp only [outside_cons, outside_nil, and_true] at hgw
    exact ⟨Or.inr hgrt', by unfold Apart; omega⟩
  · -- `natOne`
    obtain ⟨a1, a2, a3⟩ := hAz
    obtain ⟨a5, a6⟩ := a3 h
    have hrdO : ∀ a k, (a + k ≤ t - stk ∨ t + above ≤ a) → S3.mem.readLE a k = s.mem.readLE a k := hrd
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hnB.unbox
    have eO : EvenHyp.natOneA = RunIface.natOneA := rfl
    have h7 := hn7; simp only [outside_cons, outside_nil, and_true] at h7
    have h11 := hn11; simp only [outside_cons, outside_nil, and_true] at h11
    unfold Apart at a5 a6
    refine ⟨op, ?_, ?_, ?_, ?_, by rw [eO, hac]; exact hn5, by rw [eO]; exact hn6, ?_, by rw [hac]; exact hn8, hn9,
      hn10, ?_⟩
    · rw [eO, hrdO RunIface.natOneA 8 (by omega)]; exact hn1
    · rw [eO, hrdO (RunIface.natOneA + 8) 8 (by omega)]; exact hn2
    · rw [eO, hrdO (RunIface.natOneA + 16) 8 (by omega)]; exact hn3
    · rw [hrdO op 8 (by omega)]; exact hn4
    · rw [eO]; simp only [outside_cons, outside_nil, and_true]; omega
    · simp only [outside_cons, outside_nil, and_true]; omega
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hwb, -, -⟩ := id hG
    rw [hac]; exact hwb
  · simp only [StackNat.rnd]; omega
  · rw [hmP.unbox.2.2.2.2]; exact hnP
  · rw [hmP.unbox.2.2.2.2]; omega
  · have := hpoolW; simp only [outside_cons, outside_nil, and_true] at this
    rw [hrd _ _ (by omega)]; exact hpB.unbox
  · have := hpoolW; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  · exact Expmc.inv_frame hF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      exact Or.inr (hrt.of_sub (by omega) (by omega))) hinv

end FvModexp.Arm64.IExp
