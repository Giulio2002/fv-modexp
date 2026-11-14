import FvModexp.Proofs.Amd64.Exp.NNilC
import FvModexp.Proofs.Amd64.Exp.NNilTE
import FvModexp.Proofs.Amd64.Exp.NLift

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: the join's continuations (`nilJ`) (agent expmc s75)

`nilJ`: from the memory `M` before the join (the new stack `st` with `NewStk` at `M`, the spills `NilSp`), the two
continuations `NilJK` (the `rem` entry | `J4`) are `contR` / `contD` at the virtual entry `M'` (the join's writes: the
defer record, the flag bytes, `rem`'s pushed arguments — all inside the window).
* `chainW` / `chainR`: frames `R.rt ++ wN` + `LiveFrame … []` compose with a window frame / a runtime frame.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.ExpN

theorem chainW {R : RtInv} {L : List (Nat × Nat)} {sp K : Nat} {A B C : Janus.Arm64.Memory} {ws : List (Nat × Nat)}
    (h1 : MemFrame A B (R.rt ++ wN sp K) ∧ LiveFrame A B L []) (h2 : MemFrame B C ws)
    (hLs : LiveSep L [(sp - K, sp + 0x510)]) (hws : ∀ r ∈ ws, sp - K ≤ r.1 ∧ r.2 ≤ sp + 0x510)
    (hsub : ∀ a k, Outside a k (wN sp K) → Outside a k ws) :
    MemFrame A C (R.rt ++ wN sp K) ∧ LiveFrame A C L [] := by
  refine ⟨h1.1.trans h2 fun a k ho => ⟨ho, hsub a k (by rw [outside_append] at ho; exact ho.2)⟩,
    h1.2.trans (LiveFrame.of_win h2 fun r hr => DivNil.outside_of_forall fun q hq => ?_) fun _ _ h => h⟩
  have h1 := hLs r hr; have h2 := hws q hq
  simp only [outside_cons, outside_nil, and_true] at h1; omega

theorem chainR {R : RtInv} {L : List (Nat × Nat)} {sp K : Nat} {A B C : Janus.Arm64.Memory} {ws : List (Nat × Nat)}
    (h1 : MemFrame A B (R.rt ++ wN sp K) ∧ LiveFrame A B L []) (h2 : MemFrame B C (R.rt ++ ws))
    (h2l : LiveFrame B C L []) (hsub : ∀ a k, Outside a k (wN sp K) → Outside a k ws) :
    MemFrame A C (R.rt ++ wN sp K) ∧ LiveFrame A C L [] :=
  ⟨h1.1.trans h2 fun a k ho => ⟨ho, by rw [outside_append] at ho ⊢; exact ⟨ho.1, hsub a k ho.2⟩⟩,
    h1.2.trans h2l fun _ _ h => h⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the join's continuations** at the memory `M` before the join -/
theorem nilJ (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true) (hnfR : nsR.contains fn = false)
    (hKR : stkR ≤ K + 0x388)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow bp zp' zl' zc' : Nat}
    {s : State}
    (hP : PreNil R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st0 xp xl xc yp yl yc mp n
      mc slow s) (hX : NHyp.XFacts R L xp xl xc)
    (hz : ZKeep0 R L g fs sp K zp zl zc xp xc yp yl mp n zp' zl' zc' s.mem) (hna : NHyp.NoAlias zp' zc' xp xc)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hm1 : ¬(n = 1 ∧ s.mem.readLE mp 8 = 1)) (hEv : EvH impl R K needS costS xl yl n)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M : Janus.Arm64.Memory} (hN : NewStk R L L1 b b1 g M st)
    (hF : MemFrame s.mem M (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M L []) (hrg : M.regions = s.mem.regions)
    (hA : ∀ a k, sp + 0x4a0 ≤ a → a + k ≤ sp + 0x4d0 → M.readLE a k = s.mem.readLE a k)
    (hsp : NilSp M (sp + 0x498) zp' zl' zc' yc xp xl xc 0 n yp mp yl mc)
    (hbp : M.readLE (sp + 0x490) 8 = bp) (hrv : M.readLE (sp + 0x498) 8 = ret0)
    (S0 : State) (h04 : S0.regs 4 = BitVec.ofNat 64 (sp + 0x390)) (h014 : S0.regs 14 = s.regs 14)
    (h0fs : S0.fsBase = s.fsBase) (h0df : S0.df = s.df) (h0x : S0.xmm 15 = 0)
    (hK' : ∀ s'' : State, s''.regs 4 = BitVec.ofNat 64 (sp + 0x498 + 8) → s''.regs 5 = BitVec.ofNat 64 bp →
      s''.regs 14 = s.regs 14 → s''.xmm 15 = 0 →
      PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s'' → F s'') :
    NilJK impl ret0 (IsReturn F) (sp + 0x498) st S0 M zp' zl' zc' yc xp xl xc 0 n yp mp yl mc := by
  have hce := hP.1.2.2.2.2.2.2.2.1
  obtain ⟨hal, hKs, hsp2, hwacc, -, -, -, hwout, -, -, hLs, -⟩ := hce
  have hyO : NE0 R L sp K yp (8 * yl) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
  have ey := rd0_v hyO (by omega) hLF hF
  obtain ⟨-, -, -, q18, q58, q60, q68, q70, -, -, -, -, -⟩ := hsp
  -- the join's frame lies in the window (outside `R.rt`)
  have hjoin : ∀ {ws : List (Nat × Nat)} {M' : Janus.Arm64.Memory}, MemFrame M M' ws →
      (∀ r ∈ ws, sp - K ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ sp + 0x498) → M'.regions = M.regions →
      (MemFrame s.mem M' (R.rt ++ wN sp K) ∧ LiveFrame s.mem M' L []) ∧ M'.regions = s.mem.regions ∧
        NewStk R L L1 b b1 g M' st ∧
        ∀ a k, (sp + 0x498 ≤ a ∨ a + k ≤ sp - K) → M'.readLE a k = M.readLE a k := by
    intro ws M' hFM hws hrgM
    have hws' : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
      have := hws r hr; exact hwout.of_sub (by omega) (by omega)
    refine ⟨chainW ⟨hF, hLF⟩ hFM hLs (fun r hr => by have := hws r hr; omega) fun a k ho => ?_,
      by rw [hrgM, hrg], NewStk.frameE hN hFM hws', fun a k h => hFM.readLE a k (DivNil.outside_of_forall fun q hq => by
        have := hws q hq; omega)⟩
    refine DivNil.outside_of_forall fun q hq => ?_
    have := hws q hq; simp only [wN, outside_cons, outside_nil, and_true] at ho; omega
  constructor
  · intro hy1 hyv S' M' p0 p4 a0 a3 a1 a7 a6 a8 a9 a5 a14 afs adf ax am hFM hrgM r110 r108 r100 rf8 r9a _ r30 r28 r10
    obtain ⟨⟨hF', hLF'⟩, hrg', hN', hk⟩ := hjoin hFM (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega) hrgM
    refine liftNE impl hap (contR impl hap R hput hRem hnsR hnfR ret0 (retAddr_down hret) F hP hX hKR hN' hF' hLF'
      hrg' (fun a k h1 h2 => (hk a k (Or.inl (by omega))).trans (hA a k h1 h2))
      (by rw [show sp + 0x3fe = sp + 0x498 - 0x9a by omega]; exact r9a)
      (by rw [show sp + 0x488 = sp + 0x498 - 0x10 by omega, show sp + 0x468 = sp + 0x498 - 0x30 by omega]; exact r10)
      (by rw [show sp + 0x468 = sp + 0x498 - 0x30 by omega]; exact r30)
      (by rw [show sp + 0x470 = sp + 0x498 - 0x28 by omega]; exact r28)
      hz hna ⟨hy1, by rw [← ey]; exact hyv⟩ hxl0 S' p0 (p4.trans (congrArg _ (by omega))) a0 a3 a1 a7 a6 a8 a9
      (a14.trans h014) (afs.trans h0fs) (adf.trans h0df) (ax.trans h0x) am
      (by rw [show sp + 0x388 = sp + 0x498 - 0x110 by omega]; exact r110)
      (by rw [show sp + 0x390 = sp + 0x498 - 0x108 by omega]; exact r108)
      (by rw [show sp + 0x398 = sp + 0x498 - 0x100 by omega]; exact r100)
      (by rw [show sp + 0x3a0 = sp + 0x498 - 0xf8 by omega]; exact rf8)
      (by rw [hFM.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hbp) (by rw [hk _ _ (Or.inl (by omega))]; exact hrv)
      fun s'' e4 e5 e14 ex hq => hK' s'' e4 e5 (e14.trans (a14.trans h014)) ex hq)
  · intro hny S' M' p0 p4 a0 a3 a1 a7 a6 a8 a9 a10 a11 a12 a13 a15 a2 a5 a14 afs adf ax am hFM hrgM r9a _ r30 r28 r10
    obtain ⟨⟨hF', hLF'⟩, hrg', hN', hk⟩ := hjoin hFM (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega) hrgM
    have hspl : SpillsB M' sp xp xl xc yp yl yc mp n mc := by
      have rA : ∀ {a k v : Nat}, sp + 0x4a0 ≤ a → a + k ≤ sp + 0x4d0 → s.mem.readLE a k = v → M'.readLE a k = v :=
        @fun a k v h1 h2 hv => by rw [hk a k (Or.inl (by omega)), hA a k h1 h2]; exact hv
      obtain ⟨-, -, -, -, -, -, -, r1, r2, r3, r4, r5, r6, -⟩ := hP
      refine ⟨rA (by omega) (by omega) r1, rA (by omega) (by omega) r2, rA (by omega) (by omega) r3,
        rA (by omega) (by omega) r4, rA (by omega) (by omega) r5, rA (by omega) (by omega) r6, ?_, ?_, ?_, ?_⟩
      · rw [hk _ _ (Or.inl (by omega)), show sp + 0x4f0 = sp + 0x498 + 0x58 by omega]; exact q58
      · rw [hk _ _ (Or.inl (by omega)), show sp + 0x4f8 = sp + 0x498 + 0x60 by omega]; exact q60
      · rw [hk _ _ (Or.inl (by omega)), show sp + 0x500 = sp + 0x498 + 0x68 by omega]; exact q68
      · rw [hk _ _ (Or.inl (by omega)), show sp + 0x508 = sp + 0x498 + 0x70 by omega]; exact q70
    exact contD impl hap R hput H ret0 hret F hP hX hN' hF' hLF' hrg'
      (fun a k h1 h2 => (hk a k (Or.inl (by omega))).trans (hA a k h1 h2))
      (by rw [show sp + 0x3fe = sp + 0x498 - 0x9a by omega]; exact r9a)
      (by rw [show sp + 0x488 = sp + 0x498 - 0x10 by omega, show sp + 0x468 = sp + 0x498 - 0x30 by omega]; exact r10)
      (by rw [show sp + 0x468 = sp + 0x498 - 0x30 by omega]; exact r30)
      (by rw [show sp + 0x470 = sp + 0x498 - 0x28 by omega]; exact r28)
      hz hxl0 hyl0 (by rw [← ey]; exact hny) hm1 hEv S' p0 (p4.trans h04) a0 a1 a2 a7 a6 a8 a9 a10 a11 a12 a13 a15
      (a14.trans h014) (afs.trans h0fs) (adf.trans h0df) (ax.trans h0x) am hspl
      (by rw [hFM.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hbp) (by rw [hk _ _ (Or.inl (by omega))]; exact hrv)
      fun s'' e4 e5 e14 ex hq => hK' s'' e4 e5 (e14.trans (a14.trans h014)) ex hq

end FvModexp.Amd64.ExpN
