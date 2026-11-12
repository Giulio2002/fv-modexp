import FvModexp.Proofs.Arm64.Exp.NNilKP
import FvModexp.Proofs.Arm64.Exp.NNilE

/-!
# `nat.expNN` (arm64), `stk == nil`: the flag-1 epilogue as an `EpiK` (`epiK1`)

The downstream chain (from the `rem` entry / `J5`, at the virtual entry `{s with mem := M1}`, see `NNilV.npreV`) ends in
an `EpiK`. For the `stk == nil` path it is `epiK1`: the result stores (`epi1s`), the flag test and the closure call
(`epi1c`), the deferred `stk.free()` = `nat.expNN.deferwrap1` (`FreeSh.sum` lifted to `LibN`: `dwSum`) and the return
(`epi1r`); the stack-given `Post` at the virtual entry becomes `PostNil` at the real entry (`NNilKP.postNil_of`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- `deferwrap1` (the `stk.free()` closure, `StkSh` pool shape) as a callee of `LibN` -/
theorem dwSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (b : Nat) (L rs : List (Nat × Nat)) :
    Summary (LibN.program.link impl) dwA (FreeSh.Pre R b L rs) (FreeSh.Post R b L rs) := by
  have hsub : ∀ x, LibFree.names.contains x = true → LibN.names.contains x = true := by
    intro x hx
    have : x = Free.fn := by simpa [LibFree.names, Free.fn] using hx
    subst this; decide
  have hc := codeIn_restrict_mono hap hsub
  rw [← LibFree.eq_only, ← LibN.eq_only] at hc
  have h := Janus.Contracts.EqHashModel.Summary.of_codeIn hc (FreeSh.sum impl R hput b L rs)
  rwa [show segAddr Extracted.program Free.fn = dwA by decide] at h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the flag-1 epilogue** (`stk == nil`): the `EpiK` the downstream chain needs, for the stack-given `Post` at the
virtual entry, ending in `PostNil` at the real entry `s` -/
theorem epiK1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (ret0 : Nat)
    (hret : RetAddr (LibN.program.link impl) ret0) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (F : State → Prop) {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow : Nat} {s : State}
    (hP : PreNil R b L K costF needR costR needS needP costS costP g sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow s)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M1 : Memory} (hN : NewStk R L L1 b b1 g M1 st)
    (hF : MemFrame s.mem M1 (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M1 L [])
    (h1182 : M1.readLE (sp + 1182) 1 = 1) (h1296 : M1.readLE (sp + 1296) 8 = sp + 1272)
    (h1272 : M1.readLE (sp + 1272) 8 = dwA) (h1280 : M1.readLE (sp + 1280) 8 = st)
    (f29 : Nat) (r18 r28 : BitVec 64) (hr28 : r28 = BitVec.ofNat 64 g)
    (hK' : ∀ s'' : State, s''.sp = BitVec.ofNat 64 (sp + 1312) → s''.regs 29 = BitVec.ofNat 64 f29 →
      s''.regs 18 = r18 → s''.regs 28 = r28 →
      PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s'' → F s'') :
    EpiK impl ret0 F sp f29 r18 r28 M1
      (Post R b1 L1 K costF costR costS costP zp zc st xp xl yp yl mp n { s with mem := M1 }) := by
  intro r S hr hpc hsp h18 h28 hacc h29v h30v hsl hPo
  obtain ⟨⟨hs1, hs28, hg1, hg2, hg3, hgo, hal, hK4, hKs, hsp2, hwacc, hwrt, hLs, -, hsv⟩, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, ⟨hgz, -⟩, -⟩ := id hP
  have hwout : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  have hhd := hN.hdr.1
  have hhw : Apart (sp - K) (K + 1432) st 24 := out_inR2 hwout hhd
  have hgo2 : Outside (g + 16) 8 R.rt := hgo.2
  have hgo1 : Apart (g + 16) 8 (sp - K) (K + 1432) := by
    have := hgo.1; unfold Apart; omega
  have esp : s.sp.toNat = sp + 1312 := by rw [hs1, BitVec.toNat_ofNat]; omega
  -- the result stores
  refine epi1s impl ret0 hret _ sp r hr hal (by omega) hsp2 S hpc hsp hacc ?_
  intro S1 p1 sp1 r0 r1 r2 e18 e28 e29 hF1 hrg1 w0 w1 w2
  obtain ⟨p, l, c, q0, q1, q2, hv, hnm, hlc, hc64, L2, b', hx, hb, hinv, hnl, hd, hsb, hMF, hLF2, hrs⟩ :=
    hPo S1 hF1 r0 r1 r2
  have hs1m : ∀ a k, Slot sp a k → S1.mem.readLE a k = M1.readLE a k := fun a k hs =>
    (hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; unfold Slot at hs; omega)).trans (hsl a k hs)
  have hacc1 : S1.mem.accessible (sp + 1048) 256 true = true := by rw [hF1.accessible]; exact hacc
  -- the flag test and the closure call
  refine epi1c impl ret0 hret _ sp r hr hal (by omega) hsp2 S1 p1 (sp1.trans hsp) hacc1
    ((hs1m (sp + 1182) 1 (Or.inl ⟨Nat.le_refl _, by omega⟩)).trans h1182)
    ((hs1m (sp + 1296) 8 (Or.inr (Or.inr ⟨Nat.le_refl _, by omega⟩))).trans h1296)
    ((hs1m (sp + 1272) 8 (Or.inr (Or.inl ⟨Nat.le_refl _, by omega⟩))).trans h1272) ?_
  intro S2 p2 sp2 r26 r30 f18 f28 f29' hF2 hrg2
  have hbo : ∀ a k, (a + k ≤ sp + 1183 ∨ sp + 1184 ≤ a) → S2.mem.readLE a k = S1.mem.readLE a k := fun a k h =>
    hF2.readLE a k (by simp only [outside_cons, outside_nil, and_true]; exact h)
  -- the stack header at S1 / S2
  have hok1 := hsb.1.1
  obtain ⟨hok2, ew2, el2, ec2⟩ := stkOK_frame hok1 hF2 (by have := hhw; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega)
  have hl1 : stLen S1.mem st = 0 := hsb.1.2.1.trans hN.2.2.2.2.2.2.1
  have hc01 : stCap S1.mem st = 0 → stW S1.mem st = 0 := hsb.2.cap0 hN.2.2.2.2.2.2.2.2.1
  have hmH : (st, st + 24) ∈ L1 := by rw [hN.1]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hmA : 0 < stCap M1 st → (stW M1 st, stW M1 st + 8 * stCap M1 st) ∈ L1 := fun hc => by
    rw [hN.1]; refine List.mem_append_right _ ?_
    simp only [stkRs, Nat.ne_of_gt hc, ↓reduceIte, List.mem_cons, true_or, or_true]
  have hdis1 : 0 < stCap S1.mem st → Apart st 24 (stW S1.mem st) (8 * stCap S1.mem st) := fun hc => by
    rcases hsb.1.2.2 with ⟨ew, ec⟩ | ⟨-, hap'⟩
    · rw [ew, ec]; exact hN.2.2.2.2.2.2.2.2.2.2.2.2.1
    · have := hap' _ hmH; simp only [Nat.add_sub_cancel_left] at this; exact this.symm
  have hrs1 : ∀ x ∈ stkRs S1.mem st, x ∈ L2 := stkRs_forall (hx.mem_old hmH) fun hc => by
    by_cases hk : stW S1.mem st = stW M1 st ∧ stCap S1.mem st = stCap M1 st
    · rw [hk.1, hk.2]; exact hx.mem_old (hmA (by rw [← hk.2]; exact hc))
    · exact hsb.2.mem hk
  have hrsE : stkRs S2.mem st = stkRs S1.mem st := stkRs_congr ew2 ec2
  -- the guard word and the window at S2
  have hgS : S2.mem.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 := by
    have g1 := hgo1; unfold Apart at g1
    rw [hbo (g + 16) 8 (by omega), hMF.readLE (g + 16) 8 ?_, hF.readLE (g + 16) 8 ?_]
    · simp only [outside_append]; exact ⟨hgo2, by simp only [wN, outside_cons, outside_nil, and_true]; omega⟩
    · simp only [outside_append]
      refine ⟨⟨⟨hgo2, ?_⟩, ?_⟩, hN.outWs hgo2⟩
      · simp only [winA, esp, outside_cons, outside_nil, and_true]; omega
      · simp only [outside_cons, outside_nil, and_true]; unfold Apart at hgz; omega
  have hacS : ∀ a k w, S2.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hF2.accessible, hMF.accessible, hF.accessible]
  have h1280' : S2.mem.readLE (sp + 1280) 8 = st := by
    rw [hbo (sp + 1280) 8 (by omega), hs1m (sp + 1280) 8 (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact h1280
  have hg28 : S2.regs 28 = BitVec.ofNat 64 g := f28.trans (e28.trans (h28.trans hr28))
  have e28s : ({ s with mem := M1 } : State).regs 28 = BitVec.ofNat 64 g := hs28
  have eg : (BitVec.ofNat 64 g).toNat = g := by rw [BitVec.toNat_ofNat]; omega
  rw [e28s, eg] at hinv
  have hinv2 : R.inv b' L2 g (view R.rt L2 S2.mem) := RtInv.inv_frame' hF2 (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; left
    exact hwout.of_sub (by simp only; omega) (by simp only; omega)) hinv
  have hLs2 : ∀ lo hi, sp - K ≤ lo → hi ≤ sp + 1432 → LiveSep L2 [(lo, hi)] := fun lo hi h1 h2 => by
    refine LiveSep.sub_win (lo := sp - K) (hi := sp + 1432) ?_ h1 h2
    refine liveSep_ext hx (hN.liveSep hLs fun q hq => ?_) fun q hq => ?_
    all_goals
      simp only [List.mem_singleton] at hq; subst hq; simp only
      rwa [show sp + 1432 - (sp - K) = K + 1432 by omega]
  have hpre := freePre (b' := b') (L2 := L2) hN hr (sp2.trans (sp1.trans hsp)) r26 r30 hg28 hg1
    (by rw [hacS]; exact hg2) (by rw [hgS]; exact hg3) hgo hal hK4 hKs hsp2 (by rw [hacS]; exact hwacc) hwrt hLs h1280'
    hok2 (by rw [el2]; exact hl1) (by rw [ec2, ew2]; exact hc01) (by rw [ec2, ew2]; exact hdis1)
    (by rw [hrsE]; exact hrs1) hx (hsv.2.2.2.2.2.2.2.2 [Free.poolA]) hinv2
  -- the closure call and the return
  refine epi1r impl ret0 hret F (dwSum impl hap R hput b' L2 (stkRs S2.mem st)) sp r hr hal (by omega) hsp2 S2 p2
    (sp2.trans (sp1.trans hsp)) r30 hpre ?_
  intro s3 hpost3 hrg3
  obtain ⟨⟨t1, t18, t28, t29⟩, hMF3, hLF3, hinv3⟩ := hpost3
  have hso : Free.stkOf S2 = st := by
    show S2.mem.readLE ((S2.regs 26).toNat + 8) 8 = st
    rw [r26, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show sp + 1272 + 8 = sp + 1280 by omega]; exact h1280'
  have esp2 : S2.sp.toNat = sp + 1056 := by rw [sp2, sp1, hsp, BitVec.toNat_ofNat]; omega
  rw [hso, esp2] at hMF3
  rw [hso] at hLF3
  rw [hg28, eg, hrsE] at hinv3
  have hrd3 : ∀ a, sp + 1048 ≤ a → a + 8 ≤ sp + 1304 → (a + 8 ≤ sp + 1183 ∨ sp + 1184 ≤ a) →
      s3.mem.readLE a 8 = S1.mem.readLE a 8 := by
    intro a h1 h2 h3
    have w1 := hhw; unfold Apart at w1
    rw [hMF3.readLE a 8 ?_, hbo a 8 h3]
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hwout.of_sub (by omega) (by omega), by omega, by omega⟩
  have hs1r : ∀ a, (a + 8 ≤ sp + 1232 ∨ sp + 1256 ≤ a) → S1.mem.readLE a 8 = S.mem.readLE a 8 := fun a h =>
    hF1.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; exact h)
  refine ⟨t1, by rw [hMF3.accessible, hF2.accessible]; exact hacc1, ?_, ?_⟩
  · rw [hrd3 (sp + 1056) (by omega) (by omega) (by omega), hs1r (sp + 1056) (by omega)]; exact h30v
  intro s4 hs4 h40 h41 h42 h429 h418 h428 hm4
  have hF4 : MemFrame S1.mem s3.mem (R.rt ++ wN sp K ++ [(st + 8, st + 16)]) := hF2.trans hMF3 fun a k ho => by
    simp only [wN, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨by omega, ⟨ho.1.1, by omega, ho.2⟩⟩
  have hLF4 : LiveFrame S1.mem s3.mem L2 [(st + 8, st + 16)] :=
    (LiveFrame.of_win hF2 (hLs2 _ _ (by omega) (by omega))).trans hLF3 fun _ _ h => h
  have v0 : s3.mem.readLE (sp + 1232) 8 = (S1.regs 0).toNat := by
    rw [hrd3 (sp + 1232) (by omega) (by omega) (by omega), r0]; exact w0
  have v1 : s3.mem.readLE (sp + 1240) 8 = (S1.regs 1).toNat := by
    rw [hrd3 (sp + 1240) (by omega) (by omega) (by omega), r1]; exact w1
  have v2 : s3.mem.readLE (sp + 1248) 8 = (S1.regs 2).toNat := by
    rw [hrd3 (sp + 1248) (by omega) (by omega) (by omega), r2]; exact w2
  have v29 : s3.mem.readLE (sp + 1048) 8 = f29 := by
    rw [hrd3 (sp + 1048) (by omega) (by omega) (by omega), hs1r (sp + 1048) (by omega)]; exact h29v
  rw [v0, Expmc.bv_ofNat_toNat, q0] at h40
  rw [v1, Expmc.bv_ofNat_toNat, q1] at h41
  rw [v2, Expmc.bv_ofNat_toNat, q2] at h42
  rw [v29] at h429
  exact hK' s4 hs4 h429 (h418.trans (t18.trans (f18.trans (e18.trans h18))))
    (h428.trans (t28.trans (f28.trans (e28.trans h28))))
    (postNil_of hP hN hF hLF hv hnm hlc hc64 hx hb hnl hd hsb hMF hLF2 hrs hF4 hLF4 hinv3 s4 hm4 h40 h41 h42)

end FvModexp.Arm64.ExpN
