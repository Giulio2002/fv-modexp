import FvModexp.Proofs.Amd64.Exp.NNilKP
import FvModexp.Proofs.Amd64.Exp.NNilE

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: the flag-1 epilogue as an `EpiK` (`epiK1`) (agent expmc s75; twin of
`Arm64.ExpN.epiK1`)

The downstream chain (from the `rem` entry / `J4`, at the virtual entry `{s with mem := M1}`, see `NNilV.npreV`) ends in
an `EpiK`. For the `stk == nil` path it is `epiK1`: result stores, flag test and closure call (`epi1a`), the deferred
`stk.free()` = `nat.expNN.deferwrap1` (`Free.sumS` lifted to `LibN`: `dwSum`) and the return (`epi1b`); the stack-given
`Post` at the virtual entry (instantiated at the state `s1` = the return-point state with the result stores) becomes
`PostNil` at the real entry (`NNilKP.postNil_of`). The accessibility of the closure call's return slot `t - 0x110`
comes from the `Post`'s frame (`EpiK` itself only grants `[t - 0x108, t + 8)`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.ExpN

/-- `deferwrap1` (the `stk.free()` closure, `StkSh` pool shape) as a callee of `LibN` -/
theorem dwSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (b : Nat) (L rs : List (Nat × Nat)) :
    Summary (LibN.program.link impl) dwA (Free.PreS R b L rs) (Free.Post R b L rs) := by
  have hc : CodeIn64 (LibFree.program.link impl) (LibN.program.link impl) := by
    rw [LibFree.eq_only, LibN.eq_only]
    exact A64.codeIn_restrict_mono64 hap (Callees.sub_of_all (by decide))
  have h := Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc (Free.sumS impl R hput b L rs)
  rwa [dwA_eq] at h

theorem dwRet_lt {r : Nat} (hr : RetPt r) : dwRet r < 2 ^ 47 := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the flag-1 epilogue** (`stk == nil`): the `EpiK` the downstream chain needs, for the stack-given `Post` at the
virtual entry, ending in `PostNil` at the real entry `s` -/
theorem epiK1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (ret0 : Nat)
    (hret : RetAddr (LibN.program.link impl) ret0) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (F : State → Prop) {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st0 xp xl xc yp yl yc mp n mc slow : Nat} {s : State}
    (hP : PreNil R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st0 xp xl xc yp yl yc mp n
      mc slow s) (hx0 : xl ≠ 0)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M1 : Janus.Arm64.Memory} (hN : NewStk R L L1 b b1 g M1 st)
    (hF : MemFrame s.mem M1 (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem M1 L [])
    (hfl : M1.readLE (sp + 0x3fe) 1 = 1) (hrc : M1.readLE (sp + 0x488) 8 = sp + 0x468)
    (hdw : M1.readLE (sp + 0x468) 8 = dwA) (hst : M1.readLE (sp + 0x470) 8 = st)
    (bp : Nat) (r14 : BitVec 64) (hr14 : r14 = BitVec.ofNat 64 g)
    (hK' : ∀ s'' : State, s''.regs 4 = BitVec.ofNat 64 (sp + 0x498 + 8) → s''.regs 5 = BitVec.ofNat 64 bp →
      s''.regs 14 = r14 → s''.xmm 15 = 0 →
      PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s'' → F s'') :
    EpiK impl ret0 F (sp + 0x498) bp r14 M1
      (Post R b1 L1 K costD costR costS costP zp zc st xp xl yp yl mp n { s with mem := M1 }) := by
  intro r S hr hpc hsp h14 hx15 hacc hbp hra hsl hPo
  obtain ⟨⟨hs4, hs14, -, -, -, hK1, -, hce, hsv⟩, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hxlc, -, -, ⟨hzlc, -, hxlz, -⟩, -, -, hgz0, -⟩ := id hP
  have hgz := (hgz0 (by omega)).1
  obtain ⟨hal, hKs, hsp2, hwacc, hg1, hg2, hg3, hwout, hgo1, hgo2, hLs, -⟩ := hce
  have hhd := hN.hdr.1
  have hhw : Apart (sp - K) (K + 0x510) st 24 := out_inR2 hwout hhd
  have esp : (s.regs 4).toNat = sp + 0x498 := by rw [hs4, BitVec.toNat_ofNat]; omega
  have eg : (BitVec.ofNat 64 g).toNat = g := by rw [BitVec.toNat_ofNat]; omega
  have hra' : dwRet r < 2 ^ 47 := dwRet_lt hr
  -- the `Post` at `S` itself: `S.mem`'s accessibility is the entry's
  have hP0 := hPo S (MemFrame.refl _ _) rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMF0, -⟩ := hP0
  have hacS : ∀ a k w, S.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hMF0.accessible, hF.accessible]
  have hacc' : S.mem.accessible (sp + 0x498 - 0x110) 0x118 true = true := by
    rw [hacS]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
  have hSs : ∀ a k, Slot (sp + 0x498) a k → S.mem.readLE a k = M1.readLE a k := hsl
  refine epi1a impl ret0 hret _ (sp + 0x498) r S.mem hr (by omega) (by omega) hacc'
    ((hSs _ _ (Or.inl ⟨by omega, by omega⟩)).trans (by rw [show sp + 0x498 - 0x9a = sp + 0x3fe by omega]; exact hfl))
    ((hSs _ _ (Or.inr (Or.inr ⟨by omega, by omega⟩))).trans (by
      rw [show sp + 0x498 - 0x10 = sp + 0x488 by omega, show sp + 0x498 - 0x30 = sp + 0x468 by omega]; exact hrc))
    ((hSs _ _ (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans (by
      rw [show sp + 0x498 - 0x30 = sp + 0x468 by omega]; exact hdw)) S hpc hsp rfl ?_
  intro S2 p2 sp2 r2 r5 f14 fx15 ffs fdf hF2 hrg2 hra2 w0 w1 w2 _
  simp only [show sp + 0x498 - 0x110 = sp + 0x388 by omega, show sp + 0x498 - 0x108 = sp + 0x390 by omega,
    show sp + 0x498 - 0x99 = sp + 0x3ff by omega, show sp + 0x498 - 0x98 = sp + 0x400 by omega,
    show sp + 0x498 - 0x58 = sp + 0x440 by omega, show sp + 0x498 - 0x40 = sp + 0x458 by omega,
    show sp + 0x498 - 0x50 = sp + 0x448 by omega, show sp + 0x498 - 0x48 = sp + 0x450 by omega,
    show sp + 0x498 - 0x30 = sp + 0x468 by omega] at sp2 r2 hF2 hra2 w0 w1 w2
  -- the state with the result stores, where the `Post` is taken
  generalize hw : ((S.mem.writeLE (sp + 0x440) 8 (S.regs 0).toNat).writeLE (sp + 0x448) 8 (S.regs 3).toNat).writeLE
    (sp + 0x450) 8 (S.regs 1).toNat = W
  have hFw : MemFrame S.mem W [(sp + 0x440, sp + 0x458)] := by rw [← hw]; janus_frame
  have hrgw : W.regions = S.mem.regions := by rw [← hw]; simp only [Janus.Arm64.Memory.regions_writeLE]
  have hP1 := hPo { S with mem := W } (by
    rw [show sp + 0x498 - 0x58 = sp + 0x440 by omega, show sp + 0x498 - 0x40 = sp + 0x458 by omega]; exact hFw)
    hrgw rfl rfl rfl rfl rfl rfl
  obtain ⟨hfs1, hdf1, p, l, c, q0, q1, q2, hv, hnm, hlc, hc64, L2, b', hx, hb, hinv, hnl, hd, hsb, hMF, hLF2, hrs⟩ :=
    hP1
  -- `W → S2.mem`: only `[sp + 0x388, sp + 0x458)` differs
  have hw2 : MemFrame W S2.mem [(sp + 0x388, sp + 0x458)] := by
    refine ⟨fun a k ho => ?_, fun a k wr => by rw [hF2.accessible, hFw.accessible]⟩
    simp only [outside_cons, outside_nil, and_true] at ho
    rw [hF2.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hFw.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have hrdS : ∀ a k, (a + k ≤ sp + 0x388 ∨ sp + 0x390 ≤ a) → (a + k ≤ sp + 0x3ff ∨ sp + 0x400 ≤ a) →
      (a + k ≤ sp + 0x440 ∨ sp + 0x458 ≤ a) → S2.mem.readLE a k = S.mem.readLE a k := fun a k h1 h2 h3 =>
    hF2.readLE a k (by simp only [outside_cons, outside_nil, and_true]; exact ⟨h1, h2, h3⟩)
  -- the stack header at `S2`
  have hok1 := hsb.1.1
  obtain ⟨hok2, ew2, el2, ec2⟩ := DivNil.stkOK_frame hok1 hw2 (by
    have := hhw; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega)
  have hl1 : stLen W st = 0 := hsb.1.2.1.trans hN.2.2.2.2.2.2.1
  have hc01 : stCap W st = 0 → stW W st = 0 := hsb.2.cap0 hN.2.2.2.2.2.2.2.2.1
  have hmH : (st, st + 24) ∈ L1 := by rw [hN.1]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hmA : 0 < stCap M1 st → (stW M1 st, stW M1 st + 8 * stCap M1 st) ∈ L1 := fun hc => by
    rw [hN.1]; refine List.mem_append_right _ ?_
    simp only [stkRs, Nat.ne_of_gt hc, ↓reduceIte, List.mem_cons, true_or, or_true]
  have hdis1 : 0 < stCap W st → Apart st 24 (stW W st) (8 * stCap W st) := fun hc => by
    rcases hsb.1.2.2 with ⟨ew, ec⟩ | ⟨-, hap'⟩
    · rw [ew, ec]; exact hN.2.2.2.2.2.2.2.2.2.2.2.2.1
    · have := hap' _ hmH; simp only [Nat.add_sub_cancel_left] at this; exact this.symm
  have hrs1 : ∀ x ∈ stkRs W st, x ∈ L2 := stkRs_forall (hx.mem_old hmH) fun hc => by
    by_cases hk : stW W st = stW M1 st ∧ stCap W st = stCap M1 st
    · rw [hk.1, hk.2]; exact hx.mem_old (hmA (by rw [← hk.2]; exact hc))
    · exact hsb.2.mem hk
  have hrsE : stkRs S2.mem st = stkRs W st := stkRs_congr ew2 ec2
  -- the guard word and the window at `S2`
  have hgS : S2.mem.readLE (g + 16) 8 = s.mem.readLE (g + 16) 8 := by
    have g1 := hgo1; unfold Apart at g1
    rw [hrdS (g + 16) 8 (by omega) (by omega) (by omega), hMF0.readLE (g + 16) 8 ?_, hF.readLE (g + 16) 8 ?_]
    · simp only [outside_append]; exact ⟨hgo2, by simp only [wN, outside_cons, outside_nil, and_true]; omega⟩
    · simp only [outside_append]
      refine ⟨⟨⟨hgo2, ?_⟩, ?_⟩, hN.outWs hgo2⟩
      · simp only [win, esp, outside_cons, outside_nil, and_true]; omega
      · simp only [outside_cons, outside_nil, and_true]; unfold Apart at hgz; omega
  have hacS2 : ∀ a k w, S2.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hF2.accessible, hacS]
  have h24 : S2.mem.readLE (sp + 0x470) 8 = st := by
    rw [hrdS (sp + 0x470) 8 (by omega) (by omega) (by omega), hSs _ _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hst
  have hg14 : (S2.regs 14).toNat = g := by rw [f14, h14, hr14, eg]
  have e14s : (({ s with mem := M1 } : State).regs 14).toNat = g := by
    show (s.regs 14).toNat = g; rw [hs14, eg]
  rw [e14s] at hinv
  have hLs2 : ∀ lo hi, sp - K ≤ lo → hi ≤ sp + 0x510 → LiveSep L2 [(lo, hi)] := fun lo hi h1 h2 => by
    refine LiveSep.sub_win (lo := sp - K) (hi := sp + 0x510) ?_ h1 h2
    refine liveSep_ext hx (hN.liveSep hLs fun q hq => ?_) fun q hq => ?_
    all_goals
      simp only [List.mem_singleton] at hq; subst hq; simp only
      rwa [show sp + 0x510 - (sp - K) = K + 0x510 by omega]
  have hwin2 : Outside (sp + 0x388) (0x458 - 0x388) R.rt := hwout.of_sub (by omega) (by omega)
  have hinv2 : R.inv b' L2 g (view R.rt L2 S2.mem) := RtInv.inv_frame' hw2 (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; left
    exact hwin2.of_sub (by simp only; omega) (by simp only; omega)) hinv
  have hsp2' : (S2.regs 4).toNat = sp + 0x388 := by rw [sp2, BitVec.toNat_ofNat]; omega
  have hpre := freePreE (b' := b') (L2 := L2) hN hsp2' (by rw [r2, BitVec.toNat_ofNat]; omega)
    (by rw [hra2]; exact hra') hg14 hg1 (by rw [hacS2]; exact hg2) (by rw [hgS]; exact hg3) hgo1 hgo2 hal
    (by omega) hKs hsp2 (by rw [hacS2]; exact hwacc) hwout hLs h24
    hok2 (by rw [el2]; exact hl1) (by rw [ec2, ew2]; exact hc01) (by rw [ec2, ew2]; exact hdis1)
    (by rw [hrsE]; exact hrs1) hx (hsv.2.2.2.2.2.2.2.2 [Free.poolA]) hinv2
  -- the closure call and the return
  refine epi1b impl ret0 hret (dwSum impl hap R hput b' L2 (stkRs S2.mem st)) F (sp + 0x498) r hr (by omega)
    (by omega) S2 p2 (by rw [sp2, show sp + 0x498 - 0x110 = sp + 0x388 by omega]) (by rw [show sp + 0x498 - 0x110 = sp + 0x388 by omega]; exact hra2)
    hpre ?_
  intro s3 hpost3 hrg3
  obtain ⟨⟨t4, t5, t14, tx15, tfs, tdf⟩, hMF3, hLF3, hinv3⟩ := hpost3
  have hso : Free.stkOf S2 = st := by
    show S2.mem.readLE ((S2.regs 2).toNat + 8) 8 = st
    rw [r2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show sp + 0x468 + 8 = sp + 0x470 by omega]; exact h24
  rw [hso, hsp2'] at hMF3
  rw [hso] at hLF3
  rw [hg14, hrsE] at hinv3
  have hrd3 : ∀ a k, sp + 0x388 ≤ a → a + k ≤ sp + 0x510 → s3.mem.readLE a k = S2.mem.readLE a k := by
    intro a k h1 h2
    have w1 := hhw; unfold Apart at w1
    rw [hMF3.readLE a k ?_]
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hwout.of_sub (by omega) (by omega), by omega, by omega⟩
  have hacc3 : s3.mem.accessible (sp + 0x498 - 0x108) 0x110 true = true := by
    rw [show sp + 0x498 - 0x108 = sp + 0x390 by omega, hMF3.accessible, hacS2]
    exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
  refine ⟨t4, hacc3, ?_, ?_⟩
  · rw [hrd3 _ 8 (by omega) (by omega), hrdS _ 8 (by omega) (by omega) (by omega)]; exact hra
  intro s4 hs4 h40 h43 h41 h45 h414 h4x h4fs h4df hm4
  have hF4 : MemFrame W s3.mem (R.rt ++ wN sp K ++ [(st + 8, st + 16)]) := hw2.trans hMF3 fun a k ho => by
    simp only [wN, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨by omega, ⟨ho.1.1, by omega, ho.2⟩⟩
  have hLF4 : LiveFrame W s3.mem L2 [(st + 8, st + 16)] :=
    (LiveFrame.of_win hw2 (hLs2 _ _ (by omega) (by omega))).trans hLF3 fun _ _ h => h
  have v0 : s3.mem.readLE (sp + 0x498 - 0x58) 8 = (S.regs 0).toNat := by
    rw [show sp + 0x498 - 0x58 = sp + 0x440 by omega, hrd3 _ 8 (by omega) (by omega)]; exact w0
  have v3 : s3.mem.readLE (sp + 0x498 - 0x50) 8 = (S.regs 3).toNat := by
    rw [show sp + 0x498 - 0x50 = sp + 0x448 by omega, hrd3 _ 8 (by omega) (by omega)]; exact w1
  have v1 : s3.mem.readLE (sp + 0x498 - 0x48) 8 = (S.regs 1).toNat := by
    rw [show sp + 0x498 - 0x48 = sp + 0x450 by omega, hrd3 _ 8 (by omega) (by omega)]; exact w2
  have v5 : s3.mem.readLE (sp + 0x498 - 8) 8 = bp := by
    rw [hrd3 _ 8 (by omega) (by omega), hrdS _ 8 (by omega) (by omega) (by omega)]; exact hbp
  rw [v0, Expmc.bv_ofNat_toNat] at h40
  rw [v3, Expmc.bv_ofNat_toNat] at h43
  rw [v1, Expmc.bv_ofNat_toNat] at h41
  rw [v5] at h45
  have e0 : S.regs 0 = BitVec.ofNat 64 p := q0
  have e3 : S.regs 3 = BitVec.ofNat 64 l := q1
  have e1 : S.regs 1 = BitVec.ofNat 64 c := q2
  have hfs4 : s4.fsBase = s.fsBase := h4fs.trans (tfs.trans (ffs.trans hfs1))
  have hdf4 : s4.df = s.df := h4df.trans (tdf.trans (fdf.trans hdf1))
  exact hK' s4 hs4 h45 (h414.trans (t14.trans (f14.trans h14))) (h4x.trans (tx15.trans (fx15.trans hx15)))
    (postNil_of hP hx0 hN hF hLF hv hnm hlc hc64 hx hb hnl hd hsb hMF hLF2 hrs hF4 hLF4 hinv3 s4 hm4 hfs4 hdf4
      (h40.trans e0) (h43.trans e3) (h41.trans e1))

end FvModexp.Amd64.ExpN
