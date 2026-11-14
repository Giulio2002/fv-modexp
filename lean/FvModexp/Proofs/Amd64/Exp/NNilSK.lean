import FvModexp.Proofs.Amd64.Exp.NNilS
import FvModexp.Proofs.Amd64.Exp.NGetE

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: from `J2` (`TESTQ DI` with `stk == nil`) to the return (agent expmc s75; twin of
`Arm64.ExpN.k2NilE`)

`nilK2`: `J2` (`0x5e713c`, `RSP = t - 0x108`, memory `M` = the `J1` memory) → spills and `Pool.Get` (`stkNilE`,
`getCallE`) → `nilPool` | `nilNew`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem nilK2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (hget : PoolGetLive (LibNE.program.link impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hno : NewobjectLiveContract64 (LibNE.program.link impl) (cA "runtime.newobject") 4096 R)
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
    (hK' : ∀ s'' : State, s''.regs 4 = BitVec.ofNat 64 (sp + 0x498 + 8) → s''.regs 5 = BitVec.ofNat 64 bp →
      s''.regs 14 = s.regs 14 → s''.xmm 15 = 0 →
      PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s'' → F s'')
    (M : Janus.Arm64.Memory) (hF : MemFrame s.mem M [(sp + 0x390, sp + 0x498), (sp + 0x4d0, sp + 0x4f8)])
    (hrg : M.regions = s.mem.regions)
    (hbp : M.readLE (sp + 0x490) 8 = bp) (hrv : M.readLE (sp + 0x498) 8 = ret0)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6189372) (hsp : T.regs 4 = BitVec.ofNat 64 (sp + 0x390))
    (h0 : T.regs 0 = BitVec.ofNat 64 zp') (h3 : T.regs 3 = BitVec.ofNat 64 zl') (h1 : T.regs 1 = BitVec.ofNat 64 zc')
    (h7 : T.regs 7 = BitVec.ofNat 64 st0) (h6 : T.regs 6 = BitVec.ofNat 64 xp) (h8 : T.regs 8 = BitVec.ofNat 64 xl)
    (h9 : T.regs 9 = BitVec.ofNat 64 xc) (h10 : T.regs 10 = BitVec.ofNat 64 slow)
    (h12 : T.regs 12 = BitVec.ofNat 64 yp) (h15 : T.regs 15 = BitVec.ofNat 64 yl)
    (h11 : T.regs 11 = BitVec.ofNat 64 n)
    (h14 : T.regs 14 = s.regs 14) (hfs : T.fsBase = s.fsBase) (hdf : T.df = s.df) (hx15 : T.xmm 15 = 0)
    (hmem : T.mem = M) :
    Reaches ((LibNE.program.link impl).withExit ret0) T (IsReturn F) := by
  obtain ⟨⟨-, hs14, -, -, -, hK1, -, hce, hsv⟩, -, hPG, -, -, -, hslow, r1, r2, r3, r4, r5, r6, hn, hn128, -, -,
    -, -, -, -, hyO, hya, hy48, -, hyl9, -, -, -, -, -, hxl128, -, hxc, hzp, ⟨hzlc, hxz, -, -⟩, hzc, -, -, -, -, hst0,
    -, -, -, -, -, -, -, hinv0, -⟩ := id hP
  have hce' := hce
  obtain ⟨hal, hKs, hsp2, hwacc, hg1, -, -, hwout, hgw, -, hLs, -⟩ := hce'
  have hyO' := hyO (by omega)
  have hya' := hya (by omega)
  have hy48' := hy48 (by omega)
  have hwrs : ∀ {ws : List (Nat × Nat)}, (∀ r ∈ ws, sp - K ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ sp + 0x510) →
      ∀ r ∈ ws, InRanges r.1 (r.2 - r.1) L ∨ Outside r.1 (r.2 - r.1) R.rt := fun hws r hr => by
    have := hws r hr; exact Or.inr (hwout.of_sub (by omega) (by omega))
  have hF0 : MemFrame s.mem M (R.rt ++ wN sp K) ∧ LiveFrame s.mem M L [] :=
    ⟨hF.mono fun a k ho => by
        rw [outside_append] at ho; have := ho.2
        simp only [wN, outside_cons, outside_nil, and_true] at this ⊢; omega,
      LiveFrame.of_win hF fun r hr => DivNil.outside_of_forall fun q hq => by
        have h1 := hLs r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        simp only [outside_cons, outside_nil, and_true] at h1
        rcases hq with rfl | rfl <;> simp only <;> omega⟩
  have hinvM : R.inv b L g (view R.rt L M) := Expmc.inv_frame hF (hwrs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega) hinv0
  have ht : ∀ {a : Nat}, sp + 0x498 - a = sp + 0x498 - a := rfl
  have hst00 : st0 = 0 := hst0
  subst hmem
  refine stkNilE impl ret0 hret (IsReturn F) (sp + 0x498) yp yl n T.mem (by omega) (by omega)
    (by rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)) (by omega)
    (by omega) (by omega) (by omega)
    (fun _ => by rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hya' (by omega) (by omega)) T hpc
    (hsp.trans (congrArg _ (by omega))) (by rw [h7, hst00]) h12 h15 h11 rfl ?_
  intro X M' xpc x4 x0 x5 x14 xfs xdf xx xm hFS hrgS q110 q80 q70 q38 q58 q60 q68 q70b
  have hwsS : ∀ r ∈ [(sp + 0x498 - 0x110, sp + 0x498 - 0x108), (sp + 0x498 - 0x80, sp + 0x498 - 0x78),
      (sp + 0x498 - 0x70, sp + 0x498 - 0x68), (sp + 0x498 - 0x38, sp + 0x498 - 0x30), (sp + 0x498 + 0x58, sp + 0x498 + 0x78)],
      sp - K ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ sp + 0x510 := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  have hM' := chainW hF0 hFS hLs (fun r hr => by have := hwsS r hr; omega) fun a k ho => by
    simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hcew := cenv_wN hce hM'.1 (hrgS.trans hrg)
  obtain ⟨-, -, -, hwacc', hg1', hg2', hg3', -, -, -, -, -⟩ := hcew
  have hinv' : R.inv b L g (view R.rt L M') := Expmc.inv_frame hFS (hwrs hwsS) hinvM
  have hnew0 : M'.readLE (Free.poolA + newOffset) 8 = 0 := by
    obtain ⟨-, e, o1, o2⟩ := hPG
    have o2' : Outside (Free.poolA + newOffset) 8 [(sp - K, sp + 0x510)] := o2
    have o1' : Outside (Free.poolA + newOffset) 8 R.rt := o1
    rw [hM'.1.readLE _ _ (by
      rw [outside_append]; refine ⟨o1', ?_⟩
      simp only [outside_cons, outside_nil, and_true] at o2'; simp only [wN, outside_cons, outside_nil, and_true]
      omega)]; exact e
  have hg14 : X.regs 14 = BitVec.ofNat 64 g := x14.trans (h14.trans hs14)
  refine getCallE impl R hget ret0 hret (IsReturn F) b L K g sp M' hal hK1 hKs hsp2 hwacc' hg1' hg2' hg3' hwout hgw hLs
    hsv hnew0 hinv' X xpc (x4.trans (congrArg _ (by omega))) hg14 x0 xm
    (by rw [show sp + 0x388 = sp + 0x498 - 0x110 by omega]; exact q110) ?_
  intro S' m p0 p4 p5 p14 px pfs pdf pm hMF hLF hrgm hcase
  have hm := chainR hM' hMF hLF fun a k ho => by simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rdm : ∀ a k, sp + 0x398 ≤ a → a + k ≤ sp + 0x510 → m.readLE a k = M'.readLE a k := fun a k h1 h2 =>
    hMF.readLE a k (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hwout.of_sub (by omega) (by omega), by omega, by omega⟩)
  have rdA : ∀ a k, sp + 0x4a0 ≤ a → a + k ≤ sp + 0x4d0 → m.readLE a k = s.mem.readLE a k := fun a k h1 h2 => by
    rw [rdm a k (by omega) (by omega), hFS.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have hzp' : zp' < 2 ^ 64 ∧ zl' < 2 ^ 64 ∧ zc' < 2 ^ 64 := by
    rcases hz with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
  have hxs : xp < 2 ^ 64 ∧ xl < 2 ^ 64 ∧ xc < 2 ^ 64 := by
    subst hxz; omega
  have tn : ∀ {v : Nat}, v < 2 ^ 64 → (BitVec.ofNat 64 v).toNat = v := fun h => by
    rw [BitVec.toNat_ofNat]; omega
  have hsp' : NilSp m (sp + 0x498) zp' zl' zc' yc xp xl xc 0 n yp mp yl mc := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rdm _ _ (by omega) (by omega), q38, h0, tn hzp'.1]
    · rw [rdm _ _ (by omega) (by omega), q80, h3, tn hzp'.2.1]
    · rw [rdm _ _ (by omega) (by omega), q70, h1, tn hzp'.2.2]
    · rw [rdA _ _ (by omega) (by omega), show sp + 0x498 + 0x18 = sp + 0x4b0 by omega]; exact r3
    · rw [rdm _ _ (by omega) (by omega), q58, h6, tn hxs.1]
    · rw [rdm _ _ (by omega) (by omega), q60, h8, tn hxs.2.1]
    · rw [rdm _ _ (by omega) (by omega), q68, h9, tn hxs.2.2]
    · rw [rdm _ _ (by omega) (by omega), q70b, h10, hslow]; rfl
    · rw [rdA _ _ (by omega) (by omega), show sp + 0x498 + 0x28 = sp + 0x4c0 by omega]; exact r5
    · rw [rdA _ _ (by omega) (by omega), show sp + 0x498 + 8 = sp + 0x4a0 by omega]; exact r1
    · rw [rdA _ _ (by omega) (by omega), show sp + 0x498 + 0x20 = sp + 0x4b8 by omega]; exact r4
    · rw [rdA _ _ (by omega) (by omega), show sp + 0x498 + 0x10 = sp + 0x4a8 by omega]; exact r2
    · rw [rdA _ _ (by omega) (by omega), show sp + 0x498 + 0x30 = sp + 0x4c8 by omega]; exact r6
  have hbpm : m.readLE (sp + 0x490) 8 = bp := by
    rw [rdm _ _ (by omega) (by omega), hFS.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hbp
  have hrvm : m.readLE (sp + 0x498) 8 = ret0 := by
    rw [rdm _ _ (by omega) (by omega), hFS.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hrv
  have hrgm' : m.regions = s.mem.regions := hrgm.trans (hrgS.trans hrg)
  have e14 : S'.regs 14 = s.regs 14 := p14.trans (x14.trans h14)
  have efs : S'.fsBase = s.fsBase := pfs.trans (xfs.trans hfs)
  have edf : S'.df = s.df := pdf.trans (xdf.trans hdf)
  have ex : S'.xmm 15 = 0 := px.trans (xx.trans hx15)
  rcases hcase with ⟨c0, c3, hinvm⟩ | ⟨d, rs, c0, c3, hd, hSh, hfr, hin, -, hinvm⟩
  · exact nilNew impl hap R hput hno H hRem hnsR hnfR hKR ret0 hret F hP hX hz hna hxl0 hyl0 hm1 hEv hK' m hm hrgm'
      rdA hsp' hbpm hrvm hinvm S' p0 p4 c0 c3 pm e14 efs edf ex
  · exact nilPool impl hap R hput H hRem hnsR hnfR hKR ret0 hret F hP hX hz hna hxl0 hyl0 hm1 hEv hK' m hm hrgm'
      rdA hsp' hbpm hrvm hd hSh hfr hin hinvm S' p0 p4 c0 c3 pm e14 efs edf ex

end FvModexp.Amd64.ExpN
