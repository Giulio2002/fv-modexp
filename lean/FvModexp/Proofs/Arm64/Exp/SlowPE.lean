import FvModexp.Proofs.Arm64.Exp.SlowPK

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): **`segE`** — entry `fnE` → `KM` (`MV`) (agent expmc)

`runE` (frame, spills, `CMP R5, R2; BLT`): reuse (`len x ≤ cap z`, `dl_reuse`) / `makeslice(Word, 1, 1)` (`len x = 1`)
/ `makeslice(Word, len x, len x + 4)` (`mkCall`, `dl_fresh`, `runM1` / `runMN`). The fresh capacity is
`makeCap (len x)`; the budget drops by at most `makeCost (len x)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

theorem rsx {T : State} {junk : Nat → W64} {ptr : W64} {f : Flags} {v : Nat → BitVec 128} {m : Memory}
    {ex : Option (Nat × Nat)} {ep : Nat → Bool} :
    (retStateX T junk [ptr] f v m ex ep).sp = T.sp ∧ (retStateX T junk [ptr] f v m ex ep).regs 28 = T.regs 28 ∧
      (retStateX T junk [ptr] f v m ex ep).regs 29 = T.regs 29 ∧
      (retStateX T junk [ptr] f v m ex ep).regs 18 = T.regs 18 ∧
      (retStateX T junk [ptr] f v m ex ep).regs 0 = ptr ∧
      (retStateX T junk [ptr] f v m ex ep).pc = T.regs 30 ∧ (retStateX T junk [ptr] f v m ex ep).mem = m := by
  simp [retStateX, callRegs_apply]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State}

/-- the stable slots after the prologue -/
theorem sf_of {M : Memory} {r29 ret : Nat} (a1 : M.readLE (sp - 8) 8 = r29) (a2 : M.readLE sp 8 = ret)
    (a3 : M.readLE (sp + 464) 8 = st) (a4 : M.readLE (sp + 472) 8 = xp) (a5 : M.readLE (sp + 480) 8 = xl)
    (a6 : M.readLE (sp + 488) 8 = xc) (a7 : M.readLE (sp + 496) 8 = yp) (a8 : M.readLE (sp + 504) 8 = yl)
    (a9 : M.readLE (sp + 520) 8 = mp) (a10 : M.readLE (sp + 528) 8 = ml) (a11 : M.readLE (sp + 536) 8 = mc) :
    SF sp st xp xl xc yp yl mp ml mc r29 ret M :=
  ⟨a3, a4, a5, a6, a7, a8, a9, a10, a11, a1, a2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the `makeslice(Word, n, c)` call of the prologue and its return run (`runM1` / `runMN`) → `KM` -/
theorem mkSeg {impl : List Segment} (hmk : MakesliceLiveContract (LibW.program.link impl) mkA 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {r29 ret : Nat}
    {ret0 : BitVec 64} {Q : State → Prop} {n c : Nat} (hc : c = makeCap xl) (hn : n ≤ c) (hxc : xl ≤ c)
    (hxl : xl ≤ 128) (hbud : makeCost xl ≤ b)
    (KMc : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 z zc' : Nat),
      KM R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s (s.regs 18) r29 ret S L1 b1 z zc' →
      b - makeCost xl ≤ b1 → ReachesRet (LibW.program.link impl) ret0 S Q)
    (T : State) (M : Memory) (hpc : T.pc = BitVec.ofNat 64 mkA) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h0 : T.regs 0 = 2641088#64) (h1 : T.regs 1 = BitVec.ofNat 64 n) (h2 : T.regs 2 = BitVec.ofNat 64 c)
    (h30 : T.regs 30 = BitVec.ofNat 64 (if xl = 1 then mk1R else mk2R)) (h18 : T.regs 18 = s.regs 18)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = BitVec.ofNat 64 (sp - 8)) (hm : T.mem = M)
    (hF : MemFrame s.mem M (FWp sp)) (hrg : M.regions = s.mem.regions) (hsf : SF sp st xp xl xc yp yl mp ml mc r29 ret M)
    (r112 : xl ≠ 1 → M.readLE (sp + 112) 8 = xl + 4) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hwacc := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hw : WC R L K g sp st zp zc s.mem M L b (stLen s.mem st) := wc_init hP hF hrg
  have hc0 : 0 < c := by rw [hc]; unfold makeCap; split <;> omega
  have hc17 : c ≤ 2 ^ 17 := by rw [hc]; unfold makeCap; split <;> omega
  have hcost : blockSize (8 * c) true ≤ b := by
    have := blockSize_le_allocCost (8 * c) true
    have e : makeCost xl = allocCost (8 * c) := by rw [hc]; rfl
    omega
  have hra : (if xl = 1 then mk1R else mk2R) < 2 ^ 48 := by split <;> decide
  have hra4 : (if xl = 1 then mk1R else mk2R) % 4 = 0 := by split <;> decide
  refine mkCall mkA_eq hmk ret0 Q hP hw hn hc0 hc17 hra4 hra hcost T hpc hsp h28 hm h0 h1 h2 h30 ?_
  intro ptr junk f v m ex ep hA
  obtain ⟨t1, t28, t29, t18, t0, tpc, tm⟩ := @rsx T junk ptr f v m ex ep
  have hacc : m.accessible (sp - 8) 552 true = true := by
    rw [hA.macc, hw.fr.accessible]; exact Memory.accessible_mono _ hwacc (by omega) (by omega)
  have hsf' : SF sp st xp xl xc yp yl mp ml mc r29 ret m :=
    hsf.keep fun a k ha => hA.keep a k (by omega)
  have hptr : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hdl := dl_fresh hP hw hA (by rw [hc]; unfold makeCap; split <;> omega) hc0
  have hbud' : b - makeCost xl ≤ b - blockSize (8 * c) true := by
    have := blockSize_le_allocCost (8 * c) true
    have e : makeCost xl = allocCost (8 * c) := by rw [hc]; rfl
    have := hA.rc; omega
  have hjc : ∀ S' : State, S'.sp = T.sp → S'.regs 28 = T.regs 28 → S'.regs 29 = T.regs 29 →
      S'.regs 18 = T.regs 18 → S'.mem = m →
      JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s (s.regs 18) r29 ret S' S'.mem
        (L ++ [(ptr.toNat, ptr.toNat + blockSize (8 * c) true)]) (b - blockSize (8 * c) true) :=
    fun S' g1 g28 g29 g18 gm => by
      rw [gm]; exact ⟨hA.wc, gm, g1.trans hsp, g28.trans h28, g29.trans h29, g18.trans h18, hsf'⟩
  by_cases h1x : xl = 1
  · subst h1x
    have ec : c = 1 := by rw [hc]; rfl
    subst ec
    refine runM1 ret0 Q sp st xp 1 yp yl m hal hsp2 hacc hsf'.s464 hsf'.s472 hsf'.s480 hsf'.s496 hsf'.s504 _
      (by rw [tpc, h30]; rfl) (t1.trans hsp) tm ?_
    intro S' pcS spS mS e0 e1 e2 e3 e4 e5 e7 e8 e18 e28 e29
    refine KMc S' _ _ ptr.toNat 1 ⟨pcS, hjc S' (spS.trans t1) (e28.trans t28) (e29.trans t29) (e18.trans t18) mS, by rw [mS]; exact hdl, Nat.le_refl _, by rw [e0, t0]; simp, e1, e2, e3, e4, e5, e7, e8⟩ hbud'
  · have hr112 := r112 h1x
    have ec : c = xl + 4 := by rw [hc]; unfold makeCap; rw [ite_eq_right h1x]
    subst ec
    have r112' : m.readLE (sp + 112) 8 = xl + 4 := by rw [hA.keep _ _ (by omega)]; exact hr112
    refine runMN ret0 Q sp st xp xl yp yl m hal hsp2 hacc hsf'.s464 hsf'.s472 hsf'.s480 hsf'.s496 hsf'.s504 r112' _
      (by rw [tpc, h30, ite_eq_right h1x]) (t1.trans hsp) tm ?_
    intro S' pcS spS mS e0 e1 e2 e3 e4 e5 e7 e8 e18 e28 e29
    refine KMc S' _ _ ptr.toNat (xl + 4) ⟨pcS, hjc S' (spS.trans t1) (e28.trans t28) (e29.trans t29)
      (e18.trans t18) mS, by rw [mS]; exact hdl, by omega, by rw [e0, t0]; simp, e1, e2, e3, e4, e5, e7,
      e8⟩ hbud'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`segE`: entry → `KM`** (see the module doc) -/
theorem segE {impl : List Segment} (hmk : MakesliceLiveContract (LibW.program.link impl) mkA 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {zl ret : Nat} (hzl : zl < 2 ^ 64)
    (hret : ret < 2 ^ 48) (hxl0 : 0 < xl) (hbud : makeCost xl ≤ b)
    (hpc : s.pc = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc)
    (h3 : s.regs 3 = BitVec.ofNat 64 st) (h4 : s.regs 4 = BitVec.ofNat 64 xp) (h5 : s.regs 5 = BitVec.ofNat 64 xl)
    (h6 : s.regs 6 = BitVec.ofNat 64 xc) (h7 : s.regs 7 = BitVec.ofNat 64 yp) (h8 : s.regs 8 = BitVec.ofNat 64 yl)
    (h9 : s.regs 9 = BitVec.ofNat 64 yc) (h10 : s.regs 10 = BitVec.ofNat 64 mp)
    (h11 : s.regs 11 = BitVec.ofNat 64 ml) (h12 : s.regs 12 = BitVec.ofNat 64 mc)
    (h30 : s.regs 30 = BitVec.ofNat 64 ret)
    {ret0 : BitVec 64} {Q : State → Prop}
    (KMc : ∀ (S : State) (L1 : List (Nat × Nat)) (b1 z zc' : Nat),
      KM R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s (s.regs 18) (s.regs 29).toNat ret S L1 b1 z zc' →
      b - makeCost xl ≤ b1 → ReachesRet (LibW.program.link impl) ret0 S Q) :
    ReachesRet (LibW.program.link impl) ret0 s Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hwacc := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hg1 := hP.1.2.2.1
  have hg2 := hP.1.2.2.2.1
  have hg3 := hP.1.2.2.2.2.1
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzp : zp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxp : xp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxc : xc < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, hyp, hyc, hmp, hmc, -⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyl : yl ≤ 2 ^ 9 := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hml : ml ≤ 128 := hP.2.2.2.2.2.2.1
  have hst : st < 2 ^ 64 := by
    have := hP.stk0.2.2.2.1; omega
  have hacc : s.mem.accessible (sp - 8) 552 true = true := Memory.accessible_mono _ hwacc (by omega) (by omega)
  refine runE ret0 Q sp g zp zl zc st xp xl xc yp yl yc mp ml mc ret (s.regs 29) s.mem hal (by omega) hsp2 hacc hg1
    hg2 (by omega) hxl hret hzp hzl hzc hxp hxc hyp (by omega) hyc hmp (by omega) hmc hst s hpc hP.1.1 h0 h1 h2 h3 h4
    h5 h6 h7 h8 h9 h10 h11 h12 hP.1.2.1 rfl h30 rfl ?_ ?_ ?_
  · intro S' M' pcS spS hle e0 e1 e2 e3 e4 e5 e7 e8 e18 e28 e29 mS hF hrg a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    have hw : WC R L K g sp st zp zc s.mem M' L b (stLen s.mem st) := wc_init hP hF hrg
    have hz0 : 0 < zc := by omega
    subst mS
    exact KMc S' L b zp zc ⟨pcS, ⟨hw, rfl, spS, e28, e29, e18, sf_of a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11⟩,
      dl_reuse hP hF hz0, hle, e0, e1, e2, e3, e4, e5, e7, e8⟩ (Nat.sub_le _ _)
  · intro S' M' pcS spS hlt h1x e0 e1 e2 e30 e18 e28 e29 mS hF hrg a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    subst h1x
    exact mkSeg hmk hP rfl (Nat.le_refl _) (Nat.le_refl _) hxl hbud KMc S' M' pcS spS e0 e1 e2
      (by rw [e30]; rfl) e18 e28 e29 mS hF hrg (sf_of a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) (fun h => absurd rfl h)
  · intro S' M' pcS spS hlt h1x e0 e1 e2 e30 e18 e28 e29 mS hF hrg a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    exact mkSeg hmk hP (by unfold makeCap; rw [ite_eq_right h1x]) (by omega) (by omega) hxl hbud KMc S' M' pcS spS e0 e1
      e2 (by rw [e30, ite_eq_right h1x]) e18 e28 e29 mS hF hrg (sf_of a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) (fun _ => a12)

end

end FvModexp.Arm64.ExpSlow
