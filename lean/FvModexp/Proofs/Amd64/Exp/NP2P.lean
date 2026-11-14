import FvModexp.Proofs.Amd64.Exp.NSlowP
import FvModexp.Proofs.Amd64.Exp.NPow
import FvModexp.Proofs.Common.NPowMath

/-!
# `nat.expNN` (amd64): the power-of-two path — `m.isPow2()` then `z.expNNPowerOfTwo(stk, x, y, logM)`
(nat.go:712-714) to expNN's return (agent expmc s71; twin of `Arm64.ExpN.p2Path`)

From the `isPow2` loop head (`NDisp.disp`'s `KP`, `m[0]` even, after the make: context `ZM`) with `M = 2^k`:
`powAll` (the loop finds `logM = 64 (n - 1) + e = k`; the call writes the return address and `y` at
`[t - 0x110, t - 0xf0)`, `zm_frame`), then `callC` with `NHyp.P2Hyp` (`natOne` at the callee entry from `NPre`'s:
`natOne_at`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Amd64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `natOne` at a callee entry (`P2Hyp`'s conjunct) from `NPre`'s -/
theorem natOne_at {R : RtInv} {L L1 : List (Nat × Nat)} {sp K zp zc st stk op zq zcq : Nat}
    {M0 : Memory} {S : State}
    (hO : EvenHyp.NatOne R L M0 op ([(sp - K, sp + 0x510), (zp, zp + 8 * zc)] ++ ExpHyp.stWs M0 st))
    (hSA : NHyp.StkApart M0 st op 8)
    (hF : MemFrame M0 S.mem (R.rt ++ wN sp K)) (hLF : LiveFrame M0 S.mem L []) (hx : LiveExt R L L1)
    (hSsp : (S.regs 4).toNat = sp + 0x388) (hstk : stk ≤ K + 0x388) (hK : K ≤ sp)
    (hZA : ZArg R L sp K zp zc zq zcq) (hz0 : 0 < zcq)
    (ew : stW S.mem st = stW M0 st) (el : stLen S.mem st = stLen M0 st) (ec : stCap S.mem st = stCap M0 st) :
    EvenHyp.NatOne R L1 S.mem op (win S stk 112 ++ [(zq, zq + 8 * zcq)] ++ ExpHyp.stWs S.mem st) ∧
      NHyp.StkApart S.mem st op 8 := by
  obtain ⟨o1, o2, o3, o4, oa, ort, ow, opa, op48, oH, oow⟩ := hO
  simp only [ExpHyp.stWs, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ow oow
  have hws : ∀ {a k : Nat}, (InRanges a k L ∨ Outside a k R.rt) → a + k ≤ sp - K ∨ sp + 0x510 ≤ a →
      (a + k ≤ zp ∨ zp + 8 * zc ≤ a) → (a + k ≤ st ∨ st + 24 ≤ a) →
      (a + k ≤ stW M0 st + 8 * stLen M0 st ∨ stW M0 st + 8 * stCap M0 st ≤ a) →
      Outside a k (win S stk 112 ++ [(zq, zq + 8 * zcq)] ++ ExpHyp.stWs S.mem st) := fun hH h1 h2 h3 h4 => by
    simp only [win, hSsp, ExpHyp.stWs, stkWs, ew, el, ec, List.cons_append, List.nil_append, outside_cons,
      outside_nil, and_true]
    refine ⟨by omega, ?_, h3, h4⟩
    rcases hZA with ⟨h0, -⟩ | ⟨e1, e2, -⟩ | ⟨hin, hap⟩
    · omega
    · rw [e1, e2]; exact h2
    · have := apart_fresh hH hap hin; omega
  have hrt : ∀ {a k : Nat}, a + k ≤ sp - K ∨ sp + 0x510 ≤ a → Outside a k R.rt → Outside a k (R.rt ++ wN sp K) :=
    fun h ho => by
      rw [outside_append]; refine ⟨ho, ?_⟩
      simp only [wN, outside_cons, outside_nil, and_true]; omega
  have hO24 := hrt ow.1 ort
  refine ⟨⟨by rw [hF.readLE EvenHyp.natOneA 8 (hO24.of_sub (by omega) (by omega))]; exact o1,
    by rw [hF.readLE (EvenHyp.natOneA + 8) 8 (hO24.of_sub (by omega) (by omega))]; exact o2,
    by rw [hF.readLE (EvenHyp.natOneA + 16) 8 (hO24.of_sub (by omega) (by omega))]; exact o3,
    by rw [rd_mk oH hLF hF (by simp only [wN, outside_cons, outside_nil, and_true]; omega)]; exact o4,
    by rw [hF.accessible]; exact oa, ort, hws (Or.inr ort) ow.1 ow.2.1 ow.2.2.1 ow.2.2.2,
    by rw [hF.accessible]; exact opa, op48, hx.held oH, hws oH oow.1 oow.2.1 oow.2.2.1 oow.2.2.2⟩, ?_⟩
  intro h8
  obtain ⟨a1, a2⟩ := hSA h8
  rw [ew, el, ec]
  exact ⟨a1, a2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `ZM` survives a frame `ws` inside expNN's window minus the saved `BP` / return address (e.g. a call's return
address and stack arguments), given the stack header apart from the window -/
theorem zm_frame {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g fs sp K zp zc st xp xl yp yl mp n : Nat}
    {s0 M M' : Memory} {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hZ : ZM R b L g fs sp K zp zc st xp xl yp yl mp n s0 M L1 b1 zq zcq mk)
    {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions)
    (hws : ∀ a k, Outside a k (wN sp K) → Outside a k ws)
    (hwr : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt) (hLs : LiveSep L1 ws)
    (hstw : Apart st 24 (sp - K) (K + 0x510)) :
    ZM R b L g fs sp K zp zc st xp xl yp yl mp n s0 M' L1 b1 zq zcq mk := by
  obtain ⟨hF0, hLF0, hrg0, hx, hb, hmk, hinv, ⟨z1, z2, z3⟩, hZA, hnz, hzq⟩ := hZ
  have hst : Outside st 24 ws := hws _ _ (by
    simp only [wN, outside_cons, outside_nil, and_true]; unfold Apart at hstw; omega)
  have ew : stW M' st = stW M st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  have el : stLen M' st = stLen M st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  have ec : stCap M' st = stCap M st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  refine ⟨hF0.trans hF fun a k ho => ⟨ho, by rw [outside_append] at ho; exact hws a k ho.2⟩,
    hLF0.trans (LiveFrame.of_win hF fun r hr => hLs r (hx.mem_old hr)) (fun _ _ h => h), hrg.trans hrg0, hx, hb, hmk,
    Expmc.inv_frame hF (fun r hr => Or.inr (hwr r hr)) hinv,
    ⟨z1, natLive_frame z2 (LiveExt.refl R L1) hF, fun h => ?_⟩, hZA, hnz, hzq⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := z3 h
  refine ⟨a1, a2, a3, a4, ?_, a6⟩
  show Apart zq (8 * zcq) (stW M' st + 8 * stLen M' st) (8 * (stCap M' st - stLen M' st))
  rw [ew, el, ec]; exact a5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the power-of-two path from the `isPow2` loop head (`RSP = sp + 0x390`) to expNN's return -/
theorem p2Path (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} {stk : Nat} {needP : Nat → Nat → Nat → Nat} {costP : Nat → Nat → Nat → Nat → Nat}
    (hP2 : NHyp.P2Hyp impl R ns stk 112 needP costP)
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) (hnf : ns.contains fn = false)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS : Nat → Nat → Nat → Nat}
    {costS : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow bp : Nat} {s S : State}
    {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hX : NHyp.XFacts R L xp xl xc) (hstk : stk ≤ K + 0x388)
    (hZ : ZM R b L g fs sp K zp zc st xp xl yp yl mp n s.mem S.mem L1 b1 zq zcq mk)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hpow : ∃ k, natVal s.mem mp n = 2 ^ k) (hm0 : s.mem.readLE mp 8 % 2 = 0)
    (hpc : S.rip = BitVec.ofNat 64 powH) (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x390))
    (a0 : S.regs 0 = BitVec.ofNat 64 zq) (a1 : S.regs 1 = BitVec.ofNat 64 zcq) (a11 : S.regs 11 = BitVec.ofNat 64 n)
    (a7 : S.regs 7 = BitVec.ofNat 64 st) (a6 : S.regs 6 = BitVec.ofNat 64 xp) (a8 : S.regs 8 = BitVec.ofNat 64 xl)
    (a9 : S.regs 9 = BitVec.ofNat 64 xc) (a12 : S.regs 12 = BitVec.ofNat 64 yp)
    (a15 : S.regs 15 = BitVec.ofNat 64 yl) (a2 : S.regs 2 = BitVec.ofNat 64 yc) (a3 : S.regs 3 = BitVec.ofNat 64 n)
    (a13 : S.regs 13 = BitVec.ofNat 64 mp) (a10 : S.regs 10 = 0#64)
    (hzs : S.mem.readLE (sp + 0x438) 8 = zq)
    (h14 : S.regs 14 = s.regs 14) (hfsS : S.fsBase = s.fsBase) (hdfS : S.df = s.df) (hx15 : S.xmm 15 = 0)
    (hbp : S.mem.readLE (sp + 0x490) 8 = bp) (hrv : S.mem.readLE (sp + 0x498) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq S.mem M0 (sp + 0x498))
    (hEk : EpiK impl ret0 F (sp + 0x498) bp (S.regs 14) M0
      (Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs4, hs14, hsfs, -, hsdf, hK1, hK2, hce, -⟩, -, -, -, -, -, -, -, -, -, -, -,
    hn, hn128, -, hmc, hmO, hma, hm48, hmN, hyO, -, hy48, hyN, hyl, hyc, hxO, -, hx48, hxN, hxl, hxlc, hxc, -, -, -, -,
    -, ⟨op, hOne, hSA⟩, hst0, hst48, hsok, hstw, -, -, harr, hc0, -, -, -, -, -, -, -, -, hnP, hbud, -, -, hXG⟩ := hP'
  obtain ⟨hal, hK0, hA0, hacc, -, -, -, hwrt, -, -, hLs, -⟩ := hce
  have hs : (s.regs 4).toNat = sp + 0x498 := by rw [hs4, BitVec.toNat_ofNat]; omega
  have hrw := rw_of hK0 hwrt
  have hzq := hZ.2.2.2.2.2.2.2.2.2.2
  have hnz := hZ.2.2.2.2.2.2.2.2.2.1
  have hzc40 := hZ.2.2.2.2.2.2.2.1.1
  have hF0 := hZ.1
  have hLF0 := hZ.2.1
  -- the modulus words
  have hrdm : natVal S.mem mp n = natVal s.mem mp n := rd_held hmO.1 hLF0 hF0 hmO.2.1
  obtain ⟨k, hk⟩ := hpow
  have hkS : natVal S.mem mp n = 2 ^ k := hrdm.trans hk
  have hmNS : NatNorm S.mem mp n := by
    rcases hmN with h | h
    · exact Or.inl h
    · right; rw [rd_held (held_sub hmO.1 (by omega) (by omega)) hLF0 hF0 (by have := hmO.2.1; unfold Apart at this ⊢; omega)]; exact h
  obtain ⟨hk1, hk2, hw⟩ := FvModexp.Expmc.pow_words S.mem mp n k hn hkS hmNS
  have hlog : Nat.log2 (natVal s.mem mp n) = k := by rw [hk, Nat.log2_two_pow]
  have hk0 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · have h2 := val_mod2 (M := s.mem) (mp := mp) hn
      rw [hk, h0, Nat.pow_zero] at h2; omega
    · exact h0
  have hSs : (S.regs 4).toNat = sp + 0x390 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  refine powAll impl ret0 hret _ S.regs S.fsBase S.df (S.xmm 15) (sp + 0x498) mp n (k - 64 * (n - 1)) S.mem
    (by omega) (by omega) (by rw [hF0.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
    hm48 (by rw [hF0.accessible]; exact hma) (by omega) hw
    (by rw [show sp + 0x498 - 0x60 = sp + 0x438 by omega, hzs, a0, BitVec.toNat_ofNat]; omega) a3
    (by rw [hSsp]; exact congrArg _ (by omega)) a13 ?_ (n - 1) 0 S (by omega) hn hpc (fun _ _ => rfl) (by rw [a10]) rfl rfl rfl rfl
  intro S' M' e_rip e4 e0 e1 e3 e7 e6 e8 e9 e10 e14 efs edf ex15 emem hMF hrg' hra' hy0 hy1 hy2
  rw [show 64 * (n - 1) + (k - 64 * (n - 1)) = k by omega] at e10
  subst emem
  have hws : ∀ a k, Outside a k (wN sp K) → Outside a k [(sp + 0x498 - 0x110, sp + 0x498 - 0xf0)] := fun a k ho => by
    simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hLs1 : LiveSep L1 [(sp + 0x498 - 0x110, sp + 0x498 - 0xf0)] := fun r hr => by
    have := (hZ.2.2.2.1.liveSep hLs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show sp + 0x510 - (sp - K) = K + 0x510 by omega]; exact hwrt)) r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  have hZ' := zm_frame hZ hMF hrg' hws (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      exact hwrt.of_sub (by omega) (by omega)) hLs1 hstw
  obtain ⟨hF0', hLF0', hrg1, hx1, hb1, hmk, hinv1, hZQ, hZA, -, -⟩ := hZ'
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S'.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF0' hF0' (by unfold Apart at hstw ⊢; omega)
  have ew : stW S'.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S'.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S'.mem st = stCap s.mem st := rdh 16 (by omega)
  have hrdx : natVal S'.mem xp xl = natVal s.mem xp xl :=
    rd_held (held_sub hxO.1 (Nat.le_refl _) (by omega)) hLF0' hF0' (by have := hxO.2.1; unfold Apart at this ⊢; omega)
  have hrdy : natVal S'.mem yp yl = natVal s.mem yp yl := rd_held hyO.1 hLF0' hF0' hyO.2.1
  have hE := hP2 b1 L1 (BitVec.ofNat 64 zq) (BitVec.ofNat 64 n) (BitVec.ofNat 64 zcq) (BitVec.ofNat 64 st)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 k) yp yl yc
  rw [tN' hzq, tN' (by omega : n < 2 ^ 64), tN' (by omega : zcq < 2 ^ 64), tN' (by omega : st < 2 ^ 64),
    tN' (by omega : xp < 2 ^ 64), tN' (by omega : xc < 2 ^ 64), tN' (by omega : xl < 2 ^ 64),
    tN' (by omega : k < 2 ^ 64)] at hE
  have hS'sp : S'.regs 4 = BitVec.ofNat 64 (sp + 0x388) := by rw [e4]; exact congrArg _ (by omega)
  have hS's : (S'.regs 4).toNat = sp + 0x388 := by rw [hS'sp, BitVec.toNat_ofNat]; omega
  have kf : ∀ a k, sp + 0x3f8 ≤ a → S'.mem.readLE a k = S.mem.readLE a k := fun a k ha =>
    hMF.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hOne' := natOne_at hOne hSA hF0' hLF0' hx1 hS's hstk hK0 hZA (by omega) ew el ec
  refine callC impl hap hns hnf ret0 hret F (bp := bp) hs hK0 (by omega) hA0 hLs hrw hsok hstw hF0' hLF0' hx1
    hb1 hZA hstk (e14.trans h14) (efs.trans hfsS) (edf.trans hdfS) ?_ ?_
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by simp [numIntRegs]) hE
    (by rw [e_rip, show segAddr Extracted.program NHyp.fnP2 = p2A by decide]) hS'sp
    (by rw [← show sp + 0x498 - 0x110 = sp + 0x388 by omega]; exact hra') (ex15.trans hx15)
    (edf.trans (hdfS.trans hsdf)) ?_ ⟨?_, ⟨?_, ?_, ?_, by omega, by omega, by omega, ?_⟩, hxlc, hxc, ?_⟩
    (fun s' h => ⟨h.1, h.2.1, cpostG_of hzq h⟩)
    (by rw [ec, ew]; intro hc; exact (harr hc).1) (by rw [ec, ew]; exact hc0)
    (by rw [el, ec]; exact hsok.2.2.2.2.2.1)
    (by rw [hF0'.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega))
    (by rw [kf _ _ (by omega)]; exact hbp) (by rw [kf _ _ (by omega)]; exact hrv)
    (hsl.of_rd fun a k hs => kf a k (by unfold Slot at hs; omega)) (by rw [e14]; exact hEk)
  · rw [hrdx, hrdy, hk]
  · rw [el, hlog]; unfold NCost; omega
  · simp [ArgsFrom64, argReg, intArgRegs, e0, e1, e3, e7, e6, e8, e9, e10, a0, a1, a11, a7, a6, a8, a9]
  · simp only [NHyp.StkArg, hS's]
    refine ⟨?_, ?_, ?_⟩
    · rw [show sp + 0x388 + 0 + 8 = sp + 0x498 - 0x108 by omega, hy0, a12, BitVec.toNat_ofNat]; omega
    · rw [show sp + 0x388 + 0 + 16 = sp + 0x498 - 0x100 by omega, hy1, a15, BitVec.toNat_ofNat]; omega
    · rw [show sp + 0x388 + 0 + 24 = sp + 0x498 - 0xf8 by omega, hy2, a2, BitVec.toNat_ofNat]; omega
  · exact cpre_at hP hF0' hLF0' hrg1 hx1 hinv1 hS'sp (e14.trans (h14.trans hs14))
      (by rw [efs, hfsS]; exact hsfs) hstk hZQ hnz
      (fun p k hpk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpk
        rcases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩))
      (by rw [← hlog]; exact hnP) (by rw [el, ← hlog]; omega)
  · rw [hrdx]; exact val_pos hxN hxl0
  · rw [hrdy]; exact val_pos hyN hyl0
  · exact ⟨op, hOne'⟩
  · obtain ⟨xa, xn, xd, xacc, xst, xfr⟩ := hXG
    refine ⟨xa, by rw [hOne'.1.1, ← hOne.1]; exact xn, by rw [hF0'.accessible]; exact xd,
      by rw [hF0'.accessible]; exact xacc, xst, ?_⟩
    simp only [NHyp.freeOf, ew, el, ec]; exact xfr

end FvModexp.Amd64.ExpN
