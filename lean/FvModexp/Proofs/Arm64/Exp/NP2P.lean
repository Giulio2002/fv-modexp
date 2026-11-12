import FvModexp.Proofs.Arm64.Exp.NMkP
import FvModexp.Proofs.Arm64.Exp.NDisp
import FvModexp.Proofs.Arm64.Exp.NPow
import FvModexp.Proofs.Common.NPowMath

/-!
# `nat.expNN` (arm64): the power-of-two path — `m.isPow2()` then `z.expNNPowerOfTwo(stk, x, y, logM)`
(nat.go:712-714) to expNN's return

From the `isPow2` loop head (`NDisp.disp`'s `KP`, `m[0]` even, after the make: context `ZM`) with `M = 2^k`:
`powAll` (the loop finds `logM = 64 (n - 1) + e = k`), then `callC` with infra's `NHyp.P2Hyp` (`natOne` at the callee
entry from `NPre`'s: `natOne_at`). `val_mod2`: `M % 2 = m[0] % 2`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `natOne` at a callee entry (`P2Hyp`'s last conjunct) from `NPre`'s -/
theorem natOne_at {R : RtInv} {L L1 : List (Nat × Nat)} {sp K zp zc st stk op zq zcq : Nat}
    {M0 : Memory} {S : State}
    (hO : EvenHyp.NatOne R L M0 op ([(sp - K, sp + 1432), (zp, zp + 8 * zc)] ++ stkWs M0 st))
    (hSA : EvenHyp.StkApart M0 st op 8)
    (hF : MemFrame M0 S.mem (R.rt ++ wN sp K)) (hLF : LiveFrame M0 S.mem L []) (hx : LiveExt R L L1)
    (hSsp : S.sp.toNat = sp + 1056) (hstk : stk ≤ K + 1056) (hK : K ≤ sp)
    (hZA : ZArg R L sp K zp zc zq zcq) (hz0 : 0 < zcq)
    (ew : stW S.mem st = stW M0 st) (el : stLen S.mem st = stLen M0 st) (ec : stCap S.mem st = stCap M0 st) :
    EvenHyp.NatOne R L1 S.mem op (win S stk 112 ++ [(zq, zq + 8 * zcq)] ++ ExpHyp.stWs S.mem st) ∧
      EvenHyp.StkApart S.mem st op 8 := by
  obtain ⟨o1, o2, o3, o4, oa, ort, ow, opa, op48, oH, oow⟩ := hO
  simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ow oow
  have hws : ∀ {a k : Nat}, (InRanges a k L ∨ Outside a k R.rt) → a + k ≤ sp - K ∨ sp + 1432 ≤ a →
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
  have hrt : ∀ {a k : Nat}, a + k ≤ sp - K ∨ sp + 1432 ≤ a → Outside a k R.rt → Outside a k (R.rt ++ wN sp K) :=
    fun h ho => by
      rw [outside_append]; refine ⟨ho, ?_⟩
      simp only [wN, outside_cons, outside_nil, and_true]; omega
  have hO24 := hrt ow.1 ort
  refine ⟨⟨by rw [hF.readLE EvenHyp.natOneA 8 (hO24.of_sub (by omega) (by omega))]; exact o1,
    by rw [hF.readLE (EvenHyp.natOneA + 8) 8 (hO24.of_sub (by omega) (by omega))]; exact o2,
    by rw [hF.readLE (EvenHyp.natOneA + 16) 8 (hO24.of_sub (by omega) (by omega))]; exact o3,
    by rw [rd_held oH hLF hF (by unfold Apart; omega)]; exact o4,
    by rw [hF.accessible]; exact oa, ort, hws (Or.inr ort) ow.1 ow.2.1 ow.2.2.1 ow.2.2.2,
    by rw [hF.accessible]; exact opa, op48, hx.held oH, hws oH oow.1 oow.2.1 oow.2.2.1 oow.2.2.2⟩, ?_⟩
  intro h8
  obtain ⟨a1, a2⟩ := hSA h8
  rw [ew, el, ec]
  exact ⟨a1, a2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the power-of-two path from the `isPow2` loop head to expNN's return -/
theorem p2Path (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} {stk : Nat} {needP : Nat → Nat → Nat → Nat} {costP : Nat → Nat → Nat → Nat → Nat}
    (hP2 : NHyp.P2Hyp impl R ns stk 112 needP costP)
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) (hn11 : ns.contains Extracted.seg11.name = false)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS : Nat → Nat → Nat → Nat} {costS : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st xp xl xc yp yl yc mp n mc slow f29 : Nat} {s S : State}
    {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hP : NPre R b L K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (hX : NHyp.XFacts R L xp xl xc) (hstk : stk ≤ K + 1056)
    (hZ : ZM R b L g sp K zp zc st xp xl yp yl mp n s.mem S.mem L1 b1 zq zcq mk)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hpow : ∃ k, natVal s.mem mp n = 2 ^ k) (hm0 : s.mem.readLE mp 8 % 2 = 0)
    (hpc : S.pc = BitVec.ofNat 64 powH) (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (hA : DArgs S zq zcq st xp xl xc yp yl yc mp n mc) (h13 : S.regs 13 = 0#64) (h28 : S.regs 28 = s.regs 28)
    (h29v : S.mem.readLE (sp + 1048) 8 = f29) (h30v : S.mem.readLE (sp + 1056) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq S.mem M0 sp)
    (hEk : EpiK impl ret0 F sp f29 (S.regs 18) (S.regs 28) M0
      (Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, -, -, -, hal, hK4, hKs, hsp2, hacc, hwrt, hLs, -, -⟩, -, -, -, -, -,
    hn, hn128, -, hmc, hmO, hma, hm48, hmN, hyO, -, hy48, hyN, hyl, hyc, hxO, -, -, hxN, hxl, hxp, hxc, -, -, -, -,
    -, ⟨op, hOne, hSA⟩, hst0, hst48, hsok, hstw, -, harr, hc0, -, -, -, -, -, -, -, hnP, hbud, -⟩ := hP'
  obtain ⟨hF0, hLF0, hrg, hx1, hb1, hmk, hinv1, hZQ, hZA, hnz, hzq⟩ := hZ
  have hs : s.sp.toNat = sp + 1312 := by rw [hs1, BitVec.toNat_ofNat]; omega
  have hSs : S.sp.toNat = sp + 1056 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF0 hF0 (by unfold Apart at hstw ⊢; omega)
  have ew : stW S.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S.mem st = stCap s.mem st := rdh 16 (by omega)
  have hrdx : natVal S.mem xp xl = natVal s.mem xp xl := rd_held hxO.1 hLF0 hF0 hxO.2.1
  have hrdy : natVal S.mem yp yl = natVal s.mem yp yl := rd_held hyO.1 hLF0 hF0 hyO.2.1
  have hrdm : natVal S.mem mp n = natVal s.mem mp n := rd_held hmO.1 hLF0 hF0 hmO.2.1
  have hzc40 := hZQ.1
  -- the modulus words
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
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hA
  refine powAll impl ret0 hret _ mp n (k - 64 * (n - 1)) S.mem S.sp S.regs hm48
    (by rw [hF0.accessible]; exact hma) (by omega) hw a1 a10 ?_ (n - 1) 0 S (by omega) hn hpc rfl
    (fun _ _ _ _ => rfl) (by rw [h13]) rfl
  intro S' e1 e2 e3 e4 e5 e6 e7
  have r : ∀ r, r ≠ 1 → r ≠ 10 → r ≠ 13 → r ≠ 15 → r ≠ 16 → r ≠ 30 → S'.regs r = S.regs r := e3
  have hE := hP2 b1 L1 (BitVec.ofNat 64 zq) (BitVec.ofNat 64 n) (BitVec.ofNat 64 zcq) (BitVec.ofNat 64 st)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc) (BitVec.ofNat 64 k)
  rw [tN' hzq, tN' (by omega : n < 2 ^ 64), tN' (by omega : zcq < 2 ^ 64), tN' (by omega : st < 2 ^ 64), tN' hxp, tN' hxc,
    tN' (by omega : xl < 2 ^ 64), tN' (by omega : yp < 2 ^ 64), tN' (by omega : yl < 2 ^ 64),
    tN' (by omega : k < 2 ^ 64), show segAddr Extracted.program NHyp.fnP2 = p2A by decide] at hE
  have hacc2 : S'.mem.accessible (sp + 1048) 256 true = true := by
    rw [e7, hF0.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)
  have hS'sp : S'.sp = BitVec.ofNat 64 (sp + 1056) := e2.trans hSsp
  have hS's : S'.sp.toNat = sp + 1056 := by rw [hS'sp, BitVec.toNat_ofNat]; omega
  rw [← e7] at hF0 hLF0 hrg hinv1 hZQ ew el ec h29v h30v hsl hrdx hrdy
  refine callC impl hap hns hn11 ret0 hret F hs hal hKs (by omega) hsp2 hLs hwrt hsok hstw hF0 hLF0 hx1
    hb1 hZA hstk ((r 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28) ?_ ?_
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hE e1 hS'sp e6 ?_ ⟨⟨?_, ?_, ?_, by omega, by omega, hst0, ?_⟩,
      hX.1.1, hX.1.2.1⟩ (fun s' h => cpostG_of hzq h)
    (by rw [ec, ew]; intro hc; exact (harr hc).1) (by rw [ec, ew]; exact hc0)
    (by rw [el, ec]; exact hsok.2.2.2.2.2.1) hacc2 h29v h30v hsl
    (by rw [r 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      r 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hEk)
  · rw [hrdx, hrdy, hk]
  · rw [el, hlog]; unfold NCost; omega
  · simp only [ArgsFrom]
    have q := fun r h1 h2 h3 h4 h5 h6 => (e3 r h1 h2 h3 h4 h5 h6)
    refine ⟨(q 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a0,
      e4.trans a11, (q 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a2,
      (q 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a3,
      (q 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a4,
      (q 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a5,
      (q 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a6,
      (q 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a7,
      (q 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a8,
      (q 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a9, ?_, trivial⟩
    rw [e5]; congr 2; omega
  · exact cpre_at hP hF0 hLF0 hrg hx1 hinv1 hS'sp
      ((r 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h28.trans hs28)) hstk
      hZQ hnz
      (fun p k hpk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpk
        rcases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩))
      (by rw [← hlog]; exact hnP) (by rw [el, ← hlog]; omega)
  · rw [hrdx]; exact val_pos hxN hxl0
  · rw [hrdy]; exact val_pos hyN hyl0
  · exact ⟨op, natOne_at hOne hSA hF0 hLF0 hx1 hS's hstk hKs hZA (by omega) ew el ec⟩

end FvModexp.Arm64.ExpN
