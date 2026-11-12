import FvModexp.Proofs.Arm64.Exp.NP2P
import FvModexp.Proofs.Arm64.Exp.NPowE
import FvModexp.Proofs.Arm64.Exp.NLift
import FvModexp.Proofs.Arm64.Exp.EvStmt
import FvModexp.Proofs.Arm64.Exp.NZOut

/-!
# `nat.expNN` (arm64): the even path — `m.isPow2()` fails, `z.expNNEven(stk, x, y, m)` (nat.go:717-718) to the return

From the `isPow2` loop head (`NDisp.disp`'s `KP`, `m[0]` even, after the make: context `ZM`) with `M` not a power of
two: `powAllE` (on `LibNE`), then the call of infra's `ExpEven.EvenSum` (a `Summary` on `LibNE`, `.full` form — the
recursive pair) with return point fn+0x618, and the shared epilogue `EpiK` (on `LibN`, lifted by `liftNE`). The even
callee's stack need/cost are bounded by the slow slot's (`hnE`, `hcE`): `nat.expNN`'s budget `NCost` is used with a
slow cost that covers both (`NHyp.SlowHyp.mono`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the call of `expNNEven` from its entry `S` (on `LibNE`) to expNN's return (`Post`) -/
theorem callE (impl : List Segment) (hap : ImplApart Extracted.program impl)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {sp zp zc st xp xl yp yl mp n f29 : Nat} {s S : State}
    (hs : s.sp.toNat = sp + 1312) (hal : sp % 16 = 0) (hK : K ≤ sp) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hLs : LiveSep L [(sp - K, sp + 1432)]) (hrw : LiveSep [(sp - K, sp + 1432)] R.rt)
    (hsok : StkOK s.mem R L st) (hstw : Apart st 24 (sp - K) (K + 1432))
    (hF0 : MemFrame s.mem S.mem (R.rt ++ wN sp K)) (hLF0 : LiveFrame s.mem S.mem L [])
    {L1 : List (Nat × Nat)} {b1 zq zcq stk v cst mk : Nat}
    (hx1 : LiveExt R L L1) (hb1 : b - mk ≤ b1) (hzq : ZArg R L sp K zp zc zq zcq)
    (hstk : stk ≤ K + 1056) (h28 : S.regs 28 = s.regs 28)
    (hv : v = natVal s.mem xp xl ^ natVal s.mem yp yl % natVal s.mem mp n)
    (hC : mk + cst ≤ NCost costF costR costS costP xl yl n (stLen s.mem st) (Nat.log2 (natVal s.mem mp n)))
    {P : State → Prop} {Q : State → State → Prop}
    (hE : Summary (LibNE.program.link impl) ExpEven.fnE P Q)
    (hpc : S.pc = BitVec.ofNat 64 ExpEven.fnE) (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (h30 : S.regs 30 = BitVec.ofNat 64 1788100)
    (hPS : P S) (hQ : ∀ s', Q S s' → s'.sp = S.sp ∧ s'.regs 18 = S.regs 18 ∧ s'.regs 28 = S.regs 28 ∧
      s'.regs 29 = S.regs 29 ∧ CPostG R b1 L1 stk 112 zq zcq st v cst S s')
    (harr : 0 < stCap S.mem st → Apart (stW S.mem st) (8 * stCap S.mem st) (sp - K) (K + 1432))
    (hc0 : stCap S.mem st = 0 → stW S.mem st = 0) (hlc : stLen S.mem st ≤ stCap S.mem st)
    (hacc : S.mem.accessible (sp + 1048) 256 true = true) (h29v : S.mem.readLE (sp + 1048) 8 = f29)
    (h30v : S.mem.readLE (sp + 1056) 8 = ret0) {M0 : Memory} (hsl : SlotEq S.mem M0 sp)
    (hEk : EpiK impl ret0 F sp f29 (S.regs 18) (S.regs 28) M0
      (Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  have hSs : S.sp.toNat = sp + 1056 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  have hrt : Outside (sp - K) (K + 1432) R.rt := by
    have := hrw _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
  refine Reaches.call_regions (hE.withExit hret) hpc hPS (fun s' hr' hq hrg' => ?_)
  obtain ⟨e1, e4, e2, -, hq'⟩ := hQ s' hq
  have hq2 := hq'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hFq, -⟩ := hq2
  have kp := fun {a k : Nat} (h : (sp + 1048 ≤ a ∧ a + k ≤ sp + 1064) ∨ (sp + 1168 ≤ a ∧ a + k ≤ sp + 1432)) =>
    keepS hSs hstk hK hrt hzq hstw harr hc0 hlc hFq h
  refine liftNE impl hap (hEk 1788100 s' (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (hr'.trans h30) (e1.trans hSsp) e4 e2
    (by rw [hFq.accessible]; exact hacc)
    (by rw [kp (Or.inl ⟨Nat.le_refl _, by omega⟩)]; exact h29v) (by rw [kp (Or.inl ⟨by omega, by omega⟩)]; exact h30v)
    (hsl.of_rd fun a k hs => kp (by unfold Slot at hs; omega))
    fun s'' f8 f3 f4 f5 => post_call hs hK hLs hrw hsok hstw hF0 hLF0 hx1 hb1 hzq hSs hstk h28 hv hC hq' f8 f3 f4 f5)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the `isPow2` loop head, `M` even and not a power of two: `expNNEven` to expNN's return -/
theorem evPath (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {stkE : Nat} {needE : Nat → Nat → Nat → Nat} {costE : Nat → Nat → Nat → Nat → Nat}
    (hEv : ExpEven.EvenSum impl R stkE 112 needE costE)
    (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st xp xl xc yp yl yc mp n mc slow f29 : Nat} {s S : State}
    {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hP : NPre R b L K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (hX : NHyp.XFacts R L xp xl xc)
    (hstk : stkE ≤ K + 1056) (hnE : needE xl yl n ≤ needS xl yl n) (hcE : ∀ l, costE l xl yl n ≤ costS l xl yl n)
    (hZ : ZM R b L g sp K zp zc st xp xl yp yl mp n s.mem S.mem L1 b1 zq zcq mk)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hy1 : ¬(yl = 1 ∧ s.mem.readLE yp 8 = 1))
    (hnp : ¬∃ k, natVal s.mem mp n = 2 ^ k) (hm0 : s.mem.readLE mp 8 % 2 = 0)
    (hpc : S.pc = BitVec.ofNat 64 powH) (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (hA : DArgs S zq zcq st xp xl xc yp yl yc mp n mc) (h13 : S.regs 13 = 0#64) (h28 : S.regs 28 = s.regs 28)
    (h29v : S.mem.readLE (sp + 1048) 8 = f29) (h30v : S.mem.readLE (sp + 1056) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq S.mem M0 sp)
    (hEk : EpiK impl ret0 F sp f29 (S.regs 18) (S.regs 28) M0
      (Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibNE.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, -, -, -, hal, hK4, hKs, hsp2, hacc, hwrt, hLs, -, -⟩, -, -, -, -, -,
    hn, hn128, hnmc, hmc, hmO, hma, hm48, hmN, hyO, -, hy48, hyN, hyl, hyc, hxO, -, -, hxN, hxl, hxp, hxc, -, -, -, ⟨-, hzW⟩,
    -, ⟨op, hOne, hSA⟩, hst0, hst48, hsok, hstw, -, harr, hc0, -, -, -, -, -, -, hnS, -, hbud, -⟩ := hP'
  obtain ⟨hF0, hLF0, hrg, hx1, hb1, hmk, hinv1, hZQ, hZA, hnz, hzq⟩ := hZ
  have hs : s.sp.toNat = sp + 1312 := by rw [hs1, BitVec.toNat_ofNat]; omega
  have hrtE : Outside (sp - K) (K + 1432) R.rt := by
    have := hwrt _ (List.mem_singleton_self _)
    simp only at this; rwa [show sp + 1432 - (sp - K) = K + 1432 by omega] at this
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
  have hmNS : NatNorm S.mem mp n := by
    rcases hmN with h | h
    · exact Or.inl h
    · right; rw [rd_held (held_sub hmO.1 (by omega) (by omega)) hLF0 hF0 (by have := hmO.2.1; unfold Apart at this ⊢; omega)]; exact h
  have hnpS : ¬∃ k, natVal S.mem mp n = 2 ^ k := by rw [hrdm]; exact hnp
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hA
  refine powAllE impl ret0 hret _ mp n S.mem S.sp S.regs hm48 (by rw [hF0.accessible]; exact hma) hn hmNS hnpS
    a1 a10 ?_ (n - 1) 0 S (by omega) hn (fun j hj => absurd hj (Nat.not_lt_zero _)) hpc rfl
    (fun _ _ _ _ => rfl) (by rw [h13]) rfl
  intro S' e1 e2 e3 e4 e5 e6 e7
  have r : ∀ r, r ≠ 1 → r ≠ 11 → r ≠ 13 → r ≠ 15 → r ≠ 16 → r ≠ 30 → S'.regs r = S.regs r := e3
  have hE := hEv b1 L1 zq n zcq st xp xl xc yp yl yc mp n mc
  have hacc2 : S'.mem.accessible (sp + 1048) 256 true = true := by
    rw [e7, hF0.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)
  have hS'sp : S'.sp = BitVec.ofNat 64 (sp + 1056) := e2.trans hSsp
  have hS's : S'.sp.toNat = sp + 1056 := by rw [hS'sp, BitVec.toNat_ofNat]; omega
  have h28' : S'.regs 28 = s.regs 28 :=
    (r 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28
  rw [← e7] at hF0 hLF0 hrg hinv1 hZQ ew el ec h29v h30v hsl hrdx hrdy hrdm
  refine callE impl hap ret0 hret F hs hal hKs (by omega) hsp2 hLs hwrt hsok hstw hF0 hLF0 hx1
    hb1 hZA hstk h28' ?_ ?_ hE e1 hS'sp e6 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hzq, hxc, hyc, ?_, ?_⟩
    (fun s' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, cpostG_of hzq h.2.2.2.2⟩)
    (by rw [ec, ew]; intro hc; exact (harr hc).1) (by rw [ec, ew]; exact hc0)
    (by rw [el, ec]; exact hsok.2.2.2.2.2.1) hacc2 h29v h30v hsl
    (by rw [r 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h28'.trans h28.symm]; exact hEk)
  · rw [hrdx, hrdy, hrdm]
  · rw [el]; have := hcE (stLen s.mem st); unfold NCost; omega
  · exact (r 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a0
  · exact e4.trans a11
  · exact (r 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a2
  · exact (r 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a3
  · exact (r 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a4
  · exact (r 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a5
  · exact (r 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a6
  · exact (r 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a7
  · exact (r 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a8
  · exact (r 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a9
  · exact (r 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a10
  · exact e5.trans a1
  · exact (r 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a12
  · refine ⟨cpre_at hP hF0 hLF0 hrg hx1 hinv1 hS'sp (h28'.trans hs28) hstk hZQ hnz
      (fun p k hpk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpk
        rcases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩))
      (by omega) (by rw [el]; have := hcE (stLen s.mem st); omega),
      by rw [hrdx]; exact val_pos hxN hxl0, by rw [hrdy]; exact val_two hyN hyl0 hy1,
      by rw [hrdm]; exact val_pos hmN (by omega), by rw [hrdm, val_mod2 hn]; exact hm0,
      hxl, hn128, hst0, hnmc, hmc,
      out_win_even (ZArg.out hZA hzW hrtE hKs) hS's hstk hKs, op, natOne_at hOne hSA hF0 hLF0 hx1 hS's hstk hKs hZA (by omega) ew el ec⟩
  · rw [e6, BitVec.toNat_ofNat]
  · rw [e6, BitVec.toNat_ofNat]; decide

end FvModexp.Arm64.ExpN
