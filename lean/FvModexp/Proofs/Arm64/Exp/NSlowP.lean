import FvModexp.Proofs.Arm64.Exp.NMkP
import FvModexp.Proofs.Arm64.Exp.NDisp

/-!
# `nat.expNN` (arm64): the `expNNSlow` path — `z.expNNSlow(stk, x, y, m)` (nat.go:700-702) to expNN's return

From `expNNSlow`'s entry (`NDisp.disp`'s `KS`, after the make: context `ZM`): `callC` with infra's `NHyp.SlowHyp`
(`0 < X` from `len x ≠ 0`, `2 ≤ Y` from `len y ≠ 0` and `y ≠ 1`, `0 < M` from `len m ≠ 0`, all normalised).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the `expNNSlow` path from its entry to expNN's return -/
theorem slowPath (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} {stk : Nat} {needS : Nat → Nat → Nat → Nat} {costS : Nat → Nat → Nat → Nat → Nat}
    (hSl : NHyp.SlowHyp impl R ns stk 112 needS costS)
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) (hn11 : ns.contains Extracted.seg11.name = false)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needP : Nat → Nat → Nat → Nat} {costP : Nat → Nat → Nat → Nat → Nat}
    {g sp zp zl zc st xp xl xc yp yl yc mp n mc slow f29 : Nat} {s S : State}
    {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hP : NPre R b L K costF needR costR needS needP costS costP g sp zp zl zc st xp xl xc yp yl yc mp n mc slow s)
    (hstk : stk ≤ K + 1056)
    (hZ : ZM R b L g sp K zp zc st xp xl yp yl mp n s.mem S.mem L1 b1 zq zcq mk)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hy1 : ¬(yl = 1 ∧ s.mem.readLE yp 8 = 1))
    (hpc : S.pc = BitVec.ofNat 64 slowA) (hSsp : S.sp = BitVec.ofNat 64 (sp + 1056))
    (hA : DArgs S zq zcq st xp xl xc yp yl yc mp n mc) (h28 : S.regs 28 = s.regs 28)
    (h30 : S.regs 30 = BitVec.ofNat 64 1787596)
    (h29v : S.mem.readLE (sp + 1048) 8 = f29) (h30v : S.mem.readLE (sp + 1056) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq S.mem M0 sp)
    (hEk : EpiK impl ret0 F sp f29 (S.regs 18) (S.regs 28) M0
      (Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, -, -, -, hal, hK4, hKs, hsp2, hacc, hwrt, hLs, -, -⟩, -, -, -, -, -,
    hn, hn128, -, hmc, hmO, -, hm48, hmN, hyO, -, hy48, hyN, hyl, hyc, hxO, -, -, hxN, hxl, hxp, hxc, -, -, -, -,
    -, -, -, hst48, hsok, hstw, -, harr, hc0, -, -, -, -, -, -, hnS, -, hbud, -⟩ := hP'
  obtain ⟨hF0, hLF0, hrg, hx1, hb1, hmk, hinv1, hZQ, hZA, hnz, hzq⟩ := hZ
  have hs : s.sp.toNat = sp + 1312 := by rw [hs1, BitVec.toNat_ofNat]; omega
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
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hA
  have hE := hSl b1 L1 (BitVec.ofNat 64 zq) (BitVec.ofNat 64 n) (BitVec.ofNat 64 zcq) (BitVec.ofNat 64 st)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc) (BitVec.ofNat 64 mp) (BitVec.ofNat 64 n) (BitVec.ofNat 64 mc)
  rw [tN' hzq, tN' (by omega : n < 2 ^ 64), tN' (by omega : zcq < 2 ^ 64), tN' (by omega : st < 2 ^ 64), tN' hxp,
    tN' (by omega : xl < 2 ^ 64), tN' (by omega : yp < 2 ^ 64), tN' (by omega : yl < 2 ^ 64),
    tN' (by omega : mp < 2 ^ 64),
    show segAddr Extracted.program NHyp.fnSlow = slowA by decide] at hE
  have hacc2 : S.mem.accessible (sp + 1048) 216 true = true := by
    rw [hF0.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)
  refine callC impl hap hns hn11 ret0 hret F hs hal hKs (by omega) hsp2 hLs hwrt hsok hstw hF0 hLF0 hx1
    hb1 hZA hstk h28 ?_ ?_ (Or.inr (Or.inl rfl)) hE hpc hSsp h30 ?_ ⟨?_, ?_, ?_, ?_⟩ (fun s' h => cpostG_of h)
    (by rw [ec, ew]; intro hc; exact (harr hc).1) (by rw [ec, ew]; exact hc0)
    (by rw [el, ec]; exact hsok.2.2.2.2.2.1) hacc2 h29v h30v hsl hEk
  · rw [hrdx, hrdy, hrdm]
  · rw [el]; unfold NCost; omega
  · simp only [ArgsFrom]
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, trivial⟩
  · exact cpre_at hP hF0 hLF0 hrg hx1 hinv1 hSsp (h28.trans hs28) hstk hZQ hnz
      (fun p k hpk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpk
        rcases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩))
      hnS (by rw [el]; omega)
  · rw [hrdx]; exact val_pos hxN hxl0
  · rw [hrdy]; exact val_two hyN hyl0 hy1
  · rw [hrdm]; exact val_pos hmN (by omega)

end FvModexp.Arm64.ExpN
