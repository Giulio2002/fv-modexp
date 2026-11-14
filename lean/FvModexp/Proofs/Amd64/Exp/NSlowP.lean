import FvModexp.Proofs.Amd64.Exp.NZM
import FvModexp.Proofs.Amd64.Exp.NDisp

/-!
# `nat.expNN` (amd64): the `expNNSlow` path — `z.expNNSlow(stk, x, y, m)` (nat.go:700-702) to expNN's return (agent
expmc s71; twin of `Arm64.ExpN.slowPath`)

From `expNNSlow`'s entry (`NDisp.disp`'s `KS`, after the make: context `ZM`; `z''` in RAX/RBX/RCX with `len = n`,
`stk` RDI, `x` RSI/R8/R9, `y` and `m` on the stack at `RSP + 8 … RSP + 48`): `callC` with `NHyp.SlowHyp` (`0 < X`
from `len x ≠ 0`, `2 ≤ Y` from `len y ≠ 0` and `y ≠ 1`, `0 < M` from `len m ≠ 0`, all normalised; `x`'s `XFacts`
lifted to the call's live set; the post `CPostR0` as `CPostG` by `cpostG_of0`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Amd64.ExpN

/-- the registers and stack words at a callee entry `S` (`RSP = sp + 0x388`) of `z''.f(stk, x, y, m)`: `z''` (len
`n`), `stk`, `x` in registers, `y` and `m` on the stack -/
@[reducible] def DArgs (S : State) (sp zq zcq st xp xl xc yp yl yc mp n mc : Nat) : Prop :=
  S.regs 0 = BitVec.ofNat 64 zq ∧ S.regs 3 = BitVec.ofNat 64 n ∧ S.regs 1 = BitVec.ofNat 64 zcq ∧
  S.regs 7 = BitVec.ofNat 64 st ∧ S.regs 6 = BitVec.ofNat 64 xp ∧ S.regs 8 = BitVec.ofNat 64 xl ∧
  S.regs 9 = BitVec.ofNat 64 xc ∧
  S.mem.readLE (sp + 0x390) 8 = yp ∧ S.mem.readLE (sp + 0x398) 8 = yl ∧ S.mem.readLE (sp + 0x3a0) 8 = yc ∧
  S.mem.readLE (sp + 0x3a8) 8 = mp ∧ S.mem.readLE (sp + 0x3b0) 8 = n ∧ S.mem.readLE (sp + 0x3b8) 8 = mc

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the `expNNSlow` path from its entry to expNN's return -/
theorem slowPath (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} {stk : Nat} {needS : Nat → Nat → Nat → Nat} {costS : Nat → Nat → Nat → Nat → Nat}
    (hSl : NHyp.SlowHyp impl R ns stk 112 needS costS)
    (hns : ∀ x, ns.contains x = true → LibN.names.contains x = true) (hnf : ns.contains fn = false)
    (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (F : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needP : Nat → Nat → Nat → Nat}
    {costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow bp : Nat} {s S : State}
    {L1 : List (Nat × Nat)} {b1 zq zcq mk : Nat}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hX : NHyp.XFacts R L xp xl xc) (hstk : stk ≤ K + 0x388)
    (hZ : ZM R b L g fs sp K zp zc st xp xl yp yl mp n s.mem S.mem L1 b1 zq zcq mk)
    (hxl0 : xl ≠ 0) (hyl0 : yl ≠ 0) (hy1 : ¬(yl = 1 ∧ s.mem.readLE yp 8 = 1))
    (hpc : S.rip = BitVec.ofNat 64 slowA) (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x388))
    (hA : DArgs S sp zq zcq st xp xl xc yp yl yc mp n mc) (h14 : S.regs 14 = s.regs 14)
    (hfsS : S.fsBase = s.fsBase) (hdfS : S.df = s.df) (hx15 : S.xmm 15 = 0)
    (hra : S.mem.readLE (sp + 0x388) 8 = slowR)
    (hbp : S.mem.readLE (sp + 0x490) 8 = bp) (hrv : S.mem.readLE (sp + 0x498) 8 = ret0)
    {M0 : Memory} (hsl : SlotEq S.mem M0 (sp + 0x498))
    (hEk : EpiK impl ret0 F (sp + 0x498) bp (S.regs 14) M0
      (Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s)) :
    Reaches ((LibN.program.link impl).withExit ret0) S (IsReturn F) := by
  have hP' := hP
  obtain ⟨⟨hs4, hs14, hsfs, -, hsdf, -, -, hce, -⟩, -, -, -, -, -, -, -, -, -, -, -,
    hn, hn128, -, hmc, hmO, -, hm48, hmN, hyO, -, hy48, hyN, hyl, hyc, hxO, -, hx48, hxN, hxl, hxlc, hxc, -, -, -, -,
    -, -, hst0, hst48, hsok, hstw, -, -, harr, hc0, -, -, -, -, -, -, -, hnS, -, hbud, -⟩ := hP'
  obtain ⟨hal, hK0, hA0, hacc, -, -, -, hwrt, -, -, hLs, -⟩ := hce
  obtain ⟨hF0, hLF0, hrg, hx1, hb1, hmk, hinv1, hZQ, hZA, hnz, hzq⟩ := hZ
  have hs : (s.regs 4).toNat = sp + 0x498 := by rw [hs4, BitVec.toNat_ofNat]; omega
  have hrw := rw_of hK0 hwrt
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF0 hF0 (by unfold Apart at hstw ⊢; omega)
  have ew : stW S.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S.mem st = stCap s.mem st := rdh 16 (by omega)
  have hrdx : natVal S.mem xp xl = natVal s.mem xp xl :=
    rd_held (held_sub hxO.1 (Nat.le_refl _) (by omega)) hLF0 hF0 (by have := hxO.2.1; unfold Apart at this ⊢; omega)
  have hrdy : natVal S.mem yp yl = natVal s.mem yp yl := rd_held hyO.1 hLF0 hF0 hyO.2.1
  have hrdm : natVal S.mem mp n = natVal s.mem mp n := rd_held hmO.1 hLF0 hF0 hmO.2.1
  have hzc40 := hZQ.1
  obtain ⟨a0, a3, a1, a7, a6, a8, a9, r0, r1, r2, r3, r4, r5⟩ := hA
  have hE := hSl b1 L1 (BitVec.ofNat 64 zq) (BitVec.ofNat 64 n) (BitVec.ofNat 64 zcq) (BitVec.ofNat 64 st)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) yp yl yc mp n mc
  rw [tN' hzq, tN' (by omega : n < 2 ^ 64), tN' (by omega : zcq < 2 ^ 64), tN' (by omega : st < 2 ^ 64),
    tN' (by omega : xp < 2 ^ 64), tN' (by omega : xc < 2 ^ 64), tN' (by omega : xl < 2 ^ 64)] at hE
  have hSs : (S.regs 4).toNat = sp + 0x388 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  refine callC impl hap hns hnf ret0 hret F hs hK0 (by omega) hA0 hLs hrw hsok hstw hF0 hLF0 hx1
    hb1 hZA hstk h14 hfsS hdfS ?_ ?_ (Or.inr (Or.inl rfl)) (by simp [numIntRegs]) hE
    (by rw [hpc, show segAddr Extracted.program NHyp.fnSlow = slowA by decide]) hSsp hra hx15 (hdfS.trans hsdf) ?_
    ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, hst0⟩, hX.ext hx1⟩
    (fun s' h => ⟨h.1, h.2.1, cpostG_of0 hzq h⟩)
    (by rw [ec, ew]; intro hc; exact (harr hc).1) (by rw [ec, ew]; exact hc0)
    (by rw [el, ec]; exact hsok.2.2.2.2.2.1)
    (by rw [hF0.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hbp hrv hsl hEk
  · rw [hrdx, hrdy, hrdm]
  · rw [el]; unfold NCost; omega
  · simp [ArgsFrom64, argReg, intArgRegs, a0, a3, a1, a7, a6, a8, a9]
  · simp only [NHyp.StkArg, hSs]
    exact ⟨by rw [show sp + 0x388 + 0 + 8 = sp + 0x390 by omega]; exact r0,
      by rw [show sp + 0x388 + 0 + 16 = sp + 0x398 by omega]; exact r1,
      by rw [show sp + 0x388 + 0 + 24 = sp + 0x3a0 by omega]; exact r2⟩
  · simp only [NHyp.StkArg, hSs]
    exact ⟨by rw [show sp + 0x388 + 24 + 8 = sp + 0x3a8 by omega]; exact r3,
      by rw [show sp + 0x388 + 24 + 16 = sp + 0x3b0 by omega]; exact r4,
      by rw [show sp + 0x388 + 24 + 24 = sp + 0x3b8 by omega]; exact r5⟩
  · exact cpre_at hP hF0 hLF0 hrg hx1 hinv1 hSsp (h14.trans hs14) (by rw [hfsS]; exact hsfs) hstk hZQ hnz
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

end FvModexp.Amd64.ExpN
