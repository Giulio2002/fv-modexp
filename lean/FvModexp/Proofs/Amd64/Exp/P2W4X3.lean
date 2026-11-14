import FvModexp.Proofs.Amd64.Exp.P2W4X2
import FvModexp.Proofs.Amd64.Exp.P2W4Seg

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the exit's `make` allocation (agent divmc s77, port of divmc s74; amd64 twin of agent infra's
`Arm64.P2W4X3`)

`z.set(zz)` with `cap z < n` (nat.go:58-68): `makeslice(Word, n, n + 4)` (`[sp + 0x58] := n + 4`, return fn+0x930);
the reloads `R9 := [0x118]` (`zz`'s stack buffer), `SI := [0x68]` (`n`), `R8 := AX`, `R15 := [0x58]`, `AX := SI`, then
the join `xJ`. (`n = 1` with `cap z < 1` is refuted at the caller: the U-class buffer has positive capacity.)
`BF.alloc`: the body context through a live allocation.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

open FvModexp.Amd64.ExpHyp

section
variable {impl : List Amd64.Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `BF` through a live allocation -/
theorem BF.alloc (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 zzp tp : Nat} (h : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp)
    {m : Memory} {p rr n : Nat}
    (hA : AllocR R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 (lvlL (stLen s.mem st) lm) m p rr n) :
    BF R L K g sp st bp r zp zc xp xl xc yp yl lm s m (L1 ++ [(p, p + rr)]) (b1 - rr) zzp tp := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  unfold Apart at hstw
  have hbW := scr_win hP h.tz.bscr
  unfold Apart at hbW
  have hsok := h.wc.sok
  obtain ⟨e0, e1, e2⟩ := hdr3 (M := M) (M' := m) (st := st) fun j hj =>
    hA.rdH _ _ (hsok.2.1.sub (by omega) (by omega)) (by unfold Apart; omega)
  have hx : LiveExt R L1 (L1 ++ [(p, p + rr)]) :=
    LiveExt.single (by rw [show p + rr - p = rr by omega]; exact hA.rin)
      (by rw [show p + rr - p = rr by omega]; exact hA.rap)
  refine ⟨hA.wc, ESl.keep h.esl (fun a k ha => hA.keep a k (by omega)),
    h.tz.keep hA.macc hx e0 e1 e2 fun a k ha => ?_⟩
  rcases ha with ha | ha
  · exact hA.keep a k (by omega)
  · exact hA.rdH a k (h.tz.bscr.held.sub ha.1 ha.2) (by unfold Apart; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`make(nat, n, n + 4)`** at the exit (from the `makeslice` call) -/
theorem xA2 (hap : Amd64.ImplApart Extracted.program impl) (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp tp : Nat} (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp)
    {n Z cst : Nat} (hn1 : 0 < n) (hnW : n ≤ W lm) (hsrc : natVal M zzp n = Z)
    (r118 : M.readLE (sp + 0x120) 8 = zzp) (r68 : M.readLE (sp + 0x68) 8 = n)
    (r58 : M.readLE (sp + 0x58) 8 = n + 4) (rra : M.readLE (sp - 0x8) 8 = 6200304)
    (hbud : b + P2Pre.tC lm ≤ b1 + cst) (hcb : cst ≤ b)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 mkE) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 0x8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0) (hdf : T.df = false)
    (hm : T.mem = M) (h0 : T.regs 0 = BitVec.ofNat 64 7233184) (h3 : T.regs 3 = BitVec.ofNat 64 n)
    (h1 : T.regs 1 = BitVec.ofNat 64 (n + 4)) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) T (FQ R b L K zp zc st Z cst s) := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hlm := hP.2.2.2.2.2.1
  have hW128 : W lm ≤ 128 := by simp only [W]; omega
  have hlpos : 0 < lvlL (stLen s.mem st) lm := by have := hP.2.2.2.2.1; simp only [lvlL, lvlZ, lvlR, W]; omega
  have haW : allocCost (8 * (n + 4)) ≤ P2Pre.tC lm := by
    have e : P2Pre.tC lm = makeCost (W lm + 4) := rfl
    rw [e]; simp only [makeCost, makeCap, allocCost]; split <;> omega
  have hr8 : blockSize (8 * (n + 4)) true ≤ allocCost (8 * (n + 4)) := blockSize_le_allocCost _ _
  have hcost : blockSize (8 * (n + 4)) true ≤ b1 := by omega
  refine mkCall hmk hP hB.wc (n := n) (c := n + 4) (by omega) (by omega) (by omega) hcost T hpc hsp h14 hm
    (by rw [rra]; decide) h0 h3 h1 (fun ptr junk f x yh m zh kr hA => ?_)
  have hzW := scr_win hP hB.tz.zscr
  unfold Apart at hzW
  have hB2 := hB.alloc hP hA
  have hub := ub_fresh hP hB.wc hlpos hA hB.tz (c := n + 4) (by omega) hA.sz (by omega)
  have hsrc2 : natVal m zzp n = Z := by
    show m.readLE zzp (8 * n) = Z
    rw [hA.rdH _ _ (hB.tz.zscr.held.sub (Nat.le_refl _) (by omega)) (by unfold Apart; omega)]; exact hsrc
  have qk : ∀ a, sp + 24 ≤ a → a + 8 ≤ sp + 0x358 → m.readLE a 8 = M.readLE a 8 := fun a h1 h2 =>
    hA.keep a 8 (Or.inr ⟨h1, h2⟩)
  have q118 : m.readLE (sp + 0x120) 8 = zzp := by rw [qk _ (by omega) (by omega)]; exact r118
  have q68 : m.readLE (sp + 0x68) 8 = n := by rw [qk _ (by omega) (by omega)]; exact r68
  have q58 : m.readLE (sp + 0x58) 8 = n + 4 := by rw [qk _ (by omega) (by omega)]; exact r58
  have q118' : m.readLE (sp - 0x8 + 296) 8 = zzp := by rw [show sp - 0x8 + 296 = sp + 0x120 by omega]; exact q118
  have q68' : m.readLE (sp - 0x8 + 112) 8 = n := by rw [show sp - 0x8 + 112 = sp + 0x68 by omega]; exact q68
  have q58' : m.readLE (sp - 0x8 + 96) 8 = n + 4 := by rw [show sp - 0x8 + 96 = sp + 0x58 by omega]; exact q58
  have hwacc3 : m.accessible (sp - 0x8 - K) (K + 0x360) true = true := by
    rw [hA.macc]; exact (hB.wc.cenv hP).2.2.2.1
  have hwaccF3 : m.accessible (sp - 0x8 - K) (K + 0x360) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc3
  have hsz := hA.sz
  have hpl := ptr.isLt
  have hsp8 : T.regs 4 + 8#64 = BitVec.ofNat 64 sp := by
    rw [hsp]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hBH : HdM (BF R L K g sp st bp r zp zc xp xl xc yp yl lm s m (L1 ++ [(ptr.toNat, ptr.toNat +
    blockSize (8 * (n + 4)) true)]) (b1 - blockSize (8 * (n + 4)) true) zzp tp) := ⟨hB2⟩
  have hubH : HdM (UB R L K g sp st zp zc m (L1 ++ [(ptr.toNat, ptr.toNat + blockSize (8 * (n + 4)) true)]) zzp tp
    lm ptr.toNat (n + 4)) := ⟨hub⟩
  clear hB2 hub hA qk hB
  subst hm
  refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 XJ) ?_
  janus64_run [q118, q68, q58, hwacc3, hwaccF3, rra] until [XJ]
  refine xJ hap hmv hP hBH.h.wc hBH.h.esl hBH.h.tz hubH.h (by omega) hn1 (by omega) hsrc2 (by omega) _ ?_ ?_ ?_ ?_ ?_
    ?_ rfl ?_ ?_ ?_ ?_ ?_
  all_goals first | exact hfs | (janus64_simp [q118', q68', q58', hsp8]; done) |
    (simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hsp8)

end

end FvModexp.Amd64.P2W4
