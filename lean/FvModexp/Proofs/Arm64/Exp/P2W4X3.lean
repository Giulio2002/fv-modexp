import FvModexp.Proofs.Arm64.Exp.P2W4X2
import FvModexp.Proofs.Arm64.Exp.P2W4R1b

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the exit's `make` allocations (agent infra)

`z.set(zz)` with `cap z < n` (nat.go:58-68): `n = 1` → `makeslice(Word, 1, 1)` (return `0x1b622c`), else
`makeslice(Word, n, n + 4)` (`96 := n + 4`, return `0x1b6254`); the fresh array is a U-class buffer, then the
join `xJ`. `BF.alloc`: the body context through a live allocation.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

open FvModexp.Arm64.ExpHyp

section
variable {impl : List Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat}
    {s : State} {ret : Nat}

set_option maxRecDepth 20000 in
/-- `BF` through a live allocation -/
theorem BF.alloc (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp bp : Nat} (h : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {m : Memory} {p r n : Nat}
    (hA : AllocR R L K g sp st zp zc s.mem M L1 b1 (lvlL (stLen s.mem st) lm) m p r n) :
    BF R L K g sp st zp zc xp xl xc yp yl lm ret s m (L1 ++ [(p, p + r)]) (b1 - r) zzp bp := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 848) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hbW := scr_win hP h.tz.bscr
  unfold Apart at hbW
  have hsok := h.wc.sok
  obtain ⟨e0, e1, e2⟩ := hdr3 (M := M) (M' := m) (st := st) fun j hj =>
    hA.rdH _ _ (hsok.2.1.sub (by omega) (by omega)) (by unfold Apart; omega)
  have hx : LiveExt R L1 (L1 ++ [(p, p + r)]) :=
    LiveExt.single (by rw [show p + r - p = r by omega]; exact hA.rin)
      (by rw [show p + r - p = r by omega]; exact hA.rap)
  refine ⟨hA.wc, ESl.keep h.esl (fun a k ha => hA.keep a k (by omega)) (by omega),
    h.tz.keep hA.macc hx e0 e1 e2 fun a k ha => ?_⟩
  rcases ha with ha | ha
  · exact hA.keep a k (by omega)
  · exact hA.rdH a k (h.tz.bscr.held.sub ha.1 ha.2) (by unfold Apart; omega)

set_option maxRecDepth 20000 in
/-- after an exit allocation: the context, the fresh U buffer, the source and the window slots -/
theorem xAft (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp bp : Nat} (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {m : Memory} {p c : Nat}
    (hA : AllocR R L K g sp st zp zc s.mem M L1 b1 (lvlL (stLen s.mem st) lm) m p (blockSize (8 * c) true) (8 * c))
    (hc0 : 0 < c) (hc40 : c < 2 ^ 40) {n Z : Nat} (hsrc : NV M zzp n (2 * W lm) Z) :
    BF R L K g sp st zp zc xp xl xc yp yl lm ret s m (L1 ++ [(p, p + blockSize (8 * c) true)])
      (b1 - blockSize (8 * c) true) zzp bp ∧
    UB R L K g sp st zp zc m (L1 ++ [(p, p + blockSize (8 * c) true)]) zzp bp lm p c ∧
    NV m zzp n (2 * W lm) Z ∧
    (∀ a k, sp + 32 ≤ a → a + k ≤ sp + 848 → m.readLE a k = M.readLE a k) := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hlpos : 0 < lvlL (stLen s.mem st) lm := by have := hP.2.2.2.2.2.1; simp only [lvlL, lvlZ, lvlR, W]; omega
  have hzW := scr_win hP hB.tz.zscr
  unfold Apart at hzW
  refine ⟨hB.alloc hP hA, ub_fresh hP hB.wc hlpos hA hB.tz hc0 hA.sz hc40, NV.keep hsrc fun a k h1 h2 =>
    hA.rdH a k (hB.tz.zscr.held.sub h1 h2) (by unfold Apart; omega), fun a k h1 h2 => hA.keep a k (Or.inr ⟨h1, h2⟩)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`make(nat, 1)`** at the exit (from the `makeslice` call) -/
theorem xA1 (hap : ImplApart Extracted.program impl) (hmv : MemmoveLive (LibW.program.link impl) P2Pre.mvE 4096 R)
    (hmk : MakesliceLiveContract (LibW.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)} {b1 zzp bp : Nat}
    (hB : BF R L K g sp st zp zc xp xl xc yp yl lm (s.regs 30).toNat s M L1 b1 zzp bp)
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48) {Z cst : Nat}
    (hsrc : NV M zzp 1 (2 * W lm) Z) (r112 : M.readLE (sp + 112) 8 = 1) (r280 : M.readLE (sp + 280) 8 = zzp)
    (hbud : b + P2Pre.tC lm ≤ b1 + cst) (hcb : cst ≤ b)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 mkE) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h18 : T.regs 18 = s.regs 18) (hm : T.mem = M)
    (h0 : T.regs 0 = 2641088#64) (h1 : T.regs 1 = BitVec.ofNat 64 1) (h2 : T.regs 2 = BitVec.ofNat 64 1)
    (h30 : T.regs 30 = BitVec.ofNat 64 1794604) :
    ReachesRet (LibW.program.link impl) (s.regs 30) T (FQ R b L K zp zc st Z cst s) := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have ha8 : allocCost 8 ≤ P2Pre.tC lm := by simp only [P2Pre.tC, makeCost, makeCap, allocCost]; split <;> omega
  have hr8 : blockSize (8 * 1) true ≤ allocCost 8 := blockSize_le_allocCost _ _
  have hcost : blockSize (8 * 1) true ≤ b1 := by omega
  refine mkCall mkE_eq hmk _ _ hP hB.wc (n := 1) (c := 1) (ra := 1794604) (by decide) (by decide) (by decide)
    (by decide) (by decide) hcost T hpc hsp h28 hm h0 h1 h2 h30 (fun ptr junk f v m ex ep hA => ?_)
  obtain ⟨hB2, hub, hsrc2, kW⟩ := xAft hP hB hA (by decide) (by decide) hsrc
  have q112 : m.readLE (sp + 112) 8 = 1 := by rw [kW _ _ (by omega) (by omega)]; exact r112
  have q280 : m.readLE (sp + 280) 8 = zzp := by rw [kW _ _ (by omega) (by omega)]; exact r280
  have hmacc : m.accessible (sp - K) (K + 848) true = true := by
    rw [hB2.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hz48 := hB.tz.zscr.b48
  have hp48 := (hub.live (by decide)).2.2.2
  clear hB kW hA
  janus_run [q112, q280, hmacc] until [xJE]
  refine xJ hap hmv hP hB2.wc hB2.esl hr4 hr48 hB2.tz hub (Nat.le_refl 1) (by decide) hsrc2 (by omega) _ ?_ ?_ ?_ ?_
    rfl ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`make(nat, n, n + 4)`** at the exit (from the `makeslice` call; `96 = n + 4` already stored) -/
theorem xA2 (hap : ImplApart Extracted.program impl) (hmv : MemmoveLive (LibW.program.link impl) P2Pre.mvE 4096 R)
    (hmk : MakesliceLiveContract (LibW.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)} {b1 zzp bp : Nat}
    (hB : BF R L K g sp st zp zc xp xl xc yp yl lm (s.regs 30).toNat s M L1 b1 zzp bp)
    (hr4 : (s.regs 30).toNat % 4 = 0) (hr48 : (s.regs 30).toNat < 2 ^ 48) {n Z cst : Nat} (hn1 : 0 < n)
    (hnW : n ≤ W lm)
    (hsrc : NV M zzp n (2 * W lm) Z) (r112 : M.readLE (sp + 112) 8 = n) (r280 : M.readLE (sp + 280) 8 = zzp)
    (r96 : M.readLE (sp + 96) 8 = n + 4) (hbud : b + P2Pre.tC lm ≤ b1 + cst) (hcb : cst ≤ b)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 mkE) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h18 : T.regs 18 = s.regs 18) (hm : T.mem = M)
    (h0 : T.regs 0 = 2641088#64) (h1 : T.regs 1 = BitVec.ofNat 64 n) (h2 : T.regs 2 = BitVec.ofNat 64 (n + 4))
    (h30 : T.regs 30 = BitVec.ofNat 64 1794644) :
    ReachesRet (LibW.program.link impl) (s.regs 30) T (FQ R b L K zp zc st Z cst s) := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.1
  have hW128 : W lm ≤ 128 := by simp only [W]; omega
  have hW' : P2Pre.W lm = W lm := rfl
  have haW : allocCost (8 * (n + 4)) ≤ P2Pre.tC lm := by
    simp only [P2Pre.tC, makeCost, makeCap, allocCost]; split <;> omega
  have hr8 : blockSize (8 * (n + 4)) true ≤ allocCost (8 * (n + 4)) := blockSize_le_allocCost _ _
  have hcost : blockSize (8 * (n + 4)) true ≤ b1 := by omega
  refine mkCall mkE_eq hmk _ _ hP hB.wc (n := n) (c := n + 4) (ra := 1794644) (by omega) (by omega) (by omega)
    (by decide) (by decide) hcost T hpc hsp h28 hm h0 h1 h2 h30 (fun ptr junk f v m ex ep hA => ?_)
  obtain ⟨hB2, hub, hsrc2, kW⟩ := xAft hP hB hA (by omega) (by omega) hsrc
  have q112 : m.readLE (sp + 112) 8 = n := by rw [kW _ _ (by omega) (by omega)]; exact r112
  have q280 : m.readLE (sp + 280) 8 = zzp := by rw [kW _ _ (by omega) (by omega)]; exact r280
  have q96 : m.readLE (sp + 96) 8 = n + 4 := by rw [kW _ _ (by omega) (by omega)]; exact r96
  have hmacc : m.accessible (sp - K) (K + 848) true = true := by
    rw [hB2.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hz48 := hB.tz.zscr.b48
  have hp48 := (hub.live (by omega)).2.2.2
  clear hB kW hA
  janus_run [q112, q280, q96, hmacc] until [xJE]
  refine xJ hap hmv hP hB2.wc hB2.esl hr4 hr48 hB2.tz hub (by omega) hn1 hsrc2 (by omega) _ ?_ ?_ ?_ ?_
    rfl ?_ ?_ ?_ ?_ ?_
  all_goals (janus_simp <;> omega)

end

end FvModexp.Arm64.P2W4
