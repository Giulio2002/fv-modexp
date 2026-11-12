import FvModexp.Proofs.Arm64.Nat.DrsBd
import FvModexp.Proofs.Common.MaskWord

/-!
# `divRecursiveStep` (arm64), loop body segment 1: `uu := u[j-B:]`, `clear(qhat)` (natdiv.go:803-812)

`b1`: from the loop head `H` with `B < j` → `j-B`, `uu` (ptr/len/cap) spilled → `CALL runtime.memclrNoHeapPointers`
(`qhat0`, `8·(B+1)` bytes) → its return `0x1ba558` (`A1`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- the own stores of segment 1: the iteration slots -/
@[reducible] def is4 (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 288, s.sp.toNat - 272), (s.sp.toNat - 104, s.sp.toNat - 96), (s.sp.toNat - 88, s.sp.toNat - 80)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- the `clear(qhat)` call of segment 1, from the call state `X` -/
theorem b1c (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (hH : H R c s Lk bk S j)
    (hj : c.vl / 2 < j) (Q : State → Prop)
    (k : ∀ S', A1 R c s Lk bk S' j (Asm.limbs S.mem c.qp c.ql) (Asm.limbs S.mem c.up c.u1) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (cA "runtime.memclrNoHeapPointers")) (hsp : X.sp = s.sp - 400#64)
    (h0 : X.regs 0 = BitVec.ofNat 64 c.t0) (h1 : X.regs 1 = BitVec.ofNat 64 (8 * (c.vl / 2 + 1)))
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 r1) (hF4 : MemFrame S.mem X.mem (is4 s)) (hreg : X.mem.regions = S.mem.regions)
    (e1 : X.mem.readLE (s.sp.toNat - 104) 8 = j - c.vl / 2)
    (e2 : X.mem.readLE (s.sp.toNat - 88) 8 = c.up + 8 * (j - c.vl / 2))
    (e3 : X.mem.readLE (s.sp.toNat - 288) 8 = c.u1 - (j - c.vl / 2))
    (e4 : X.mem.readLE (s.sp.toNat - 280) 8 = c.uc - (j - c.vl / 2)) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  have hcr := hH.cr
  have hev := hH.ev
  obtain ⟨hce, hsv, -, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, -, huh, huw, -⟩, ⟨-, -, hvh, hvw, -, -, -⟩, -⟩ :=
    hcr.pre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, hga, hgr, -, -⟩ := hce'
  have hWg := drsW_ge c.vl
  have hW := hcr.hW; have h40 := hcr.h40; have hu1 := hcr.u1ul
  have hqh := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hqw := hcr.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hx : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hF : MemFrame S.mem X.mem (fw s) := hF4.mono fun x n ho => by
    simp only [fw, winA, is4, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hEvX : Ev R c s Lk bk X.mem := Ev.own hcr hev hF hreg
  have hFpX : Fp R c s Lk X.mem (c.l1 s) := Fp.own hcr hH.fp hF
  have rd4 : ∀ x n, Outside x n (win s c.W 96) → X.mem.readLE x n = S.mem.readLE x n := fun x n ho =>
    hF4.readLE _ _ (by simp only [win, is4, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hsl : Sl c s X.mem := hH.sl.frame hF4 (by simp only [FixOut, is4, outside_cons, outside_nil, and_true]; omega)
  have hBdX : Bd c s X.mem j (Asm.limbs S.mem c.qp c.ql) :=
    ⟨hsl, e1, e2, e3, e4, by rw [rd4 _ _ hvw]; exact hH.vk,
      by rw [rd4 _ _ (huw.of_sub (by omega) (by omega))]; exact hH.utl, limbs_congr (rd4 _ _ hqw)⟩
  have ht0w := hcr.t0w
  have hdw : c.t0 + 8 * (c.vl / 2 + 1) ≤ s.sp.toNat - c.W ∨ s.sp.toNat + 96 ≤ c.t0 := by
    simp only [win, outside_cons, outside_nil, and_true] at ht0w; omega
  have hn8 : 8 * (c.vl / 2 + 1) < 2 ^ 64 := by omega
  refine ReachesRet.call_regions (hmc Lk bk) (by rw [hpc]) (mc_pre (dst := c.t0) (n := 8 * (c.vl / 2 + 1)) hce
    (by omega) hx X hsp h28 (hEvX.grd hcr) (fun a n w => hEvX.fr.accessible a n w) (by rw [h30]; decide)
    (by rw [h30]; decide) hEvX.inv (by rw [h0, BitVec.toNat_ofNat]; have := hcr.t048; omega)
    (by rw [h1, BitVec.toNat_ofNat]; omega) (hsv.2.2.1 _ _ (by omega)) (by have := hcr.t048; omega)
    (by rw [hEvX.fr.accessible]; exact hcr.t0acc) (hev.ext.held hcr.t0h) hdw) ?_
  intro T hT ⟨junk, f, v, m, ex, ep, hs, hMF, hLF, hinv', hzr⟩ hrg
  subst hs
  have e0 : (X.regs 0).toNat = c.t0 := by rw [h0, BitVec.toNat_ofNat]; have := hcr.t048; omega
  have e1' : (X.regs 1).toNat = 8 * (c.vl / 2 + 1) := by rw [h1, BitVec.toNat_ofNat]; omega
  rw [e0, e1'] at hMF hLF hzr
  rw [show calleeStack X 4096 2 = winA X 4096 24 by simp only [calleeStack, winA]] at hMF
  have hS : ∀ x n, Outside x n (winA s c.W 96) → Outside x n (winA X 4096 24) := fun x n ho => by
    simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; rw [hspn]; omega
  have hloc := (show Loc R c s c.t0 (8 * (c.vl / 2 + 1)) from hcr.t0loc).out
  have hst : Outside c.st 24 [(c.t0, c.t0 + 8 * (c.vl / 2 + 1))] := by
    have := hcr.t0st; unfold Apart at this; simp only [outside_cons, outside_nil, and_true]; omega
  rw [h28] at hinv'
  have hreg' : m.regions = X.mem.regions := by rw [← hrg]; rfl
  have hEvT : Ev R c s Lk bk m := Ev.callN hcr hEvX hMF hLF hS hloc.1 hloc.2 hst hinv' hreg'
  obtain ⟨eW, eL, eC⟩ := hdr_keep hcr hEvX hMF hLF hS hst
  have kp : ∀ x n, Held R Lk x n → Outside x n (win s c.W 96) → Apart x n c.t0 (8 * (c.vl / 2 + 1)) →
      m.readLE x n = S.mem.readLE x n := by
    intro x n hh hw' hap
    rw [Held.readLE2 hh hMF hLF (hS _ _ (by simp only [win, winA, outside_cons, outside_nil, and_true] at hw' ⊢; omega))
      (by unfold Apart at hap; simp only [outside_cons, outside_nil, and_true]; omega)]
    exact rd4 x n hw'
  have t0q := hcr.t0q; have t0u := hcr.t0u; have t0v := hcr.t0v
  unfold Apart at t0q t0u t0v
  have kv := kp _ _ (hx.held hvh) hvw (by unfold Apart; omega)
  have ku : m.readLE c.up (8 * c.u1) = S.mem.readLE c.up (8 * c.u1) := kp _ _ (hx.held (huh.sub (Nat.le_refl _) (by omega))) (huw.of_sub (by omega) (by omega))
    (by unfold Apart; omega)
  have kt : m.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = S.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) :=
    kp _ _ (hx.held (huh.sub (by omega) (by omega))) (huw.of_sub (by omega) (by omega))
    (by unfold Apart; omega)
  have kq := kp _ _ (hx.held hqh) hqw (by unfold Apart; omega)
  have hBdT : Bd c s m j (Asm.limbs S.mem c.qp c.ql) := by
    refine hBdX.frame hMF ?_ ?_ (kv.trans (rd4 _ _ hvw).symm) (kt.trans (rd4 _ _ (huw.of_sub (by omega) (by omega))).symm)
      (kq.trans (rd4 _ _ hqw).symm)
    · refine fixOut_callee hout (by omega) (by omega) hspn (by omega) ?_
      simp only [FixOut, win, outside_cons, outside_nil, and_true] at ht0w ⊢; omega
    · refine iOut_callee hout (by omega) (by omega) hspn (by omega) ?_
      simp only [IOut, win, outside_cons, outside_nil, and_true] at ht0w ⊢; omega
  refine k _ ⟨?_, ?_, ?_, ?_, ?_, hcr, hEvT, Fp.hdr hFpX eW eL eC, hBdT, hj, hH.li, limbs_congr ku,
    FvModexp.Expmc.readLE_zeroed hzr, hH.bud⟩
  · rw [hT]; simp only [h30]
  · exact hsp
  · simp only [retStateX, callRegs, h28]; simp
  · simp only [retStateX, callRegs, h29]; simp
  · simp only [retStateX, callRegs, h18]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem b1 (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibDrs.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (hH : H R c s Lk bk S j)
    (hj : c.vl / 2 < j) (Q : State → Prop)
    (k : ∀ S', A1 R c s Lk bk S' j (Asm.limbs S.mem c.qp c.ql) (Asm.limbs S.mem c.up c.u1) →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) S Q := by
  have hcr := hH.cr
  have hpre := hcr.pre
  obtain ⟨hce, hsv, -, -, -, huc, huc4, -, -, -, ⟨hvl9, -⟩, -, -, -, -, ⟨-, hu48, -, -, -⟩, -⟩ := hpre
  obtain ⟨-, ⟨hal, hb', ha48, hw⟩, -, hout, -, -, -, -⟩ := hce
  have hWg := drsW_ge c.vl
  have hW := hcr.hW
  have hu1 := hcr.u1ul; have hvu := hcr.vu1; have h40 := hcr.h40
  have hjm : j ≤ c.u1 - c.vl := by
    have := hH.li.2.2.2.2.2.2.2; omega
  have hsl := hH.sl
  have hpc := hH.pc; have hsp := hH.sp; have h3 := hH.r3; have h0 := hH.r0; have h1 := hH.r1
  have h28 := hH.r28; have h29 := hH.r29; have h18 := hH.r18
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hspn : (s.sp - 400#64).toNat = s.sp.toNat - 400 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have rn := hsl.nn; have ru := hsl.ul'; have ruc := hsl.s7; have rup := hsl.s5
  have hl3 := lsl3_ofNat (c.vl / 2 + 1) (by omega)
  have hne : (BitVec.ofNat 64 (c.vl / 2 + 1) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hm1 := FvModexp.mask_sub_lt (j - c.vl / 2) c.uc (by omega) (by omega)
  have hm2 := FvModexp.asr63_mask (j - c.vl / 2) c.uc (j - c.vl / 2) (by omega) (by omega) (by omega)
  have haccS : S.mem.accessible (s.sp.toNat - 408) 504 true = true := by
    rw [hH.ev.fr.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  have hB := lsr1 c.vl (by omega)
  have hBn : (BitVec.ofNat 64 c.vl >>> 1).toNat = c.vl / 2 := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hBi : (BitVec.ofNat 64 c.vl >>> 1).toInt = ((c.vl / 2 : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_of_msb (by rw [BitVec.msb_eq_decide]; simp only [hBn, decide_eq_false_iff_not]; omega), hBn]
  have hneg : (BitVec.ofNat 64 j - BitVec.ofNat 64 (c.vl / 2)).getLsbD 63 = false := by
    rw [← BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_decide]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  have hnz : (BitVec.ofNat 64 j - BitVec.ofNat 64 (c.vl / 2) = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
  have hjB : BitVec.ofNat 64 j - BitVec.ofNat 64 (c.vl / 2) = BitVec.ofNat 64 (j - c.vl / 2) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hB' : BitVec.ofNat 64 c.vl >>> 1 = BitVec.ofNat 64 (c.vl / 2) := by rw [← klsr1]; exact hB
  have hmd : (j - c.vl / 2) % 18446744073709551616 = j - c.vl / 2 := Nat.mod_eq_of_lt (by omega)
  have hBl : c.vl / 2 < 2 ^ 64 := by omega
  janus_run [rn, ru, ruc, rup, hl3, hne, hm1, hm2, hB', hjB, hmd, hneg, hnz] until [cA "runtime.memclrNoHeapPointers"]
  refine b1c impl R hmc c s Lk bk S j hH hj Q k _ rfl rfl ?_ ?_ ?_ ?_ ?_ rfl (by unfold is4; janus_frame) (by simp) ?_ ?_ ?_ ?_
  all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
  · exact h0
  · exact h28
  · exact h29
  · exact h18
  all_goals (try dsimp only)
  all_goals (repeat (first | rw [Memory.readLE_writeLE_self] | rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]))
  all_goals omega

end FvModexp.Arm64.DivRec
