import FvModexp.Proofs.Amd64.Exp.P2DTzE
import FvModexp.Proofs.Amd64.Exp.P2DZero
import FvModexp.Proofs.Amd64.Exp.LibCallsQ

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): `xOdd := nat(nil).rsh(x, i)` (nat.go:952; agent asm s69; twin of infra's arm64
`P2DRsh`)

`cenvD`: the caller environment one frame down (callee `RSP = RSP_entry - 0x78`, window `[RSP - stk, RSP + A)`).
`rshCall`: from the `rsh` entry reached by `tzE` (memory `M1 = W1 (W0 …)`, `RAX/RBX/RCX = 0`, `RDI/RSI/R8 = x`,
`R9 = tz`, `[RSP] = rshR`) through `Rsh.Hyp` (`LibCalls.hypSumW`) to `rshR`, handing the callee's `RshPost`
(`z = nil`) to the continuation.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

theorem w1_frame (M : Memory) {sp st lm zc zl zp lo : Nat} (h8 : 8 ≤ sp) :
    MemFrame M (W1 M sp st lm zc zl zp lo) [(sp - 8, sp + 0x68), (sp + 0x98, sp + 0xd0)] := by
  simp only [W1]
  refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x68)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x68)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 0x68)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 0x98, sp + 0xd0)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 0x98, sp + 0xd0)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 0x98, sp + 0xd0)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 0x98, sp + 0xd0)) (by simp) (by simp only; omega) (by simp only; omega)
  exact MemFrame.refl _ _

theorem w1_ra {M : Memory} {sp st lm zc zl zp lo : Nat} : (W1 M sp st lm zc zl zp lo).readLE (sp - 8) 8 = rshR := by
  simp only [W1, Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by decide)

/-- the memory at the `rsh` call -/
@[reducible] def M1 (s : State) (zp zl zc st lm xp lo : Nat) : Memory :=
  W1 (W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp) ((s.regs 4).toNat - 0x70) st lm zc zl zp lo

theorem m1_frame (s : State) {stk A zp zl zc st lm xp lo : Nat} (hk : 0x78 ≤ stk) (hs : stk ≤ (s.regs 4).toNat)
    (hA : 96 ≤ A) : MemFrame s.mem (M1 s zp zl zc st lm xp lo) (ownW s stk A) :=
  (w0_frame s.mem _ _ _ _).trans (w1_frame _ (by omega)) fun a k ho => by
    simp only [ownW, outside_cons, outside_nil, and_true] at ho ⊢
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> omega

theorem m1_regions (s : State) (zp zl zc st lm xp lo : Nat) :
    (M1 s zp zl zc st lm xp lo).regions = s.mem.regions := by
  simp only [M1, W1, W0, Janus.Arm64.Memory.regions_writeLE]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the caller environment one frame down** -/
theorem cenvD (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {M : Memory}
    (hF : MemFrame s.mem M (R.rt ++ ownW s stk A)) (hrg : M.regions = s.mem.regions)
    {L1 : List (Nat × Nat)} (hx : LiveExt R L L1) (hk : 0x78 ≤ stk) :
    CallW.CEnv R L1 (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 0x78) (stk - 0x78) (0x78 + A) M := by
  have ce0 := cenv_ent hP.1
  generalize hSP : (s.regs 4).toNat = SP at *
  obtain ⟨hal, hK0, hA0, hacc, -, -, -, hrt, hga, hgrt, -, -, -, -, -, -, -, f5, f6⟩ := id ce0
  have hws : ∀ r ∈ ownW s stk A, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr _
    simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;>
      exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have ce1 := CallW.CEnv.frame ce0 hF hrg hws
    (by unfold Apart at hga; simp only [ownW, hSP, outside_cons, outside_nil, and_true]; omega)
    (by unfold Apart at f6; simp only [ownW, hSP, outside_cons, outside_nil, and_true]; omega)
  exact cenv_ext (cenv_rebase ce1 (x' := SP - 0x78) (K' := stk - 0x78) (A' := 0x78 + A) (by omega)
    (by omega) (by omega) (by omega)) hx

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat}
  {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the `rsh` call** -/
theorem rshCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains NHyp.fnP2 = false)
    {stkR aboveR : Nat} (hrh : Rsh.Hyp impl R ns stkR aboveR) (hkR : stkR + 0x78 ≤ stk) (haR : aboveR ≤ 0x60)
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 96 ≤ A)
    (hxc : xl ≤ xc) (hxc' : xc < 2 ^ 40) {tz lo : Nat} (htz : tz < 2 ^ 64)
    (hbud : makeCost (Rsh.need xl tz) ≤ cst) (hx15 : s.xmm 15 = 0) (hdf : s.df = false) {Q : State → Prop}
    (S : State) (hpc : S.rip = BitVec.ofNat 64 rshE) (hsp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x78))
    (r0 : S.regs 0 = 0#64) (r3 : S.regs 3 = 0#64) (r1 : S.regs 1 = 0#64) (r7 : S.regs 7 = BitVec.ofNat 64 xp)
    (r6 : S.regs 6 = BitVec.ofNat 64 xl) (r8 : S.regs 8 = BitVec.ofNat 64 xc) (r9 : S.regs 9 = BitVec.ofNat 64 tz)
    (r14 : S.regs 14 = s.regs 14) (rfs : S.fsBase = s.fsBase) (rx : S.xmm 15 = s.xmm 15) (rdf : S.df = s.df)
    (hm : S.mem = M1 s zp zl zc st lm xp lo)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 rshR → S'.regs 4 = S.regs 4 + 8 → S'.regs 14 = S.regs 14 →
      S'.xmm 15 = S.xmm 15 → S'.mem.regions = S.mem.regions →
      Rsh.RshPost R b L stkR aboveR 0 0 xp xl tz S S' → ReachesRet (LibW.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S Q := by
  have hC := hP.1
  have hC' := hC
  obtain ⟨⟨-, ⟨hle, -, -⟩, -, -, hwrt, -, -, hLs, -⟩, hsv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hinv⟩ := hC'
  simp only [regSP] at hle
  have hX := hP.2.1
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  have hF0 : MemFrame s.mem S.mem (ownW s stk A) := by rw [hm]; exact m1_frame s (by omega) hle hA
  have hF0' : MemFrame s.mem S.mem (R.rt ++ ownW s stk A) := hF0.mono fun a k ho => by
    rw [outside_append] at ho; exact ho.2
  have hLs' : LiveSep L (ownW s stk A) := fun r hr => by
    have := hLs r hr; simp only [win, ownW, outside_cons, outside_nil, and_true] at this ⊢; omega
  have hLF0 : LiveFrame s.mem S.mem L [] := LiveFrame.of_win hF0 hLs'
  have hrg : S.mem.regions = s.mem.regions := by rw [hm]; exact m1_regions s _ _ _ _ _ _ _
  have hwin : Outside ((s.regs 4).toNat - stk) (stk + A) R.rt := hwrt
  have hinv1 : R.inv b L (s.regs 14).toNat (view R.rt L S.mem) := by
    refine Expmc.inv_frame hF0 (fun r hr => Or.inr ?_) hinv
    simp only [ownW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact hwin.of_sub (by omega) (by omega)
  have hSsp : (S.regs 4).toNat + 0x78 = (s.regs 4).toNat := by rw [hsp, BitVec.toNat_ofNat]; omega
  obtain ⟨hxR, hxn, hxN, -⟩ := in_sub hC (p := xp) (n := xl) (by simp) hF0' hLF0 (LiveExt.refl R L) hSsp
    (stk' := stkR) (A' := aboveR) (by omega) (by omega)
  have hS := LibCalls.hypSumW hap hns
    (by simp only [numIntRegs, List.length_cons, List.length_nil]; decide) (hrh b L 0#64 0#64 0#64 (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
    (BitVec.ofNat 64 xc) (BitVec.ofNat 64 tz))
  rw [rsh_a] at hS
  have tx := LibCalls.tN (show xp < 2 ^ 64 by have := hxR.2.2.1; omega)
  have tl := LibCalls.tN (show xl < 2 ^ 64 by omega)
  have tc := LibCalls.tN (show xc < 2 ^ 64 by omega)
  have tt := LibCalls.tN htz
  simp only [BitVec.toNat_zero, tx, tl, tc, tt] at hS
  have tsp : (S.regs 4).toNat = (s.regs 4).toNat - 0x78 := by omega
  have hra : S.mem.readLE (S.regs 4).toNat 8 = rshR := by
    rw [tsp, hm, show (s.regs 4).toNat - 0x78 = (s.regs 4).toNat - 0x70 - 8 by omega]; exact w1_ra
  refine ReachesRet.call_regions hS hpc ⟨?_, rx.trans hx15, ?_, rdf.trans hdf, ?_⟩ fun s' hr hq hrg' => ?_
  · rw [hra]; exact ra_p2 hap hnf 0x217 (by decide)
  · simp only [ArgsFrom64, argReg, intArgRegs]; exact ⟨r0, r3, r1, r7, r6, r8, r9, trivial⟩
  · refine ⟨⟨CallW.callEnv_of (cenvD hC hF0' hrg (LiveExt.refl R L) (by omega)) tsp (by rw [r14]) (by rw [rfs]) rfl
      (by omega) (by omega) (by omega), hsv, Nat.le_refl _, ⟨by decide, by simp, fun h => absurd h (by omega)⟩, hxR,
      by omega, fun h => absurd h (by omega), hxN, hxl0, Or.inr rfl, by omega, by rw [r14]; exact hinv1⟩, hxc, hxc'⟩
  · obtain ⟨⟨e4, -, e14, ex⟩, hq⟩ := hq
    exact K s' (by rw [hr]; simp only [retAddrOf, hra]) e4 e14 ex hrg' hq

end

end FvModexp.Amd64.P2D
