import FvModexp.Proofs.Amd64.NatQ.KSqrB
import FvModexp.Proofs.Amd64.Nat.StackNatX

/-!
# [amd64 port (divmc s39) of the Q-form Arm64/NatQ/KSqrProD.lean — TIGHT COSTS] `karatsubaSqr` (amd64): the `z1 := stk.nat(2·n2 + 1)` call (natmul.go:291-292) → `KB1` (pure)

`KP … P`: the state at `(*stack).nat`'s entry (`CALL` at `0x5f2573`, return `0x5f2578` pushed at `SP - 320`): `KPre`
at the entry `s`, the normalised halves of `x` (as `KM`), the prologue's frame stores (saved `RBP`, spills, defer
record, the `x0`/`x1`/`z0`/`z2` headers, the push); the prologue wrote only `[SP - 320, SP)` and the spill area.
`ks_natcall`: the call (`StackNatX.sumQ` in `LibSqr`, pre `kNatPre`) and `KB1` from its postcondition (`kmOf`).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

abbrev stkNatA : Nat := 0x5e6480

theorem stkNat_entry : segAddr Extracted.program StackNat.fn = stkNatA := by decide

structure KP (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State)
    (lx0 lx1 : Nat) (P : State) : Prop where
  pre : KPre R b H L W st zp (2 * n) zc xp n xc s
  pc : P.rip = BitVec.ofNat 64 stkNatA
  sp : (P.regs 4).toNat = (s.regs 4).toNat - 320
  g : P.regs 14 = s.regs 14
  fpr : P.regs 5 = s.regs 4 - 8#64
  fs : P.fsBase = s.fsBase
  df : P.df = s.df
  x15 : P.xmm 15 = s.xmm 15
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 3 = BitVec.ofNat 64 (kT n)
  ra : P.mem.readLE ((s.regs 4).toNat - 320) 8 = 0x5f2578
  l0 : lx0 ≤ kn2 n
  v0 : natVal s.mem xp lx0 = natVal s.mem xp (kn2 n)
  nn0 : NatNorm s.mem xp lx0
  l1 : lx1 ≤ n - kn2 n
  v1 : natVal s.mem (xp + 8 * kn2 n) lx1 = natVal s.mem (xp + 8 * kn2 n) (n - kn2 n)
  nn1 : NatNorm s.mem (xp + 8 * kn2 n) lx1
  fr : MemFrame s.mem P.mem [((s.regs 4).toNat - 320, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 48)]
  reg : P.mem.regions = s.mem.regions
  fp : P.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  bit : P.mem.readLE ((s.regs 4).toNat - 249) 1 = 1
  n2s : P.mem.readLE ((s.regs 4).toNat - 248) 8 = kn2 n
  n1s : P.mem.readLE ((s.regs 4).toNat - 240) 8 = 8 * kn2 n
  dfn : P.mem.readLE ((s.regs 4).toNat - 168) 8 = kDfn
  dst : P.mem.readLE ((s.regs 4).toNat - 160) 8 = st
  dln : P.mem.readLE ((s.regs 4).toNat - 152) 8 = stLen s.mem st
  dpt : P.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 168
  s1 : P.mem.readLE ((s.regs 4).toNat + 8) 8 = st
  s2 : P.mem.readLE ((s.regs 4).toNat + 16) 8 = zp
  s3 : P.mem.readLE ((s.regs 4).toNat + 24) 8 = 2 * n
  s4 : P.mem.readLE ((s.regs 4).toNat + 32) 8 = zc
  s5 : P.mem.readLE ((s.regs 4).toNat + 40) 8 = xp
  x0h : IntAt P.mem ((s.regs 4).toNat - 48) 0 xp lx0 xc
  x1h : IntAt P.mem ((s.regs 4).toNat - 80) 0 (xp + 8 * kn2 n) lx1 (xc - kn2 n)
  z0h : Z0H s P.mem zp zc n
  z2h : Z2H s P.mem zp zc n

/-- the window facts of the entry (from `KPre`) -/
theorem KP.lay {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 : Nat} {P : State} (h : KP R b H L W st zp zc xp n xc s lx0 lx1 P) :
    4880 + 16 * n ≤ W ∧ W ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat + 48 ≤ 2 ^ 48 ∧ 80 ≤ n ∧
      n ≤ 2 ^ 12 ∧ n ≤ xc ∧ xc < 2 ^ 40 ∧ 2 * n ≤ zc ∧ zc < 2 ^ 40 ∧
      Outside ((s.regs 4).toNat - W) (W + 48) R.rt ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
      Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - W) (W + 48) := by
  obtain ⟨⟨-, ⟨hb, ha, -⟩, hal, -, hout, hga, hgr, -, -, -⟩, hW, -, -, -, h80, hxc, hxc40, hx12, -, -, -, -, -, hzl, hzc40, -⟩ := h.pre
  unfold ksqrW at hW
  exact ⟨by omega, hb, hal, ha, h80, hx12, hxc, hxc40, by omega, hzc40, hout, hgr, hga⟩

/-- reads outside the prologue's writes are unchanged since the entry -/
theorem KP.rd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 : Nat} {P : State} (h : KP R b H L W st zp zc xp n xc s lx0 lx1 P) {a k : Nat}
    (ha : a + k ≤ (s.regs 4).toNat - 320 ∨ (s.regs 4).toNat + 48 ≤ a ∨
      ((s.regs 4).toNat ≤ a ∧ a + k ≤ (s.regs 4).toNat + 8)) :
    P.mem.readLE a k = s.mem.readLE a k :=
  h.fr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`stk.nat(2·n2 + 1)`'s precondition** at its entry `P` -/
theorem kNatPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 : Nat} {P : State} (h : KP R b H L W st zp zc xp n xc s lx0 lx1 P) :
    StackNatX.PreQ R b L H 4192 24 st (kT n) P := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨-, -, hw⟩, -, hdl, -, -, -, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩, -, hsv, hglb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsp, -, hslen, ⟨hlenH, hcost⟩, -, hinv⟩ := h.pre
  obtain ⟨hst0, hsok, hstw, hstg, hsta, hfg, hfw, hsf, hswb, -, -, -, -, -, -⟩ := hsp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwbacc, -, -⟩ := hglb
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hw
  have hspP := h.sp
  have hacc : ∀ a k w, P.mem.accessible a k w = s.mem.accessible a k w := fun a k w => h.fr.accessible a k w
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw
  simp only [guard, BasicSqr.freeP, BasicSqr.freeN] at hstg hfg hfw hsf hsta
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hc40⟩ := hsok
  have eW : P.mem.readLE st 8 = s.mem.readLE st 8 := h.rd (by omega)
  have eL : P.mem.readLE (st + 8) 8 = s.mem.readLE (st + 8) 8 := h.rd (by omega)
  have eC : P.mem.readLE (st + 16) 8 = s.mem.readLE (st + 16) 8 := h.rd (by omega)
  have eG : P.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    unfold Apart at hga; exact h.rd (by omega)
  have eT : P.mem.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
    unfold Apart at htw; exact h.rd (by omega)
  have hdlP : Extracted.program.DataLoaded P.mem := by
    refine dataLoaded_frame64 hdl h.reg hro (h.fr.widen R.rt) fun r hr hlt => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
  simp only [stW, stLen, stCap] at hnl hlc hc40 hstw hfw hsf hsta hslen hlenH
  have hce : CallEnv R L P 4192 24 := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, hdlP, ?_, ?_, by rw [h.g]; exact hgr, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [stackguard0Offset, regG]; rw [h.g]; exact hg1
    · simp only [stackguard0Offset, regG]; rw [h.g, hacc]; exact hg2
    · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [h.g, eG, hspP]; omega
    · simp only [regSP]; omega
    · simp only [regSP]; omega
    · simp only [regSP]; rw [hacc, hspP]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    · omega
    · rw [hspP]; exact hout.of_sub (by omega) (by omega)
    · rw [hspP, h.g]; unfold Apart at hga ⊢; omega
    · intro r hr
      have := hLs r hr
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hspP]; omega
    · rw [h.fs]; exact htb
    · rw [h.fs, hacc]; exact htr
    · rw [h.fs, eT, htg, h.g]
    · rw [h.fs]; exact htrt
    · rw [h.fs, hspP]; unfold Apart at htw ⊢; omega
  unfold StackNatX.PreQ StkOK
  simp only [stW, stLen, stCap]
  rw [h.g, eW, eL, eC]
  refine ⟨hce,
    hsv, ⟨hst8, hsth, by rw [hacc]; exact hstacc, hst48, fun h0 => ?_, hlc, hc40⟩,
    by simp only [win, outside_cons, outside_nil, and_true, hspP]; omega,
    fun h0 => ⟨by simp only [win, outside_cons, outside_nil, and_true, hspP]; have := (hsta h0).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega,
      by unfold Apart at hsta ⊢; have := (hsta h0).2; omega⟩,
    by simp only [kT, kn2]; omega, by simp only [kT, kn2]; omega,
    ⟨by simp only [kT, kn2]; omega, by rw [stkR_congr (m := s.mem) (m' := P.mem) (by simp only [stCap]; exact eC)]; omega⟩, ?_, by rw [hacc]; exact hwbacc, hswb, hsf⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hnl h0; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  · refine RtInv.inv_frame' h.fr (fun r hr => ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> left <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)

end FvModexp.Amd64.Q.NatSqr
