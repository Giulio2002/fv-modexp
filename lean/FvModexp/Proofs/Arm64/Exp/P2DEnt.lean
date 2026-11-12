import FvModexp.Proofs.Arm64.Exp.P2DDefs

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): from the entry to the four branch points (agent infra)

`ent`: guard, prologue (frame 112), spills `z.ptr`/`x.ptr`/`y.ptr`, the `len y` / `y[0]` panics (excluded),
`logM = 1` → `oneE` (`0x1b59f0`); `len x = 0` panic (excluded); `x[0]` odd → `oddE` (`0x1b5990`); even with
`len y > 1` → `zeroE` (`0x1b5980`, `return z[:0]`); even with `len y = 1` → the `trailingZeroBits` loop head `tzH`
(`0x1b5a44`, `R11 = 0`). Memory at every exit: `W0` (the five stores).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

abbrev oneE : Nat := 1792496
abbrev oddE : Nat := 1792400
abbrev zeroE : Nat := 1792384
abbrev tzH : Nat := 1792580

/-- the memory after the prologue and the three pointer spills -/
@[reducible] def W0 (M : Memory) (sp r29 r30 zp xp yp : Nat) : Memory :=
  ((((M.writeLE sp 8 r30).writeLE (sp - 8) 8 r29).writeLE (sp + 120) 8 zp).writeLE (sp + 152) 8 xp).writeLE
    (sp + 176) 8 yp

theorem w0_rd {M : Memory} {sp r29 r30 zp xp yp a k : Nat} (hsp : 8 ≤ sp) (h : Outside a k [(sp - 8, sp + 184)]) :
    (W0 M sp r29 r30 zp xp yp).readLE a k = M.readLE a k := by
  simp only [outside_cons, outside_nil, and_true] at h
  simp (disch := omega) only [W0, Memory.readLE_writeLE_of_disjoint]

theorem w0_frame (M : Memory) {sp r29 r30 zp xp yp : Nat} (hsp : 8 ≤ sp) :
    MemFrame M (W0 M sp r29 r30 zp xp yp) [(sp - 8, sp + 8), (sp + 120, sp + 184)] := by
  simp only [W0]
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 184)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 184)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 120, sp + 184)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 8)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 8)) (by simp) (by simp only; omega) (by simp only; omega)
  exact MemFrame.refl _ _

theorem w0_lr {M : Memory} {sp r29 r30 zp xp yp : Nat} (hsp : 8 ≤ sp) (h30 : r30 < 2 ^ 64) :
    (W0 M sp r29 r30 zp xp yp).readLE sp 8 = r30 := by
  simp (disch := omega) only [W0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt h30

theorem w0_fp {M : Memory} {sp r29 r30 zp xp yp : Nat} (hsp : 8 ≤ sp) (h29 : r29 < 2 ^ 64) :
    (W0 M sp r29 r30 zp xp yp).readLE (sp - 8) 8 = r29 := by
  simp (disch := omega) only [W0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt h29

/-- the register file at an exit of `ent` (arguments kept, `X29 = sp - 8`) -/
@[reducible] def RE (S' : State) (sp g zp zl zc st xp xl xc yp yl yc lm : Nat) (r18 : BitVec 64) : Prop :=
  S'.sp = BitVec.ofNat 64 sp ∧ S'.regs 0 = BitVec.ofNat 64 zp ∧ S'.regs 1 = BitVec.ofNat 64 zl ∧
    S'.regs 2 = BitVec.ofNat 64 zc ∧ S'.regs 3 = BitVec.ofNat 64 st ∧ S'.regs 4 = BitVec.ofNat 64 xp ∧
    S'.regs 5 = BitVec.ofNat 64 xl ∧ S'.regs 6 = BitVec.ofNat 64 xc ∧ S'.regs 7 = BitVec.ofNat 64 yp ∧
    S'.regs 8 = BitVec.ofNat 64 yl ∧ S'.regs 9 = BitVec.ofNat 64 yc ∧ S'.regs 10 = BitVec.ofNat 64 lm ∧
    S'.regs 18 = r18 ∧ S'.regs 28 = BitVec.ofNat 64 g ∧ S'.regs 29 = BitVec.ofNat 64 (sp - 8)

theorem bit0_iff (v : Nat) : ((BitVec.ofNat 64 v).getLsbD 0 == true) = true ↔ v % 2 = 1 := by
  rw [beq_iff_eq, BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit_zero, decide_eq_true_iff]; omega

theorem bit0_iff' (v : Nat) : ¬((BitVec.ofNat 64 v).getLsbD 0 == true) = true ↔ v % 2 = 0 := by
  rw [bit0_iff]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **from the entry to the branch points** -/
theorem ent (impl : List Segment) (ret0 : BitVec 64) (Q : State → Prop)
    (sp g zp zl zc st xp xl xc yp yl yc lm : Nat) (r29 r30 : BitVec 64) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 184 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 192 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 112)
    (hyl0 : 0 < yl) (hyl : yl < 2 ^ 63) (hy0 : yl = 1 → M.readLE yp 8 ≠ 0) (hya : M.accessible yp 8 false = true)
    (hyp : yp < 2 ^ 64) (hyw : Outside yp 8 [(sp - 8, sp + 184)])
    (hxl0 : 0 < xl) (hxl : xl < 2 ^ 64) (hxa : M.accessible xp 8 false = true) (hxp : xp < 2 ^ 64)
    (hxw : Outside xp 8 [(sp - 8, sp + 184)]) (hlm : lm < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 fnE) (hsp : S.sp = BitVec.ofNat 64 (sp + 112))
    (hR : S.regs 0 = BitVec.ofNat 64 zp ∧ S.regs 1 = BitVec.ofNat 64 zl ∧ S.regs 2 = BitVec.ofNat 64 zc ∧
      S.regs 3 = BitVec.ofNat 64 st ∧ S.regs 4 = BitVec.ofNat 64 xp ∧ S.regs 5 = BitVec.ofNat 64 xl ∧
      S.regs 6 = BitVec.ofNat 64 xc ∧ S.regs 7 = BitVec.ofNat 64 yp ∧ S.regs 8 = BitVec.ofNat 64 yl ∧
      S.regs 9 = BitVec.ofNat 64 yc ∧ S.regs 10 = BitVec.ofNat 64 lm)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (h30 : S.regs 30 = r30) (hmem : S.mem = M)
    (K1 : lm = 1 → ∀ S' : State, S'.pc = BitVec.ofNat 64 oneE → RE S' sp g zp zl zc st xp xl xc yp yl yc lm (S.regs 18) →
      S'.mem = W0 M sp r29.toNat r30.toNat zp xp yp → ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K2 : ¬lm = 1 → M.readLE xp 8 % 2 = 1 → ∀ S' : State, S'.pc = BitVec.ofNat 64 oddE →
      RE S' sp g zp zl zc st xp xl xc yp yl yc lm (S.regs 18) →
      S'.mem = W0 M sp r29.toNat r30.toNat zp xp yp → ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K3 : ¬lm = 1 → M.readLE xp 8 % 2 = 0 → 1 < yl → ∀ S' : State, S'.pc = BitVec.ofNat 64 zeroE →
      RE S' sp g zp zl zc st xp xl xc yp yl yc lm (S.regs 18) →
      S'.mem = W0 M sp r29.toNat r30.toNat zp xp yp → ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K4 : ¬lm = 1 → M.readLE xp 8 % 2 = 0 → yl = 1 → ∀ S' : State, S'.pc = BitVec.ofNat 64 tzH →
      RE S' sp g zp zl zc st xp xl xc yp yl yc lm (S.regs 18) → S'.regs 11 = 0#64 →
      S'.mem = W0 M sp r29.toNat r30.toNat zp xp yp → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hR
  generalize e18 : S.regs 18 = x18 at K1 K2 K3 K4
  have es1 : BitVec.ofNat 64 (sp + 112) - 112#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have rx : (W0 M sp r29.toNat r30.toNat zp xp yp).readLE xp 8 = M.readLE xp 8 := w0_rd hsp1 hxw
  have ry : (W0 M sp r29.toNat r30.toNat zp xp yp).readLE yp 8 = M.readLE yp 8 := w0_rd hsp1 hyw
  have hti : (BitVec.ofNat 64 yl).toInt = yl := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), if_pos (by omega)]
  have hx64 : M.readLE xp 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  subst hmem
  by_cases hy1 : yl = 1
  · have hy0' := hy0 hy1
    subst hy1
    janus_run [es1, es2, rx, ry, hti] until [oneE, oddE, zeroE, tzH]
    · refine K1 hbr _ rfl ?_ rfl
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp
    · refine K2 ‹_› ((bit0_iff _).1 hbr) _ rfl ?_ rfl
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp
    · refine K4 ‹_› ((bit0_iff' _).1 hbr) rfl _ rfl ?_ (by janus_simp) rfl
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp
  · janus_run [es1, es2, rx, ry, hti] until [oneE, oddE, zeroE, tzH]
    · refine K1 hbr _ rfl ?_ rfl
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp
    · refine K2 ‹_› ((bit0_iff _).1 hbr) _ rfl ?_ rfl
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp
    · refine K3 ‹_› ((bit0_iff' _).1 ‹_›) (by omega) _ rfl ?_ rfl
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp

end FvModexp.Arm64.P2D
