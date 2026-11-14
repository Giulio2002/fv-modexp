import FvModexp.Proofs.Amd64.Exp.P2DDefs

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): from the entry to the four branch points (agent asm s66; twin of infra's arm64 `P2DEnt`)

`ent`: stack guard, prologue (`PUSHQ BP; SUBQ $0x68`, frame base `sp = RSP - 0x70`), spills `[sp + 0x90] := z.ptr`,
`[sp + 0xb0] := x.ptr`, the `len y` / `y[0]` panics (excluded), `logM = 1` → `oneE` (`0x5e90e1`); `len x = 0` panic
(excluded); `x[0]` odd → `oddE` (`0x5e902d`); even with `len y > 1` → `zeroE` (`0x5e9025`); even with `len y = 1` →
the `trailingZeroBits` loop head `tzH` (`0x5e912f`, `R12 = 0`). Memory at every exit: `W0` (the three writes).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

abbrev oneE : Nat := 0x5e90e1
abbrev oddE : Nat := 0x5e902d
abbrev zeroE : Nat := 0x5e9025
abbrev tzH : Nat := 0x5e912f

/-- the memory after the prologue (`PUSHQ BP`) and the two spills -/
@[reducible] def W0 (M : Memory) (sp bp zp xp : Nat) : Memory :=
  ((M.writeLE (sp + 104) 8 bp).writeLE (sp + 144) 8 zp).writeLE (sp + 176) 8 xp

theorem w0_rd {M : Memory} {sp bp zp xp a k : Nat} (h : a + k ≤ sp + 0x68 ∨ sp + 0xb8 ≤ a) :
    (W0 M sp bp zp xp).readLE a k = M.readLE a k := by
  simp (disch := omega) only [W0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]

theorem w0_frame (M : Memory) (sp bp zp xp : Nat) :
    MemFrame M (W0 M sp bp zp xp) [(sp + 0x68, sp + 0x70), (sp + 0x90, sp + 0x98), (sp + 0xb0, sp + 0xb8)] := by
  simp only [W0]
  refine MemFrame.writeLE ?_ _ (r := (sp + 0xb0, sp + 0xb8)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 0x90, sp + 0x98)) (by simp) (by simp only; omega) (by simp only; omega)
  refine MemFrame.writeLE ?_ _ (r := (sp + 0x68, sp + 0x70)) (by simp) (by simp only; omega) (by simp only; omega)
  exact MemFrame.refl _ _

theorem w0_bp {M : Memory} {sp bp zp xp : Nat} (h : bp < 2 ^ 64) : (W0 M sp bp zp xp).readLE (sp + 0x68) 8 = bp := by
  simp (disch := omega) only [W0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt h

theorem w0_zp {M : Memory} {sp bp zp xp : Nat} (h : zp < 2 ^ 64) : (W0 M sp bp zp xp).readLE (sp + 0x90) 8 = zp := by
  simp (disch := omega) only [W0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt h

theorem w0_xp {M : Memory} {sp bp zp xp : Nat} (h : xp < 2 ^ 64) : (W0 M sp bp zp xp).readLE (sp + 0xb0) 8 = xp := by
  simp (disch := omega) only [W0, Janus.Arm64.Memory.readLE_writeLE_self]
  exact Nat.mod_eq_of_lt h

/-- the register file at an exit of `ent` (arguments kept, `RBP = sp + 0x68`, `R11 = yp`, `RDX = yl`) -/
@[reducible] def RE (S0 S' : State) (sp g zp zl zc st xp xl xc yp yl lm : Nat) : Prop :=
  S'.regs 4 = BitVec.ofNat 64 sp ∧ S'.regs 5 = BitVec.ofNat 64 (sp + 0x68) ∧ S'.regs 0 = BitVec.ofNat 64 zp ∧
    S'.regs 3 = BitVec.ofNat 64 zl ∧ S'.regs 1 = BitVec.ofNat 64 zc ∧ S'.regs 7 = BitVec.ofNat 64 st ∧
    S'.regs 6 = BitVec.ofNat 64 xp ∧ S'.regs 8 = BitVec.ofNat 64 xl ∧ S'.regs 9 = BitVec.ofNat 64 xc ∧
    S'.regs 10 = BitVec.ofNat 64 lm ∧ S'.regs 11 = BitVec.ofNat 64 yp ∧ S'.regs 2 = BitVec.ofNat 64 yl ∧
    S'.regs 14 = BitVec.ofNat 64 g ∧ S'.fsBase = S0.fsBase ∧ S'.xmm 15 = S0.xmm 15 ∧ S'.df = S0.df

theorem bit0_iff (v : Nat) : (BitVec.setWidth 32 (BitVec.ofNat 64 v)).getLsbD 0 = true ↔ v % 2 = 1 := by
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit_zero]; simp

theorem bit0_iff' (v : Nat) : ¬(BitVec.setWidth 32 (BitVec.ofNat 64 v)).getLsbD 0 = true ↔ v % 2 = 0 := by
  rw [bit0_iff]; omega

theorem lm1_iff (lm : Nat) (h : lm < 2 ^ 64) : (18446744073709551615 + lm) % 18446744073709551616 = 0 ↔ lm = 1 := by
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the entry to the four branch points** -/
theorem ent {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop)
    (sp g zp zl zc st xp xl xc yp yl lm bp : Nat) (M : Memory)
    (hsp2 : sp + 0xb8 ≤ 2 ^ 48) (hacc : M.accessible (sp + 0x68) 0x50 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 0x70)
    (hryl : M.readLE (sp + 0x80) 8 = yl) (hryp : M.readLE (sp + 0x78) 8 = yp)
    (hyl0 : 0 < yl) (hyl : yl < 2 ^ 63) (hy0 : yl = 1 → M.readLE yp 8 ≠ 0) (hya : M.accessible yp 8 false = true)
    (hyp : yp + 8 ≤ 2 ^ 48) (hyw : yp + 8 ≤ sp + 0x68 ∨ sp + 0xb8 ≤ yp)
    (hxl0 : 0 < xl) (hxl : xl < 2 ^ 64) (hxa : M.accessible xp 8 false = true) (hxp : xp + 8 ≤ 2 ^ 48)
    (hxw : xp + 8 ≤ sp + 0x68 ∨ sp + 0xb8 ≤ xp) (hlm : lm < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 fnE) (h4 : S.regs 4 = BitVec.ofNat 64 (sp + 0x70))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (h10 : S.regs 10 = BitVec.ofNat 64 lm)
    (h5 : S.regs 5 = BitVec.ofNat 64 bp) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (K1 : lm = 1 → ∀ S' : State, S'.rip = BitVec.ofNat 64 oneE → RE S S' sp g zp zl zc st xp xl xc yp yl lm →
      S'.mem = W0 M sp bp zp xp → ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K2 : ¬lm = 1 → M.readLE xp 8 % 2 = 1 → ∀ S' : State, S'.rip = BitVec.ofNat 64 oddE →
      RE S S' sp g zp zl zc st xp xl xc yp yl lm → S'.mem = W0 M sp bp zp xp →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K3 : ¬lm = 1 → M.readLE xp 8 % 2 = 0 → 1 < yl → ∀ S' : State, S'.rip = BitVec.ofNat 64 zeroE →
      RE S S' sp g zp zl zc st xp xl xc yp yl lm → S'.mem = W0 M sp bp zp xp →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K4 : ¬lm = 1 → M.readLE xp 8 % 2 = 0 → yl = 1 → ∀ S' : State, S'.rip = BitVec.ofNat 64 tzH →
      RE S S' sp g zp zl zc st xp xl xc yp yl lm → S'.regs 12 = 0#64 → S'.mem = W0 M sp bp zp xp →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (sp + 0x70) - 8#64 = BitVec.ofNat 64 (sp + 0x68) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (sp + 0x68) - 0x68#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hti : (BitVec.ofNat 64 yl).toInt = yl := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left (by omega)]
  have hl1 := lm1_iff lm hlm
  subst hmem
  janus64_run [es1, es2, hryl, hryp, hti] until [oneE, oddE, zeroE, tzH]
  all_goals first
    | (exfalso; omega)
    | exact K1 (by omega) _ rfl (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp) rfl
    | exact K2 (by omega) ((bit0_iff _).1 (by janus_assumption)) _ rfl (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp) rfl
    | exact K3 (by omega) ((bit0_iff' _).1 (by janus_assumption)) (by omega) _ rfl (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp) rfl
    | exact K4 (by omega) ((bit0_iff' _).1 (by janus_assumption)) (by omega) _ rfl (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp) (by janus64_simp) rfl

end FvModexp.Amd64.P2D

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

set_option maxRecDepth 20000 in
/-- **`ent` from the function's precondition** (`PreD` with window `[RSP - stk, RSP + A)`, `72 ≤ A`, `4320 ≤ stk`;
frame base `RSP - 0x70`, memory `W0 s.mem …`) -/
theorem entP {impl : List Amd64.Segment} (Q : State → Prop) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {stk A cst zp zl zc st xp xl xc yp yl yc lm : Nat} (s : State) {ret0 : W64}
    (hP : PreD R b L stk A cst zp zl zc st xp xl yp yl lm s) (hk : 4320 ≤ stk) (hA : 72 ≤ A)
    (hpc : s.rip = BitVec.ofNat 64 fnE) (hR : Regs s zp zl zc st xp xl xc yp yl yc lm)
    (K1 : lm = 1 → ∀ S' : State, S'.rip = BitVec.ofNat 64 oneE →
      RE s S' ((s.regs 4).toNat - 0x70) (s.regs 14).toNat zp zl zc st xp xl xc yp yl lm →
      S'.mem = W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K2 : ¬lm = 1 → s.mem.readLE xp 8 % 2 = 1 → ∀ S' : State, S'.rip = BitVec.ofNat 64 oddE →
      RE s S' ((s.regs 4).toNat - 0x70) (s.regs 14).toNat zp zl zc st xp xl xc yp yl lm →
      S'.mem = W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K3 : ¬lm = 1 → s.mem.readLE xp 8 % 2 = 0 → 1 < yl → ∀ S' : State, S'.rip = BitVec.ofNat 64 zeroE →
      RE s S' ((s.regs 4).toNat - 0x70) (s.regs 14).toNat zp zl zc st xp xl xc yp yl lm →
      S'.mem = W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (K4 : ¬lm = 1 → s.mem.readLE xp 8 % 2 = 0 → yl = 1 → ∀ S' : State, S'.rip = BitVec.ofNat 64 tzH →
      RE s S' ((s.regs 4).toNat - 0x70) (s.regs 14).toNat zp zl zc st xp xl xc yp yl lm → S'.regs 12 = 0#64 →
      S'.mem = W0 s.mem ((s.regs 4).toNat - 0x70) (s.regs 5).toNat zp xp →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 s Q := by
  obtain ⟨hC, hX, hY, -, hlm, -, -⟩ := hP
  obtain ⟨⟨⟨g1, g2, g3⟩, ⟨hbel, h48, hacc⟩, -, -, -, -, -, -, -, -⟩, -, -, -, -, -, -, hins, -⟩ := hC
  obtain ⟨⟨-, hxa, hx48, -, hxw⟩, hxn, -⟩ := hins xp xl (by simp)
  obtain ⟨⟨-, hya, hy48, -, hyw⟩, hyn, -⟩ := hins yp yl (by simp)
  obtain ⟨h0, h3, h1, h7, h6, h8, h9, h10, hy1, hy2, -⟩ := hR
  simp only [regG, regSP, stackguard0, stackguard0Offset] at g1 g2 g3 hbel h48 hacc
  generalize hSP : (s.regs 4).toNat = SP at *
  have hxl0 : 0 < xl := by
    rcases Nat.eq_zero_or_pos xl with h | h
    · subst h; simp [natVal] at hX
    · exact h
  have hyl0 : 0 < yl := by
    rcases Nat.eq_zero_or_pos yl with h | h
    · subst h; simp [natVal] at hY
    · exact h
  have hsp : s.regs 4 = BitVec.ofNat 64 (SP - 0x70 + 0x70) := by
    apply BitVec.eq_of_toNat_eq; rw [hSP, BitVec.toNat_ofNat]; omega
  have hg : (s.regs 14).toNat < 2 ^ 64 := BitVec.isLt _
  have h5 : s.regs 5 = BitVec.ofNat 64 (s.regs 5).toNat := by apply BitVec.eq_of_toNat_eq; simp
  have h14 : s.regs 14 = BitVec.ofNat 64 (s.regs 14).toNat := by apply BitVec.eq_of_toNat_eq; simp
  simp only [win, hSP, outside_cons, outside_nil, and_true] at hxw hyw
  refine ent ret0 Q (SP - 0x70) (s.regs 14).toNat zp zl zc st xp xl xc yp yl lm (s.regs 5).toNat s.mem
    (by omega) (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) (by omega)
    g2 (by omega) (by rw [show SP - 0x70 + 0x80 = SP + 0 + 16 by omega]; exact hy2)
    (by rw [show SP - 0x70 + 0x78 = SP + 0 + 8 by omega]; exact hy1) hyl0 (by omega)
    (fun h1 => by subst h1; simpa [natVal] using (Nat.pos_iff_ne_zero.1 hY))
    (Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hya (Nat.le_refl _) (by omega)))
    (by omega) (by omega) hxl0 (by omega)
    (Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hxa (Nat.le_refl _) (by omega)))
    (by omega) (by omega) (by omega) s hpc hsp h0 h3 h1 h7 h6 h8 h9 h10 h5 h14 rfl
    K1 K2 K3 K4

end FvModexp.Amd64.P2D
