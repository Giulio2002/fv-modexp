import FvModexp.Proofs.Arm64.Exp.EvStmt

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the internal entry facts `EPre` and the frame slots `ESl` (agent infra)

At the entry state `s` (`SP = sp + 336`, the function's frame will be `sp`), arguments `z = (zp, _, zc)` X0-2,
`stk = st` X3, `x = (xp, xl, xc)` X4-6, `y = (yp, yl, yc)` X7-9, `m = (mp, ml, mc)` X10-12. The window is
`[sp - K, sp + 448)` (`= [SP - (K + 336), SP + 112)`). Same conjunct LAYOUT as `P2W2.EPre` (positions 0..33, so the
shared context lemmas copied from `P2W2WC` keep their projections): position 5/6 = `0 < ml ∧ ml ≤ 128` (P2W2:
`logM`), `y` and `x` objects at 7..19, `z` at 20..22, the stack at 24..31; position 32 = `stLen ≤ 2^16` (the real
stack need is a separate hypothesis); 33 = `natOne`; 34 = the `m` object (+ the `z`/`m` separation, the capacities
`yc`/`mc` as words, `stCap = 0 → stW = 0`); 35 = the invariant. `EvEP.epre_of` derives it from `ExpEven.Pre`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the free part of the stack's array -/
@[reducible] def free (M : Memory) (st : Nat) : Nat × Nat := (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- an object at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def OE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - K) (K + 448) ∧ Apart a k st 24 ∧
    Apart a k (free M st).1 (free M st).2

/-- the call environment of the entry (entry state `s`, frame `sp = SP(s) - 336`, window `[sp - K, sp + 448)`) -/
@[reducible] def EEnv (R : RtInv) (L : List (Nat × Nat)) (g sp K : Nat) (s : State) : Prop :=
  s.sp = BitVec.ofNat 64 (sp + 336) ∧ s.regs 28 = BitVec.ofNat 64 g ∧
  g + 24 ≤ 2 ^ 48 ∧ s.mem.accessible (g + 16) 8 false = true ∧ s.mem.readLE (g + 16) 8 + K < sp ∧
  Outside (g + 16) 8 ((sp - K, sp + 448) :: R.rt) ∧ sp % 16 = 0 ∧ 4304 ≤ K ∧ K ≤ sp ∧ sp + 448 ≤ 2 ^ 48 ∧
  s.mem.accessible (sp - K) (K + 448) true = true ∧ LiveSep [(sp - K, sp + 448)] R.rt ∧
  LiveSep L [(sp - K, sp + 448)] ∧ Extracted.program.DataLoaded s.mem ∧ RunIface.Serves R

theorem EEnv.sp {R : RtInv} {L : List (Nat × Nat)} {g sp K : Nat} {s : State} (h : EEnv R L g sp K s) :
    s.sp.toNat = sp + 336 := by
  rw [h.1, BitVec.toNat_ofNat]; have := h.2.2.2.2.2.2.2.2.2.1; omega

theorem EEnv.g {R : RtInv} {L : List (Nat × Nat)} {g sp K : Nat} {s : State} (h : EEnv R L g sp K s) :
    (s.regs 28).toNat = g := by
  rw [h.2.1, BitVec.toNat_ofNat]; have := h.2.2.1; omega

/-- the entry facts of `nat.expNNEven` (layout: see the module doc) -/
def EPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) : Prop :=
  EEnv R L g sp K s ∧ K ≤ 2 ^ 20 ∧ RunIface.Globals R s.mem [(sp - K, sp + 448)] ∧ RoOut R ∧
  Outside StackNat.wT 16 R.rt ∧ 0 < ml ∧ ml ≤ 128 ∧
  OE R L sp K st s.mem yp (8 * yl) ∧ s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧
    NatNorm s.mem yp yl ∧ 0 < yl ∧ yl ≤ 2 ^ 9 ∧
  OE R L sp K st s.mem xp (8 * xl) ∧ s.mem.accessible xp (8 * xl) false = true ∧ xp + 8 * xl ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ xl ≤ 128 ∧ xp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧
  zp < 2 ^ 64 ∧ zc < 2 ^ 40 ∧ (0 < zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart zp (8 * zc) xp (8 * xl) ∧ Apart zp (8 * zc) yp (8 * yl) ∧ Apart zp (8 * zc) RunIface.gA 32) ∧
  OE R L sp K st s.mem RunIface.gA 32 ∧
  StkOK s.mem R L st ∧ Apart st 24 (sp - K) (K + 448) ∧ Apart st 24 (g + 16) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - K) (K + 448) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (free s.mem st).1 (free s.mem st).2 ∧ st ≠ 0 ∧
  stLen s.mem st ≤ 2 ^ 16 ∧
  (∃ op, EvenHyp.NatOne R L s.mem op ([(sp - K, sp + 448), (zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
    EvenHyp.StkApart s.mem st op 8) ∧
  (OE R L sp K st s.mem mp (8 * ml) ∧ s.mem.accessible mp (8 * ml) false = true ∧ mp + 8 * ml ≤ 2 ^ 48 ∧
    NatNorm s.mem mp ml ∧ (0 < zc → Apart zp (8 * zc) mp (8 * ml)) ∧ yp < 2 ^ 64 ∧ yc < 2 ^ 64 ∧ mp < 2 ^ 64 ∧
    mc < 2 ^ 64 ∧ (stCap s.mem st = 0 → stW s.mem st = 0)) ∧
  R.inv b L g (view R.rt L s.mem)

/-- the array at a later point: kept or fresh -/
@[reducible] def ArrKF (R : RtInv) (L : List (Nat × Nat)) (st : Nat) (M0 M : Memory) : Prop :=
  (stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)

/-- the frame slots after the prologue and the `tz` loop (saved FP/LR, defer record `296..320`, argument spills
`344..448`, `n` at `184`) -/
@[reducible] def ESl (M : Memory) (sp st : Nat) (r29 : BitVec 64) (ret zp zc xp xl xc yp yl yc mp ml mc len0 n : Nat) :
    Prop :=
  M.readLE (sp - 8) 8 = r29.toNat ∧ M.readLE sp 8 = ret ∧ M.readLE (sp + 320) 8 = sp + 296 ∧
  M.readLE (sp + 296) 8 = dwE ∧ M.readLE (sp + 304) 8 = st ∧ M.readLE (sp + 312) 8 = len0 ∧
  M.readLE (sp + 344) 8 = zp ∧ M.readLE (sp + 360) 8 = zc ∧ M.readLE (sp + 368) 8 = st ∧
  M.readLE (sp + 376) 8 = xp ∧ M.readLE (sp + 384) 8 = xl ∧ M.readLE (sp + 392) 8 = xc ∧
  M.readLE (sp + 400) 8 = yp ∧ M.readLE (sp + 408) 8 = yl ∧ M.readLE (sp + 416) 8 = yc ∧
  M.readLE (sp + 424) 8 = mp ∧ M.readLE (sp + 432) 8 = ml ∧ M.readLE (sp + 440) 8 = mc ∧
  M.readLE (sp + 184) 8 = n

/-- the slot ranges of `ESl` -/
@[reducible] def SlotR (sp a k : Nat) : Prop :=
  sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 184 ≤ a ∧ a + k ≤ sp + 192 ∨ sp + 296 ≤ a ∧ a + k ≤ sp + 328 ∨
    sp + 344 ≤ a ∧ a + k ≤ sp + 448

theorem ESl.keep {M1 M3 : Memory} {sp st : Nat} {r29 : BitVec 64} {ret zp zc xp xl xc yp yl yc mp ml mc len0 n : Nat}
    (h : ESl M1 sp st r29 ret zp zc xp xl xc yp yl yc mp ml mc len0 n)
    (hk : ∀ a k, SlotR sp a k → M3.readLE a k = M1.readLE a k)
    (hsp : 8 ≤ sp) : ESl M3 sp st r29 ret zp zc xp xl xc yp yl yc mp ml mc len0 n := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := h
  exact ⟨(hk _ _ (by omega)).trans a1, (hk _ _ (by omega)).trans a2, (hk _ _ (by omega)).trans a3,
    (hk _ _ (by omega)).trans a4, (hk _ _ (by omega)).trans a5, (hk _ _ (by omega)).trans a6,
    (hk _ _ (by omega)).trans a7, (hk _ _ (by omega)).trans a8, (hk _ _ (by omega)).trans a9,
    (hk _ _ (by omega)).trans a10, (hk _ _ (by omega)).trans a11, (hk _ _ (by omega)).trans a12,
    (hk _ _ (by omega)).trans a13, (hk _ _ (by omega)).trans a14, (hk _ _ (by omega)).trans a15,
    (hk _ _ (by omega)).trans a16, (hk _ _ (by omega)).trans a17, (hk _ _ (by omega)).trans a18,
    (hk _ _ (by omega)).trans a19⟩

end FvModexp.Arm64.ExpEven
