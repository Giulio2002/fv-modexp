import FvModexp.Proofs.Amd64.Exp.EvDefs
import FvModexp.Proofs.Amd64.Exp.NHyp
import FvModexp.Proofs.Amd64.Exp.CallW

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the internal entry facts `EPre` and the frame slots `ESl` (asm s56; twin of infra's arm64
`EvPre`, environment as expmc's amd64 `W2EnDefs.EEnv` / `W2EnCtx.EPre`)

At the entry state `s` (`RSP = sp + 0x148`, `sp` = the frame after `PUSHQ BP; SUBQ $0x140`), arguments `z = (zp, _, zc)`
RAX/RBX/RCX, `stk = st` RDI, `x = (xp, xl, xc)` RSI/R8/R9, `y = (yp, yl, yc)` at `sp + 0x150/0x158/0x160`, `m = (mp, ml,
mc)` at `sp + 0x168/0x170/0x178`. The window is `[sp - 8 - K, sp + 0x1b8)` = the callee stacks (`K`), the frame, the
saved `BP`, the return address, the stack arguments and the register spill area (`EvenSum`'s `above = 112`): the
`CallW.CEnv` of the callee `RSP = sp - 8` with `A = 0x1c0`.

Stack floor `42816 ≤ K` (asm s57): the binding callee is the inner `expNN` (`ExpN.NEnv`: its own `K_N ≥ 41640`, window
`K_N + 0x498` below its entry `RSP = sp - 8`), so `K ≥ 41640 + 0x498 = 42816`; every other callee needs less.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- the top of the window above `sp` -/
abbrev wTop : Nat := 0x1b8

/-- the free part of the stack's array -/
@[reducible] def free (M : Memory) (st : Nat) : Nat × Nat := (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- an object at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def OE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - 8 - K) (K + 0x1c0) ∧ Apart a k st 24 ∧
    Apart a k (free M st).1 (free M st).2

/-- the call environment of the entry (entry state `s`, `RSP = sp + 0x148`, window `[sp - 8 - K, sp + 0x1b8)`) -/
@[reducible] def EEnv (R : RtInv) (L : List (Nat × Nat)) (g fs sp K : Nat) (s : State) : Prop :=
  s.regs 4 = BitVec.ofNat 64 (sp + 0x148) ∧ s.regs 14 = BitVec.ofNat 64 g ∧ s.fsBase.toNat = fs ∧
  s.xmm 15 = 0 ∧ s.df = false ∧ sp % 8 = 0 ∧ 42816 ≤ K ∧ K ≤ 2 ^ 20 ∧
  CallW.CEnv R L g fs (sp - 8) K 0x1c0 s.mem ∧ RunIface.Serves R

theorem EEnv.sp {R : RtInv} {L : List (Nat × Nat)} {g fs sp K : Nat} {s : State} (h : EEnv R L g fs sp K s) :
    (s.regs 4).toNat = sp + 0x148 := by
  obtain ⟨h1, -, -, -, -, -, -, -, ⟨-, -, hA, -⟩, -⟩ := h
  rw [h1, BitVec.toNat_ofNat]; omega

theorem EEnv.g {R : RtInv} {L : List (Nat × Nat)} {g fs sp K : Nat} {s : State} (h : EEnv R L g fs sp K s) :
    (s.regs 14).toNat = g := by
  obtain ⟨-, h1, -, -, -, -, -, -, ⟨-, -, -, -, hg, -⟩, -⟩ := h
  rw [h1, BitVec.toNat_ofNat]; omega

/-- the entry facts of `nat.expNNEven` (arm64 `EvPre.EPre` + the TLS slot, `hasADX` and the stack-argument words;
`bp` = the caller's `RBP`, `r` = the return address) -/
def EPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) : Prop :=
  EEnv R L g fs sp K s ∧ RunIface.Globals R s.mem [(sp - 8 - K, sp + wTop)] ∧
  Outside StackNat.wT 16 R.rt ∧ s.mem.accessible Callees.adxAddr 1 false = true ∧ 0 < ml ∧ ml ≤ 128 ∧
  OE R L sp K st s.mem yp (8 * yl) ∧ s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧
    NatNorm s.mem yp yl ∧ 0 < yl ∧ yl ≤ 2 ^ 9 ∧
  OE R L sp K st s.mem xp (8 * xl) ∧ s.mem.accessible xp (8 * xl) false = true ∧ xp + 8 * xl ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ xl ≤ 128 ∧ xp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧
  zp < 2 ^ 64 ∧ zc < 2 ^ 40 ∧ (0 < zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart (fs - 8) 8 zp (8 * zc) ∧ Apart zp (8 * zc) xp (8 * xl) ∧ Apart zp (8 * zc) yp (8 * yl) ∧
    Apart zp (8 * zc) RunIface.gA 32) ∧
  OE R L sp K st s.mem RunIface.gA 32 ∧
  StkOK s.mem R L st ∧ Apart st 24 (sp - 8 - K) (K + 0x1c0) ∧ Apart st 24 (g + 16) 8 ∧ Apart st 24 (fs - 8) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - 8 - K) (K + 0x1c0) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8 ∧ Apart (stW s.mem st) (8 * stCap s.mem st) (fs - 8) 8) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (free s.mem st).1 (free s.mem st).2 ∧ st ≠ 0 ∧
  stLen s.mem st ≤ 2 ^ 16 ∧
  (∃ op, EvenHyp.NatOne R L s.mem op ([(sp - 8 - K, sp + wTop), (zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
    NHyp.StkApart s.mem st op 8) ∧
  (OE R L sp K st s.mem mp (8 * ml) ∧ s.mem.accessible mp (8 * ml) false = true ∧ mp + 8 * ml ≤ 2 ^ 48 ∧
    NatNorm s.mem mp ml ∧ (0 < zc → Apart zp (8 * zc) mp (8 * ml)) ∧ yp < 2 ^ 64 ∧ yc < 2 ^ 64 ∧ mp < 2 ^ 64 ∧
    (mc < 2 ^ 40 ∧ ml ≤ mc) ∧ (stCap s.mem st = 0 → stW s.mem st = 0)) ∧
  ((s.regs 5).toNat = bp ∧ s.mem.readLE (sp + 0x148) 8 = r ∧ r < 2 ^ 47 ∧
    s.mem.readLE (sp + 0x150) 8 = yp ∧ s.mem.readLE (sp + 0x158) 8 = yl ∧ s.mem.readLE (sp + 0x160) 8 = yc ∧
    s.mem.readLE (sp + 0x168) 8 = mp ∧ s.mem.readLE (sp + 0x170) 8 = ml ∧ s.mem.readLE (sp + 0x178) 8 = mc) ∧
  R.inv b L g (view R.rt L s.mem)

/-- the array at a later point: kept or fresh -/
@[reducible] def ArrKF (R : RtInv) (L : List (Nat × Nat)) (st : Nat) (M0 M : Memory) : Prop :=
  (stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)

/-- the frame slots after the prologue and the `tz` loop (saved `BP`, return address, stack arguments, defer record
`0x120 .. 0x140`, register spills `0x180 .. 0x1b8` (`zl` not spilled), `n` at `0xb0`) -/
@[reducible] def ESl (M : Memory) (sp st bp r zp zc xp xl xc yp yl yc mp ml mc len0 n : Nat) : Prop :=
  M.readLE (sp + 0x140) 8 = bp ∧ M.readLE (sp + 0x148) 8 = r ∧ M.readLE (sp + 0x138) 8 = sp + 0x120 ∧
  M.readLE (sp + 0x120) 8 = dwE ∧ M.readLE (sp + 0x128) 8 = st ∧ M.readLE (sp + 0x130) 8 = len0 ∧
  M.readLE (sp + 0x180) 8 = zp ∧ M.readLE (sp + 0x190) 8 = zc ∧ M.readLE (sp + 0x198) 8 = st ∧
  M.readLE (sp + 0x1a0) 8 = xp ∧ M.readLE (sp + 0x1a8) 8 = xl ∧ M.readLE (sp + 0x1b0) 8 = xc ∧
  M.readLE (sp + 0x150) 8 = yp ∧ M.readLE (sp + 0x158) 8 = yl ∧ M.readLE (sp + 0x160) 8 = yc ∧
  M.readLE (sp + 0x168) 8 = mp ∧ M.readLE (sp + 0x170) 8 = ml ∧ M.readLE (sp + 0x178) 8 = mc ∧
  M.readLE (sp + 0xb0) 8 = n

/-- the slot ranges of `ESl` -/
@[reducible] def SlotR (sp a k : Nat) : Prop :=
  sp + 0xb0 ≤ a ∧ a + k ≤ sp + 0xb8 ∨ sp + 0x120 ≤ a ∧ a + k ≤ sp + 0x1b8

theorem ESl.keep {M1 M3 : Memory} {sp st bp r zp zc xp xl xc yp yl yc mp ml mc len0 n : Nat}
    (h : ESl M1 sp st bp r zp zc xp xl xc yp yl yc mp ml mc len0 n)
    (hk : ∀ a k, SlotR sp a k → M3.readLE a k = M1.readLE a k) :
    ESl M3 sp st bp r zp zc xp xl xc yp yl yc mp ml mc len0 n := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := h
  exact ⟨(hk _ _ (by omega)).trans a1, (hk _ _ (by omega)).trans a2, (hk _ _ (by omega)).trans a3,
    (hk _ _ (by omega)).trans a4, (hk _ _ (by omega)).trans a5, (hk _ _ (by omega)).trans a6,
    (hk _ _ (by omega)).trans a7, (hk _ _ (by omega)).trans a8, (hk _ _ (by omega)).trans a9,
    (hk _ _ (by omega)).trans a10, (hk _ _ (by omega)).trans a11, (hk _ _ (by omega)).trans a12,
    (hk _ _ (by omega)).trans a13, (hk _ _ (by omega)).trans a14, (hk _ _ (by omega)).trans a15,
    (hk _ _ (by omega)).trans a16, (hk _ _ (by omega)).trans a17, (hk _ _ (by omega)).trans a18,
    (hk _ _ (by omega)).trans a19⟩

end FvModexp.Amd64.ExpEven
