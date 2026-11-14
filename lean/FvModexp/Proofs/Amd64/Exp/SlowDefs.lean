import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.NHyp
import FvModexp.Proofs.Amd64.Exp.CallW

set_option autoImplicit false

/-!
# `nat.expNNSlow` (go-bigmodexpfix nat.go:732-787), amd64 — code map and the internal entry facts `EPre`
(agent expmc s78; twin of Arm64/Exp/SlowDefs.lean, environment as asm's amd64 `ExpEven.EPre` (EvPre.lean))

Entry `0x5e7a20 = 6191648` (program `LibW`: no `nat.expNN`, NESTED-PROGRAM RULE). Go ABIInternal: `z = (zp, zl, zc)`
RAX/RBX/RCX, `stk = st` RDI, `x = (xp, xl, xc)` RSI/R8/R9; `y`, `m` on the stack at `RSP + 8 … + 48` (`NHyp.StkArg`).
Frame: guard `LEAQ -0x130(SP), R12; CMPQ R12, 16(R14); JBE morestack` (+0x7f8), `PUSHQ BP; MOVQ SP, BP; SUBQ $0x1a8`
→ `sp := RSP_entry - 0x1b0`; saved RBP at `sp + 0x1a8`, return address at `sp + 0x1b0`. Caller area: y 0x1b8/0x1c0/0x1c8,
m 0x1d0/0x1d8/0x1e0; register spills 0x1e8 zp, 0x200 st, 0x208 xp, 0x210 xl, 0x218 xc (zl, zc not spilled). No defer,
no write barrier. Window `[sp - 8 - K, sp + 0x220)` = `CallW.CEnv … (sp - 8) K 0x228` (callee `RSP = sp - 8`); the
exported window `[RSP - stk, RSP + 0x70)` with `K = stk - 0x1b8`. Callees' stack arguments at `sp + 0 …`.

Code map (`fnE + off`):
* +0x00 prologue + spills; `z = z.set(x)` (inline `make`): `zc ≥ xl` → reuse (`DX = R8 = xl`) → `setJ` (+0xda);
  `xl = 1` → `makeslice(wT, 1, 1)` (ret `mk1R` +0x6d; `R8 = CX = 1`); else `makeslice(wT, xl, xl + 4)` (`xl + 4` spilled
  at 0x68; ret `mk2R` +0xb2; `R8 = xl`, `CX = xl + 4`); reloads `DX = xl`, `SI = xp`, `DI = st`, `R9 = xc`.
  `setJ`: `R10 = R8` (= `len z`), `R8 = min DX R8` (= `xl`); `zp = xp` → skip; else spill CX 0x80, R10 0x138, AX 0x158,
  `memmove(AX, SI, 8·xl)` (ret `mvR` +0x110), reload AX/CX/DX/SI/DI/R9/R10 → +0x148.
* +0x148: `R11 = yl = [0x1c0]`; `yl = 0` → `panicBounds` (+0x7f2; excluded); `R12 = yp`; `R13 = v = y[yl-1]`;
  `R15 = w = 63 - nlz v` (`BSRQ`; spilled 0x138), `shift = 64 - w`, `v <<= shift` (0 when `shift = 64`); `BX = xl`,
  `R8 = CX` (= `cap z`); slots 0xa8 0xa0 0x90 0x168 0x160 0x78 0x70 0x150 := 0; `CX = DX = 0` → `t1` (+0x28b).
* top loop test `t1` (+0x28b, `CMPQ CX, R15; JGE t1x`): state `j` CX, `w` R15 (= [0x138]), `v` R13, `z = (AX, R10, R8)`,
  `zz = ([0x150], [0x70], [0x78])`, `r = ([0x160], [0x90], DX)`, `q = ([0x168], [0xa0], [0xa8])`, BX = xl, SI = xp,
  DI = st, R9 = xc, R11 = yl, R12 = yp. Body spills R8 0x130, DX 0x98, R10 0x128, AX 0x188, CX 0xb8, R13 0x88;
  `zz.sqr(stk, z)` (ret `sq1R` +0x2e5) → `v < 0` (`BTQ $63`) → `zz.mul(stk, z, x)` (x at `sp + 0/8/0x10`; spills
  CX 0x120, AX 0x180, BX 0x118; ret `ml1R` +0x37d) → +0x39d: `len m ≠ 0` (`[0x1d8]`) → spills AX 0x178, BX 0x110,
  CX 0x108; `zz.div(stk, r, z, m)` (u = z at `sp + 0/8/0x10`, v = m at `sp + 0x18/0x20/0x28`; ret `dv1R` +0x44a);
  `len m = 0` → +0x3aa → join `j1` (+0x1f9: `v <<= 1`, `j++`, re-spill zz/q/r, reload) → `t1`.
* `t1x` (+0x4a9): `R11 = yl - 2` (`i`), `R13 = len q`, `R15 = cap q`, `CX = len r` → `iT` (+0x4e0): `i < 0` → `ex`;
  `[0xc0] = i`, `R9 = v = y[i]`, `[0xb0] = j = 0` → `t2`; `iS` (+0x4c7): `i--`, reload R9/R12 → `iT`.
* lower loop test `t2` (+0x589, `R12 = j = [0xb0]; CMPQ R12, $0x40; JGE iS`): state `v` R9, `z = (AX, R10, R8)`, zz as
  above, `q = ([0x168], R13, R15)`, `r = ([0x160], CX, DX)`, `i` R11 (= [0xc0]), BX = xl, SI = xp, DI = st. Body spills
  R9 0x88, R13 0x100, R15 0xf8, CX 0xf0, DX 0xe8, AX 0x170, R10 0xe0, R8 0xd8; sqr (ret `sq2R` +0x5fb), mul (spills
  CX 0xd0, BX 0xc8, AX 0x1a0; ret `ml2R` +0x693), div (spills AX 0x198, BX 0x148, CX 0x140; ret `dv2R` +0x765);
  join `j2` (+0x511) → `t2`.
* `ex` (+0x7c5): `z.norm()` (R10 down while the top word is 0), `len ≤ cap` check (`panicBounds` +0x7ed; excluded),
  `BX = R10`, `CX = R8`, epilogue, `RET` (+0x7ec).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNSlow"
theorem fn_eq : fn = NHyp.fnSlow := rfl
theorem fnBase : segAddr LibW.program fn = 6191648 := by decide
theorem fnBaseX : segAddr Extracted.program fn = 6191648 := by decide

/-- the function's entry -/
abbrev fnE : Nat := 6191648
/-- the join after `z.set`'s allocation, the post-`set` point, the loop tests and joins -/
abbrev setJ : Nat := fnE + 0xda
abbrev aSet : Nat := fnE + 0x148
abbrev t1 : Nat := fnE + 0x28b
abbrev j1 : Nat := fnE + 0x1f9
abbrev t1x : Nat := fnE + 0x4a9
abbrev iS : Nat := fnE + 0x4c7
abbrev iT : Nat := fnE + 0x4e0
abbrev t2 : Nat := fnE + 0x589
abbrev j2 : Nat := fnE + 0x511
/-- the exit (`z.norm()`) -/
abbrev ex : Nat := fnE + 0x7c5
/-- the call return points -/
abbrev mk1R : Nat := fnE + 0x6d
abbrev mk2R : Nat := fnE + 0xb2
abbrev mvR : Nat := fnE + 0x110
abbrev sq1R : Nat := fnE + 0x2e5
abbrev ml1R : Nat := fnE + 0x37d
abbrev dv1R : Nat := fnE + 0x44a
abbrev sq2R : Nat := fnE + 0x5fb
abbrev ml2R : Nat := fnE + 0x693
abbrev dv2R : Nat := fnE + 0x765

/-- the top of the window above `sp` (`RSP_entry + 0x70`) -/
abbrev wTop : Nat := 0x220

/-- the need of the exported shape (as arm64): `2^13` stack words when `len x, len m ≤ 128`, else unsatisfiable -/
@[reducible] def need (xl _yl ml : Nat) : Nat := if xl ≤ 128 ∧ ml ≤ 128 then 2 ^ 13 else 2 ^ 16 + 1

/-- the free part of the stack's array -/
@[reducible] def free (M : Memory) (st : Nat) : Nat × Nat := (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- an object at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def OE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - 8 - K) (K + 0x228) ∧ Apart a k st 24 ∧
    Apart a k (free M st).1 (free M st).2

/-- the call environment of the entry (entry state `s`, `RSP = sp + 0x1b0`, window `[sp - 8 - K, sp + 0x220)`) -/
@[reducible] def EEnv (R : RtInv) (L : List (Nat × Nat)) (g fs sp K : Nat) (s : State) : Prop :=
  s.regs 4 = BitVec.ofNat 64 (sp + 0x1b0) ∧ s.regs 14 = BitVec.ofNat 64 g ∧ s.fsBase.toNat = fs ∧
  s.xmm 15 = 0 ∧ s.df = false ∧ sp % 8 = 0 ∧ 41512 ≤ K ∧ K ≤ 2 ^ 20 ∧
  CallW.CEnv R L g fs (sp - 8) K 0x228 s.mem ∧ RunIface.Serves R

theorem EEnv.sp {R : RtInv} {L : List (Nat × Nat)} {g fs sp K : Nat} {s : State} (h : EEnv R L g fs sp K s) :
    (s.regs 4).toNat = sp + 0x1b0 := by
  obtain ⟨h1, -, -, -, -, -, -, -, ⟨-, -, hA, -⟩, -⟩ := h
  rw [h1, BitVec.toNat_ofNat]; omega

theorem EEnv.g {R : RtInv} {L : List (Nat × Nat)} {g fs sp K : Nat} {s : State} (h : EEnv R L g fs sp K s) :
    (s.regs 14).toNat = g := by
  obtain ⟨-, h1, -, -, -, -, -, -, ⟨-, -, -, -, hg, -⟩, -⟩ := h
  rw [h1, BitVec.toNat_ofNat]; omega

/-- the entry facts of `nat.expNNSlow` (asm's amd64 `ExpEven.EPre` layout, the `natOne` conjunct replaced by `True` (so asm's EvRel lemmas port
with the same projections); `bp` = the caller's `RBP`,
`r` = the return address) -/
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
  StkOK s.mem R L st ∧ Apart st 24 (sp - 8 - K) (K + 0x228) ∧ Apart st 24 (g + 16) 8 ∧ Apart st 24 (fs - 8) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - 8 - K) (K + 0x228) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8 ∧ Apart (stW s.mem st) (8 * stCap s.mem st) (fs - 8) 8) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (free s.mem st).1 (free s.mem st).2 ∧ st ≠ 0 ∧
  stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 ∧ True ∧
  (OE R L sp K st s.mem mp (8 * ml) ∧ s.mem.accessible mp (8 * ml) false = true ∧ mp + 8 * ml ≤ 2 ^ 48 ∧
    NatNorm s.mem mp ml ∧ (0 < zc → Apart zp (8 * zc) mp (8 * ml)) ∧ yp < 2 ^ 64 ∧ yc < 2 ^ 64 ∧ mp < 2 ^ 64 ∧
    mc < 2 ^ 64 ∧ (stCap s.mem st = 0 → stW s.mem st = 0)) ∧
  ((s.regs 5).toNat = bp ∧ s.mem.readLE (sp + 0x1b0) 8 = r ∧ r < 2 ^ 47 ∧
    s.mem.readLE (sp + 0x1b8) 8 = yp ∧ s.mem.readLE (sp + 0x1c0) 8 = yl ∧ s.mem.readLE (sp + 0x1c8) 8 = yc ∧
    s.mem.readLE (sp + 0x1d0) 8 = mp ∧ s.mem.readLE (sp + 0x1d8) 8 = ml ∧ s.mem.readLE (sp + 0x1e0) 8 = mc) ∧
  R.inv b L g (view R.rt L s.mem)

/-- the array at a later point: kept or fresh -/
@[reducible] def ArrKF (R : RtInv) (L : List (Nat × Nat)) (st : Nat) (M0 M : Memory) : Prop :=
  (stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)

/-- the frame slots constant after the prologue (saved `BP`, return address, stack arguments, register spills) -/
@[reducible] def ESl (M : Memory) (sp st bp r zp xp xl xc yp yl yc mp ml mc : Nat) : Prop :=
  M.readLE (sp + 0x1a8) 8 = bp ∧ M.readLE (sp + 0x1b0) 8 = r ∧
  M.readLE (sp + 0x1b8) 8 = yp ∧ M.readLE (sp + 0x1c0) 8 = yl ∧ M.readLE (sp + 0x1c8) 8 = yc ∧
  M.readLE (sp + 0x1d0) 8 = mp ∧ M.readLE (sp + 0x1d8) 8 = ml ∧ M.readLE (sp + 0x1e0) 8 = mc ∧
  M.readLE (sp + 0x1e8) 8 = zp ∧ M.readLE (sp + 0x200) 8 = st ∧
  M.readLE (sp + 0x208) 8 = xp ∧ M.readLE (sp + 0x210) 8 = xl ∧ M.readLE (sp + 0x218) 8 = xc

/-- the slot range of `ESl` -/
@[reducible] def SlotR (sp a k : Nat) : Prop := sp + 0x1a8 ≤ a ∧ a + k ≤ sp + 0x220

theorem ESl.keep {M1 M3 : Memory} {sp st bp r zp xp xl xc yp yl yc mp ml mc : Nat}
    (h : ESl M1 sp st bp r zp xp xl xc yp yl yc mp ml mc)
    (hk : ∀ a k, SlotR sp a k → M3.readLE a k = M1.readLE a k) :
    ESl M3 sp st bp r zp xp xl xc yp yl yc mp ml mc := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  exact ⟨(hk _ _ (by omega)).trans a1, (hk _ _ (by omega)).trans a2, (hk _ _ (by omega)).trans a3,
    (hk _ _ (by omega)).trans a4, (hk _ _ (by omega)).trans a5, (hk _ _ (by omega)).trans a6,
    (hk _ _ (by omega)).trans a7, (hk _ _ (by omega)).trans a8, (hk _ _ (by omega)).trans a9,
    (hk _ _ (by omega)).trans a10, (hk _ _ (by omega)).trans a11, (hk _ _ (by omega)).trans a12,
    (hk _ _ (by omega)).trans a13⟩

end FvModexp.Amd64.ExpSlow
