import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.NHyp

set_option autoImplicit false

/-!
# `nat.expNNSlow` (go-bigmodexpfix nat.go:732-787), arm64 — code map and the internal entry facts `EPre`

Entry `0x1b49c0 = 1788352` (`Extracted.seg20`), args `z` X0..X2, `stk` X3, `x` X4..X6, `y` X7..X9, `m` X10..X12.
Frame: guard `SUB $304` (`morestack` iff `SP - 304 ≤ stackguard`), `SUB $432` → `sp = SP - 432`, saved FP at `sp - 8`,
LR at `sp`. Argument spills (caller area, `above = 112`): `z.ptr` 440, `stk` 464, `x` 472/480/488, `y` 496/504,
`m` 520/528/536. No defer, no write barrier. Window `[sp - K, sp + 544)` (`= [SP - (K + 432), SP + 112)`).
`EPre`: the conjunct LAYOUT of infra's `ExpEven.EPre` (EvPre.lean, copied with the frame constants; position 32 =
the stack bound `stLen + 2^13 ≤ 2^16`, 33 = `True` (no `natOne`), 34's capacity slot `mc < 2^64`).

Code map (offsets from `fnE`):
* `z = z.set(x)` (inline `make`: reuse when `len x ≤ cap z` (0x4c); `len x = 1` → `makeslice(1,1)` (ret 0x78);
  else `makeslice(len x, len x + 4)` (ret 0xc0); 0xec: `memmove` unless same pointer (ret 0x114)).
* 0x144: `v = y[len y - 1]`, `shift = nlz(v) + 1`, `v <<= shift` (0 if `shift = 64`), `w = 64 - shift` (152);
  zz, r, q := nil → top-loop test `T1` (0x208, `CMP R14, R13`: `j < w`).
* Loop state at both tests: `z = (R0, R5, R2)`, `zz = (R24, R23, R22)`, `r = (R20, R15, R19)`, `q = (R21, R17, R16)`,
  `j = R13`, `v = R9`. Top body: `zz.sqr(stk, z)` (ret 0x254), `v < 0` → `zz.mul(stk, z, x)` (ret 0x2a4),
  `len m ≠ 0` → `zz.div(stk, r, z, m)` (ret 0x31c); back at 0x1a4 → `T1`.
* `T1` exit (0x358): `i = len y - 2` → 0x364 (`TBNZ $63, i` → exit 0x528); `v = y[i]` → lower test `T2` (0x3d8,
  `j < 64`), body sqr (ret 0x424) / mul (ret 0x474) / div (ret 0x4ec), back at 0x378; exit 0x360 (`i--`) → 0x364.
* exit 0x528: `return z.norm()`, `RET` (0x558).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNSlow"
theorem fnBase : segAddr LibW.program fn = 1788352 := by decide
theorem fn_eq : fn = NHyp.fnSlow := rfl

/-- the function's entry -/
abbrev fnE : Nat := 1788352
/-- the loop tests -/
abbrev t1 : Nat := fnE + 0x208
abbrev t2 : Nat := fnE + 0x3d8
/-- the exit (`z.norm()`) -/
abbrev ex : Nat := fnE + 0x528
/-- the call return points -/
abbrev mk1R : Nat := fnE + 0x78
abbrev mk2R : Nat := fnE + 0xc0
abbrev mvR : Nat := fnE + 0x114
abbrev sq1R : Nat := fnE + 0x254
abbrev ml1R : Nat := fnE + 0x2a4
abbrev dv1R : Nat := fnE + 0x31c
abbrev sq2R : Nat := fnE + 0x424
abbrev ml2R : Nat := fnE + 0x474
abbrev dv2R : Nat := fnE + 0x4ec

/-- the need of the exported shape: `2^13` stack words when `len x, len m ≤ 128` (the call site's bounds; the loop's
`div` operands have `≤ 3·128 ≤ 2^9` words), else unsatisfiable (`2^16 + 1`) — the bounds enter through `CPre`'s
`stLen + need ≤ 2^16` -/
@[reducible] def need (xl _yl ml : Nat) : Nat := if xl ≤ 128 ∧ ml ≤ 128 then 2 ^ 13 else 2 ^ 16 + 1

/-- the free part of the stack's array -/
@[reducible] def free (M : Memory) (st : Nat) : Nat × Nat := (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- an object at the entry: held, apart from the window, the stack header and the stack's free part -/
@[reducible] def OE (R : RtInv) (L : List (Nat × Nat)) (sp K st : Nat) (M : Memory) (a k : Nat) : Prop :=
  (InRanges a k L ∨ Outside a k R.rt) ∧ Apart a k (sp - K) (K + 544) ∧ Apart a k st 24 ∧
    Apart a k (free M st).1 (free M st).2

/-- the call environment of the entry (entry state `s`, frame `sp = SP(s) - 432`, window `[sp - K, sp + 544)`) -/
@[reducible] def EEnv (R : RtInv) (L : List (Nat × Nat)) (g sp K : Nat) (s : State) : Prop :=
  s.sp = BitVec.ofNat 64 (sp + 432) ∧ s.regs 28 = BitVec.ofNat 64 g ∧
  g + 24 ≤ 2 ^ 48 ∧ s.mem.accessible (g + 16) 8 false = true ∧ s.mem.readLE (g + 16) 8 + K < sp ∧
  Outside (g + 16) 8 ((sp - K, sp + 544) :: R.rt) ∧ sp % 16 = 0 ∧ 4304 ≤ K ∧ K ≤ sp ∧ sp + 544 ≤ 2 ^ 48 ∧
  s.mem.accessible (sp - K) (K + 544) true = true ∧ LiveSep [(sp - K, sp + 544)] R.rt ∧
  LiveSep L [(sp - K, sp + 544)] ∧ Extracted.program.DataLoaded s.mem ∧ RunIface.Serves R

theorem EEnv.sp {R : RtInv} {L : List (Nat × Nat)} {g sp K : Nat} {s : State} (h : EEnv R L g sp K s) :
    s.sp.toNat = sp + 432 := by
  rw [h.1, BitVec.toNat_ofNat]; have := h.2.2.2.2.2.2.2.2.2.1; omega

theorem EEnv.g {R : RtInv} {L : List (Nat × Nat)} {g sp K : Nat} {s : State} (h : EEnv R L g sp K s) :
    (s.regs 28).toNat = g := by
  rw [h.2.1, BitVec.toNat_ofNat]; have := h.2.2.1; omega

/-- the entry facts of `nat.expNNSlow` (layout: see the module doc) -/
def EPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) : Prop :=
  EEnv R L g sp K s ∧ K ≤ 2 ^ 20 ∧ RunIface.Globals R s.mem [(sp - K, sp + 544)] ∧ RoOut R ∧
  Outside StackNat.wT 16 R.rt ∧ 0 < ml ∧ ml ≤ 128 ∧
  OE R L sp K st s.mem yp (8 * yl) ∧ s.mem.accessible yp (8 * yl) false = true ∧ yp + 8 * yl ≤ 2 ^ 48 ∧
    NatNorm s.mem yp yl ∧ 0 < yl ∧ yl ≤ 2 ^ 9 ∧
  OE R L sp K st s.mem xp (8 * xl) ∧ s.mem.accessible xp (8 * xl) false = true ∧ xp + 8 * xl ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ xl ≤ 128 ∧ xp < 2 ^ 64 ∧ xc < 2 ^ 64 ∧
  zp < 2 ^ 64 ∧ zc < 2 ^ 40 ∧ (0 < zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart zp (8 * zc) xp (8 * xl) ∧ Apart zp (8 * zc) yp (8 * yl) ∧ Apart zp (8 * zc) RunIface.gA 32) ∧
  OE R L sp K st s.mem RunIface.gA 32 ∧
  StkOK s.mem R L st ∧ Apart st 24 (sp - K) (K + 544) ∧ Apart st 24 (g + 16) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - K) (K + 544) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8) ∧
  s.mem.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧
  Apart st 24 (free s.mem st).1 (free s.mem st).2 ∧ st ≠ 0 ∧
  stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 ∧ True ∧
  (OE R L sp K st s.mem mp (8 * ml) ∧ s.mem.accessible mp (8 * ml) false = true ∧ mp + 8 * ml ≤ 2 ^ 48 ∧
    NatNorm s.mem mp ml ∧ (0 < zc → Apart zp (8 * zc) mp (8 * ml)) ∧ yp < 2 ^ 64 ∧ yc < 2 ^ 64 ∧ mp < 2 ^ 64 ∧
    mc < 2 ^ 64 ∧ (stCap s.mem st = 0 → stW s.mem st = 0)) ∧
  R.inv b L g (view R.rt L s.mem)

/-- the array at a later point: kept or fresh -/
@[reducible] def ArrKF (R : RtInv) (L : List (Nat × Nat)) (st : Nat) (M0 M : Memory) : Prop :=
  (stW M st = stW M0 st ∧ stCap M st = stCap M0 st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)

end FvModexp.Arm64.ExpSlow
