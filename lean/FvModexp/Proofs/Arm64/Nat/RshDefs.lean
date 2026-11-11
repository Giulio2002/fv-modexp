import FvModexp.Proofs.Arm64.Nat.LibRsh
import FvModexp.Proofs.Arm64.Nat.NatAddMid
import FvModexp.Proofs.Arm64.Exp.MulHyp

/-!
# `nat.rsh` (go-bigmodexpfix nat.go:425), arm64: statement and segment-boundary facts

```go
func (z nat) rsh(x nat, s uint) nat {
	if s == 0 { if same(z, x) { return z }; if !alias(z, x) { return z.set(x) } }
	m := len(x)
	n := m - int(s/_W)
	if n <= 0 { return z[:0] }
	z = z.make(n)
	if s %= _W; s == 0 { copy(z, x[m-n:]) } else { rshVU(z, x[m-n:], s) }
	return z.norm()
}
```
(`make`, `set`, `norm`, `same`, `alias` inlined.) Arguments `R0..R2 = z`, `R3..R5 = x`, `R6 = s`. Frame 144
(`MOVD.W R30, -144(RSP)`; entry `SP`, `SP' = SP - 144`): saved `X30` at `SP - 144`, `X29` at `SP - 152`; spills
`SP + 8, 32, 40, 48, 56` (`above = 64`); locals `SP - 88 … SP - 16`; `rshVU.abi0` frame arguments `8 … 64(RSP')`.
Calls `runtime.makeslice` (`make(nat, n, n + 4)` / `make(nat, 1)`), `runtime.memmove` (`copy`, skipped when the
pointers agree), `rshVU.abi0`; contract stack 4096 below `SP'`: `stk = 144 + 4096 = 4240`.

The statement (asm's shape, NOTES-conventions "[asm s11]"/"[asm s12]"): `z` apart from `x` (no alias), `x`
normalised and non-empty (`len x = 0` with `s = 0` would `memmove(z, x, 0)` to a possibly unmapped `z`, see trunc);
`s = 0` only with `cap z = 0` (nat.go:952 `nat(nil).rsh(x, i)`; then `same`/`alias` are false and `z.set(x)` runs).
Result `X / 2^s` normalised, need `len x - s/64` words (`NatRes` + fresh capacity `≥ need`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)
open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.ExpHyp (RdIn WrOut NatRes RtPost)

namespace FvModexp.Arm64.Rsh

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.rsh"
def names : List String := LibRsh.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- `n = len x - s / 64` (as a natural number; `≤ 0` means the result is empty) -/
@[reducible] def need (xl sh : Nat) : Nat := xl - sh / 64

@[reducible] def RshPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl sh : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ WrOut R L s stk above zp zc ∧ RdIn R L s stk above x xl ∧
    xl ≤ 2 ^ 16 ∧ (0 < zc → Apart zp (8 * zc) x (8 * xl)) ∧ NatNorm s.mem x xl ∧ 0 < xl ∧ (0 < sh ∨ zc = 0) ∧
    makeCost (need xl sh) ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

@[reducible] def RshPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc x xl sh : Nat) (s s' : State) :
    Prop :=
  ∃ (p' l' c' : Nat), s'.regs 0 = BitVec.ofNat 64 p' ∧ s'.regs 1 = BitVec.ofNat 64 l' ∧ s'.regs 2 = BitVec.ofNat 64 c' ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat),
      NatRes R L L' s'.mem zp zc (need xl sh) p' l' c' (natVal s.mem x xl / 2 ^ sh) ∧
      (zc < need xl sh → need xl sh ≤ c') ∧
      RtPost R b (makeCost (need xl sh)) L L' b' s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk above ++ [(zp, zp + 8 * zc)]) ∧
      LiveFrame s.mem s'.mem L [(zp, zp + 8 * zc)]

/-- **The premise shape of `z.rsh(x, s)`** (`z` X0..X2, `x` X3..X5, `s` X6). -/
def Hyp (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc sh : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn) [z, zl, zc, x, xl, xc, sh]
      (fun s => RshPre R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat sh.toNat s)
      (fun s s' => RshPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat sh.toNat s s')

@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl sh : Nat) (s : State) : Prop :=
  RshPre R b L 4240 64 zp zl zc x xl sh s

@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat) (s s' : State) : Prop :=
  RshPost R b L 4240 64 zp zc x xl sh s s'

/-- The segment-boundary facts after the result array `(p, c)` of `z.make(n)` is chosen (`0 < n`). -/
structure Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory) : Prop where
  gok : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4240 < s.sp.toNat
  g48 : (s.regs 28).toNat + 24 ≤ 2 ^ 48
  al : s.sp.toNat % 16 = 0
  sp0 : 4240 ≤ s.sp.toNat
  sp1 : s.sp.toNat + 64 ≤ 2 ^ 48
  wrt : Outside (s.sp.toNat - 4240) (4240 + 64) R.rt
  gw : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4240) (4240 + 64)
  grt : Outside ((s.regs 28).toNat + 16) 8 R.rt
  lr4 : (s.regs 30).toNat % 4 = 0
  lr48 : (s.regs 30).toNat < 2 ^ 48
  xl16 : xl ≤ 2 ^ 16
  xl0 : 0 < need xl sh
  lr : M.readLE (s.sp.toNat - 144) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 152) 8 = (s.regs 29).toNat
  sacc : M.accessible (s.sp.toNat - 4240) (4240 + 64) true = true
  gacc : M.accessible ((s.regs 28).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8
  cap : need xl sh ≤ c
  c40 : c < 2 ^ 40
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) (s.sp.toNat - 4240) (4240 + 64)
  pg : Apart p (8 * c) ((s.regs 28).toNat + 16) 8
  pheld : Held R L' p (8 * c)
  px : Apart p (8 * c) x (8 * xl)
  xacc : M.accessible x (8 * xl) false = true
  x48 : x + 8 * xl ≤ 2 ^ 48
  xw : Outside x (8 * xl) (win s 4240 64)
  xr : ∀ a k, x ≤ a → a + k ≤ x + 8 * xl → M.readLE a k = s.mem.readLE a k
  ext : LiveExt R L L'
  bud : b - makeCost (need xl sh) ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M)
  lsep : LiveSep L' (win s 4240 64)
  ru : need xl sh ≤ zc → p = zp ∧ c = zc
  ror : (p = zp ∧ c = zc) ∨ (zc < need xl sh ∧ need xl sh ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ winA s 4240 64 ++ [(zp, zp + 8 * zc)])
  lf : LiveFrame s.mem M L [(zp, zp + 8 * zc)]
  sv : Serves R

/-- The ranges written after `Mid`: the window except the saved `X29`/`X30`, and the result array. -/
@[reducible] def ws (s : State) (p c : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - 4240, s.sp.toNat - 152), (s.sp.toNat - 136, s.sp.toNat - 8), (p, p + 8 * c)]

/-- **The postcondition from `Mid`** and the final memory `M'` (`M` changed in `ws`), given the result `(p, l', c)`. -/
theorem Mid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M' : Memory}
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (hF : MemFrame M M' (R.rt ++ ws s p c)) (hLF : LiveFrame M M' L' [(p, p + 8 * c)])
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M'))
    (s' : State) (l' : Nat) (hm : s'.mem = M') (h0 : s'.regs 0 = BitVec.ofNat 64 p)
    (h1 : s'.regs 1 = BitVec.ofNat 64 l') (h2 : s'.regs 2 = BitVec.ofNat 64 c) (hl : l' ≤ c)
    (hv : natVal M' p l' = natVal s.mem x xl / 2 ^ sh) (hn : NatNorm M' p l') :
    Post R b L zp zc x xl sh s s' := by
  subst hm
  have hpw := h.pw; have hsp0 := h.sp0; have hcap := h.cap
  unfold Apart at hpw
  refine ⟨p, l', c, h0, h1, h2, L', b', ⟨hv, hn, hl, h.c40, fun _ => ⟨h.p8, h.pheld, ?_, h.p48⟩, h.ru, ?_⟩, ?_,
    ⟨h.ext, h.bud, hinv⟩, ?_, ?_⟩
  · rw [hF.accessible]; exact h.pacc
  · intro hz _
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, -, hin, hap⟩
    · omega
    · exact ⟨hin, hap⟩
  · intro hz
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hkc, -, -⟩
    · omega
    · exact hkc
  · refine h.mf.trans hF fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, winA, ws, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1, hw2⟩, hz⟩ := ho
    refine ⟨hrt, by omega, by omega, ?_⟩
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, -, hin, -⟩
    · omega
    · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hLF.readLE a n (h.ext.inRanges_old hin) ?_]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      simp only [outside_cons, outside_nil, and_true] at hz ⊢
      rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, -, -, hap⟩
      · omega
      · have := hap q hq; unfold Apart at this; omega

end FvModexp.Arm64.Rsh
