import FvModexp.Proofs.Arm64.Nat.LibLsh
import FvModexp.Proofs.Arm64.Nat.NatAddMid
import FvModexp.Proofs.Arm64.Exp.MulHyp

/-!
# `nat.lsh` (go-bigmodexpfix nat.go:395), arm64: statement and segment-boundary facts

```go
func (z nat) lsh(x nat, s uint) nat {
	if s == 0 { if same(z, x) { return z }; if !alias(z, x) { return z.set(x) } }
	m := len(x)
	if m == 0 { return z[:0] }
	n := m + int(s/_W)
	z = z.make(n + 1)
	if s %= _W; s == 0 { copy(z[n-m:n], x); z[n] = 0 } else { z[n] = lshVU(z[n-m:n], x, s) }
	clear(z[0 : n-m])
	return z.norm()
}
```
(`make`, `norm`, `same`, `alias` inlined.) Arguments `R0..R2 = z`, `R3..R5 = x`, `R6 = s`. Frame 160
(`MOVD.W R30, -160(RSP)`; entry `SP`, `SP' = SP - 160`): saved `X30` at `SP - 160`, `X29` at `SP - 168`; spills
`168, 192, 200, 208, 216(RSP')` = `SP + 8, 32, 40, 48, 56` (`above = 64`); locals `SP - 80 … SP - 16`; `lshVU.abi0`
frame arguments `8 … 64(RSP')`. Calls `runtime.makeslice` (`make(nat, n + 1, n + 5)`), `runtime.memmove` (`copy`,
skipped when the pointers agree), `lshVU.abi0`, `runtime.memclrNoHeapPointers` (`clear`, skipped when `s/64 = 0`),
contract stack 4096 below `SP'`: `stk = 160 + 4096 = 4256`.

The statement (`ens`) is infra's `EvenHyp.LshPreA` / expmc's `ExpHyp.LshPost` (window 4256/64; `z = x` allowed) with
the code-forced precondition `0 < s ∧ 0 < len x` (the `s = 0` and `len x = 0` paths return `z` itself or `z[:0]`,
reusing `z` although `cap z < need`); `ensZ` covers `z.lsh(z, s)` with `s = 0` allowed (nat.go:955).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)
open FvModexp.Arm64.RunIface (Serves)

namespace FvModexp.Arm64.Lsh

def fn : String := ExpHyp.fnLsh
def names : List String := LibLsh.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- `n + 1` with `n = len x + s / 64`: the capacity `z.make(n + 1)` asks for -/
@[reducible] def need (xl sh : Nat) : Nat := xl + sh / 64 + 1

/-- The precondition: `EvenHyp.LshPreA` (window `4256 / 64`) and `0 < s ∧ 0 < len x`. -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl sh : Nat) (s : State) : Prop :=
  EvenHyp.LshPreA R b L 4256 64 zp zl zc x xl sh s ∧ 0 < sh ∧ 0 < xl

/-- The postcondition: expmc's `ExpHyp.LshPost` (window `4256 / 64`). -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat) (s s' : State) : Prop :=
  ExpHyp.LshPost R b L 4256 64 zp zc x xl sh s s'

/-- The premise shape `EvenHyp.LshHypA` with the amended precondition. -/
def Hyp2 (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc sh : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn) [z, zl, zc, x, xl, xc, sh]
      (fun s => EvenHyp.LshPreA R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat sh.toNat s ∧
        0 < sh.toNat ∧ 0 < xl.toNat)
      (fun s s' => ExpHyp.LshPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat sh.toNat s s')

/-- The segment-boundary facts after the result array `(p, c)` of `z.make(n + 1)` is chosen. -/
structure Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory) : Prop where
  gok : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4256 < s.sp.toNat
  g48 : (s.regs 28).toNat + 24 ≤ 2 ^ 48
  al : s.sp.toNat % 16 = 0
  sp0 : 4256 ≤ s.sp.toNat
  sp1 : s.sp.toNat + 64 ≤ 2 ^ 48
  wrt : Outside (s.sp.toNat - 4256) (4256 + 64) R.rt
  gw : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4256) (4256 + 64)
  grt : Outside ((s.regs 28).toNat + 16) 8 R.rt
  lr4 : (s.regs 30).toNat % 4 = 0
  lr48 : (s.regs 30).toNat < 2 ^ 48
  n16 : need xl sh ≤ 2 ^ 16
  xl0 : 0 < xl
  sh0 : 0 < sh
  lr : M.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat
  ssh : M.readLE (s.sp.toNat + 56) 8 = sh
  sn : M.readLE (s.sp.toNat - 40) 8 = xl + sh / 64
  sn1 : M.readLE (s.sp.toNat - 48) 8 = need xl sh
  sacc : M.accessible (s.sp.toNat - 4256) (4256 + 64) true = true
  gacc : M.accessible ((s.regs 28).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8
  cap : need xl sh ≤ c
  c40 : c < 2 ^ 40
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) (s.sp.toNat - 4256) (4256 + 64)
  pg : Apart p (8 * c) ((s.regs 28).toNat + 16) 8
  pheld : Held R L' p (8 * c)
  px : p = x ∨ Apart p (8 * c) x (8 * xl)
  xacc : M.accessible x (8 * xl) false = true
  x48 : x + 8 * xl ≤ 2 ^ 48
  xw : Outside x (8 * xl) (win s 4256 64)
  xr : ∀ a k, x ≤ a → a + k ≤ x + 8 * xl → M.readLE a k = s.mem.readLE a k
  ext : LiveExt R L L'
  bud : b - makeCost (need xl sh) ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M)
  lsep : LiveSep L' (win s 4256 64)
  ru : need xl sh ≤ zc → p = zp ∧ c = zc
  ror : (p = zp ∧ c = zc) ∨ (zc < need xl sh ∧ need xl sh ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ winA s 4256 64 ++ [(zp, zp + 8 * zc)])
  lf : LiveFrame s.mem M L [(zp, zp + 8 * zc)]
  sv : Serves R

/-- The ranges written after `Mid`: the window except the saved `X29`/`X30`, and the result array. -/
@[reducible] def ws (s : State) (p c : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - 4256, s.sp.toNat - 168), (s.sp.toNat - 152, s.sp.toNat - 8), (p, p + 8 * c)]

/-- **The postcondition from `Mid`** and the final memory `M'` (`M` changed in `ws`), given the result `(p, l', c)`. -/
theorem Mid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl sh : Nat} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M' : Memory}
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (hF : MemFrame M M' (R.rt ++ ws s p c)) (hLF : LiveFrame M M' L' [(p, p + 8 * c)])
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M'))
    (s' : State) (l' : Nat) (hm : s'.mem = M') (h0 : s'.regs 0 = BitVec.ofNat 64 p)
    (h1 : s'.regs 1 = BitVec.ofNat 64 l') (h2 : s'.regs 2 = BitVec.ofNat 64 c) (hl : l' ≤ c)
    (hv : natVal M' p l' = natVal s.mem x xl * 2 ^ sh) (hn : NatNorm M' p l') :
    Post R b L zp zc x xl sh s s' := by
  subst hm
  have hpw := h.pw; have hsp0 := h.sp0; have hcap := h.cap
  unfold Apart at hpw
  refine ⟨p, l', c, h0, h1, h2, L', b', ⟨hv, hn, hl, h.c40, fun _ => ⟨h.p8, h.pheld, ?_, h.p48⟩, h.ru, ?_⟩, ?_,
    ⟨h.ext, h.bud, hinv⟩, ?_, ?_⟩
  · rw [hF.accessible]; exact h.pacc
  · intro hz _
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, -, hin, hap⟩
    · simp only [need] at hcap; omega
    · exact ⟨hin, hap⟩
  · intro hz
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hkc, -, -⟩
    · simp only [need] at hcap; omega
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

end FvModexp.Arm64.Lsh
