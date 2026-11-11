import FvModexp.Proofs.Arm64.Nat.LibTrunc
import FvModexp.Proofs.Arm64.Nat.NatAddMid
import FvModexp.Proofs.Arm64.Exp.EvenHyp

/-!
# `nat.trunc` (go-bigmodexpfix nat.go:530), arm64: statement and segment-boundary facts

```go
func (z nat) trunc(x nat, n uint) nat {
	w := (n + _W - 1) / _W
	if uint(len(x)) < w {
		return z.set(x)          // z = z.make(len(x)); copy(z, x); return z
	}
	z = z.make(int(w))
	copy(z, x)
	if n%_W != 0 {
		z[len(z)-1] &= 1<<(n%_W) - 1
	}
	return z.norm()
}
```
(`make`, `set`, `norm` inlined.) Arguments `R0..R2 = z`, `R3..R5 = x`, `R6 = n`. Frame 112 (`MOVD.W R30, -112(RSP)`;
entry `SP`, `SP' = SP - 112`): saved `X30` at `SP - 112`, `X29` at `SP - 120`; spills `120, 144, 152, 168(RSP')` =
`SP + 8, 32, 40, 56` (`above = 64`); locals `SP - 72 … SP - 16`. Calls `runtime.makeslice` (`make(nat, w, w + 4)` /
`make(nat, 1)`) and `runtime.memmove` (`copy`, skipped when the pointers agree), contract stack 4096 below `SP'`:
`stk = 112 + 4096 = 4208`.

The statement is infra's `EvenHyp.TruncPre`/`TruncPost` (window 4208/64) with two more precondition facts the code
forces:
* `NatNorm x ∨ ⌈n/64⌉ ≤ len x`: `z.set(x)` (the `len(x) < w` path) copies `x` without normalising it (infra s9:
  the weaker disjunction, since the main path normalises itself);
* `zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n)`: when `min(len x, w) = 0` Go's `copy` still calls `memmove(z, x, 0)` unless the
  pointers agree, and Janus v0.2.0's `MemmoveLive` needs the (empty) destination inside a mapped region — true for a
  `z` with an array (`0 < zc`), not for an arbitrary `nil` pointer (JANUS-ISSUES "[asm s6] memmove n = 0"; lifted by
  `MemmoveZeroLive` in Janus v0.3.1).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)
open FvModexp.Arm64.RunIface (Serves)

namespace FvModexp.Arm64.Trunc

def fn : String := EvenHyp.fnTrunc
def names : List String := LibTrunc.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- `w = ⌈n / 64⌉` -/
@[reducible] def wOf (n : Nat) : Nat := (n + 63) / 64

/-- The precondition: infra's `TruncPre` (window `4208 / 64`) and the two code-forced facts. -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl n : Nat) (s : State) : Prop :=
  EvenHyp.TruncPre R b L 4208 64 zp zl zc x xl n s ∧ (NatNorm s.mem x xl ∨ wOf n ≤ xl) ∧ (zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n))

/-- The postcondition: infra's `TruncPost` (window `4208 / 64`). -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl n : Nat) (s s' : State) : Prop :=
  EvenHyp.TruncPost R b L 4208 64 zp zc x xl n s s'

/-- The premise shape `EvenHyp.TruncHyp` with the amended precondition. -/
def Hyp2 (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc n : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, x, xl, xc, n]
      (fun s => EvenHyp.TruncPre R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat n.toNat s ∧
        (NatNorm s.mem x.toNat xl.toNat ∨ (n.toNat + 63) / 64 ≤ xl.toNat) ∧ (z.toNat = x.toNat ∨ 0 < zc.toNat ∨ (0 < xl.toNat ∧ 0 < n.toNat)))
      (fun s s' => EvenHyp.TruncPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat n.toNat s s')

/-- The segment-boundary facts after the result array `(p, c)` of `z.make(k)` is chosen (`0 < c`). -/
structure Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc x xl n : Nat) (s : State)
    (k p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory) : Prop where
  gok : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4208 < s.sp.toNat
  g48 : (s.regs 28).toNat + 24 ≤ 2 ^ 48
  al : s.sp.toNat % 16 = 0
  sp0 : 4208 ≤ s.sp.toNat
  sp1 : s.sp.toNat + 64 ≤ 2 ^ 48
  wrt : Outside (s.sp.toNat - 4208) (4208 + 64) R.rt
  gw : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4208) (4208 + 64)
  grt : Outside ((s.regs 28).toNat + 16) 8 R.rt
  lr4 : (s.regs 30).toNat % 4 = 0
  lr48 : (s.regs 30).toNat < 2 ^ 48
  xl16 : xl ≤ 2 ^ 16
  kx : k ≤ xl
  lr : M.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat
  sn : k = wOf n → M.readLE (s.sp.toNat + 56) 8 = n
  sacc : M.accessible (s.sp.toNat - 4208) (4208 + 64) true = true
  gacc : M.accessible ((s.regs 28).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8
  c0 : 0 < c
  cap : k ≤ c
  c40 : c < 2 ^ 40
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) (s.sp.toNat - 4208) (4208 + 64)
  pg : Apart p (8 * c) ((s.regs 28).toNat + 16) 8
  pheld : Held R L' p (8 * c)
  px : 0 < k → p = x ∨ Apart p (8 * c) x (8 * xl)
  xacc : M.accessible x (8 * xl) false = true
  x48 : x + 8 * xl ≤ 2 ^ 48
  xw : Outside x (8 * xl) (win s 4208 64)
  xr : ∀ a k, x ≤ a → a + k ≤ x + 8 * xl → M.readLE a k = s.mem.readLE a k
  ext : LiveExt R L L'
  bud : b - makeCost k ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M)
  lsep : LiveSep L' (win s 4208 64)
  ru : k ≤ zc → p = zp ∧ c = zc
  ror : (p = zp ∧ c = zc) ∨ (zc < k ∧ k ≤ c ∧ InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ winA s 4208 64 ++ [(zp, zp + 8 * zc)])
  lf : LiveFrame s.mem M L [(zp, zp + 8 * zc)]
  sv : Serves R

/-- The ranges written after `Mid`: the window except the saved `X29`/`X30`, and the result array. -/
@[reducible] def ws (s : State) (p c : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - 4208, s.sp.toNat - 120), (s.sp.toNat - 104, s.sp.toNat - 8), (p, p + 8 * c)]

/-- **The postcondition from `Mid`** and the final memory `M'` (`M` changed in `ws`), given the result `(p, l', c)`. -/
theorem Mid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc x xl n : Nat} {s : State}
    {k p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M' : Memory}
    (h : Mid R b L zp zc x xl n s k p c L' b' M) (hk : k = EvenHyp.truncNeed xl n)
    (hF : MemFrame M M' (R.rt ++ ws s p c)) (hLF : LiveFrame M M' L' [(p, p + 8 * c)])
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M'))
    (s' : State) (l' : Nat) (hm : s'.mem = M') (h0 : s'.regs 0 = BitVec.ofNat 64 p)
    (h1 : s'.regs 1 = BitVec.ofNat 64 l') (h2 : s'.regs 2 = BitVec.ofNat 64 c) (hl : l' ≤ c)
    (hv : natVal M' p l' = natVal s.mem x xl % 2 ^ n) (hn : NatNorm M' p l') :
    Post R b L zp zc x xl n s s' := by
  subst hm hk
  have hpw := h.pw; have hsp0 := h.sp0; have hcap := h.cap; have hc0 := h.c0
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

end FvModexp.Arm64.Trunc
