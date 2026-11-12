import FvModexp.Proofs.Arm64.Int.LibIntAS
import FvModexp.Proofs.Arm64.Nat.NatAdd
import FvModexp.Proofs.Arm64.Nat.NatSub
import FvModexp.Proofs.Arm64.Nat.DivmcCall
import FvModexp.Proofs.Arm64.CmpSum
import FvModexp.Proofs.Arm64.Top.RunIface
import FvModexp.Proofs.Common.SubMod2NMath

/-!
# `(*Int).Add` / `(*Int).Sub` (go-bigmodexpfix int.go:141 / int.go:162), arm64 — statement and shared lemmas

```go
func (z *Int) Sub(x, y *Int) *Int {              // Add: the same with `x.neg == y.neg` in the first test
	neg := x.neg
	if x.neg != y.neg {
		z.abs = z.abs.add(x.abs, y.abs)
	} else {
		if x.abs.cmp(y.abs) >= 0 {
			z.abs = z.abs.sub(x.abs, y.abs)
		} else {
			neg = !neg
			z.abs = z.abs.sub(y.abs, x.abs)
		}
	}
	z.neg = len(z.abs) > 0 && neg // 0 has no sign
	return z
}
```
The two functions are the same machine code (`Add` at `0x1b0910`, `Sub` at `0x1b0ab0`, every offset equal) except for
the first branch (`TBNZ`/`TBZ $0` on `x.neg ^ y.neg`). `sub : Bool` selects the function. Frame 96
(`MOVD.W R30, -96(RSP)`), spills `z` at `SP + 8`, `x`/`y` at `SP + 16`/`SP + 24` (`above = 32`), `neg` at `SP - 9`; the
deepest callee is `nat.add` (window 4464) at `SP - 96`: `stk = 4560`. The store `z.abs = …` is a pointer store into
the header: write barrier (`runtime.writeBarrier` flag, `gcWriteBarrier2`). `*Int` header: `neg` byte at `+0`,
`abs = (ptr, len, cap)` at `+8, +16, +24`. Signs are general (`neg ∈ {0, 1}`): karatsuba's temporaries are negative.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.IntAS

open FvModexp.Arm64.RunIface (Serves)

def fnAdd : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Add"
def fnSub : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Sub"
def names : List String := LibIntAS.names

/-- the function (`sub = false`: `Add`, `true`: `Sub`) -/
def fn (sub : Bool) : String := if sub then fnSub else fnAdd

/-- the entry address of the function -/
def entry (sub : Bool) : Nat := if sub then 0x1b0ab0 else 0x1b0910

theorem entry_eq (sub : Bool) : segAddr Extracted.program (fn sub) = entry sub := by
  cases sub <;> decide

/-- `runtime.writeBarrier`'s flag word -/
abbrev wbA : Nat := Extracted.dataAddr.«runtime.writeBarrier»

/-! ## The `*Int` header -/

@[reducible] def hNeg (m : Memory) (a : Nat) : Nat := m.readLE a 1
@[reducible] def hP (m : Memory) (a : Nat) : Nat := m.readLE (a + 8) 8
@[reducible] def hL (m : Memory) (a : Nat) : Nat := m.readLE (a + 16) 8
@[reducible] def hC (m : Memory) (a : Nat) : Nat := m.readLE (a + 24) 8

/-- the signed value of the `*Int` at `a` (`neg = 0`: `|x|`, else `-|x|`) -/
def intZ (m : Memory) (a : Nat) : Int :=
  if hNeg m a = 0 then (natVal m (hP m a) (hL m a) : Int) else -(natVal m (hP m a) (hL m a) : Int)

/-- the result of `x + y` (`sub = false`) / `x - y` (`sub = true`) -/
def resZ (sub : Bool) (vx vy : Int) : Int := if sub then vx - vy else vx + vy

/-- the budget: `nat.add` or `nat.sub` (`makeCap 0 = 4 > makeCap 1`, hence the max) -/
def asCost (xl yl : Nat) : Nat := max (makeCost (if min xl yl = 0 then max xl yl else max xl yl + 1)) (makeCost (max xl yl))

/-- the capacity of `z.abs` that `nat.add` / `nat.sub` keep -/
def asNeed (xl yl : Nat) : Nat := if min xl yl = 0 then max xl yl else max xl yl + 1

/-- a read-only `*Int` operand: header readable outside the window, `neg ∈ {0, 1}`, `abs` normalised, readable,
held and outside the window -/
@[reducible] def OpR (R : RtInv) (L : List (Nat × Nat)) (s : State) (a : Nat) : Prop :=
  hNeg s.mem a ≤ 1 ∧ s.mem.accessible a 32 false = true ∧ a + 32 ≤ 2 ^ 48 ∧ Outside a 32 (win s 4560 32) ∧
    hL s.mem a ≤ hC s.mem a ∧ hC s.mem a < 2 ^ 40 ∧ hL s.mem a ≤ 2 ^ 16 ∧
    s.mem.accessible (hP s.mem a) (8 * hL s.mem a) false = true ∧ hP s.mem a + 8 * hL s.mem a ≤ 2 ^ 48 ∧
    Held R L (hP s.mem a) (8 * hL s.mem a) ∧ NatNorm s.mem (hP s.mem a) (hL s.mem a) ∧
    Outside (hP s.mem a) (8 * hL s.mem a) (win s 4560 32)

/-- The precondition (both functions; args `X0 = z`, `X1 = x`, `X2 = y`). `z` may be `x` (`z1.Add(z1, z0)`). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State) : Prop :=
  CallEnv R L s 4560 32 ∧ Serves R ∧ Outside NatAdd.wordT 16 R.rt ∧ OpR R L s x ∧ OpR R L s y ∧
    s.mem.accessible z 32 true = true ∧ z + 32 ≤ 2 ^ 48 ∧ Outside z 32 (win s 4560 32) ∧ Held R L z 32 ∧
    Apart z 32 ((s.regs 28).toNat + 16) 8 ∧ Apart z 32 wbA 4 ∧ (z = x ∨ Apart z 32 x 32) ∧ Apart z 32 y 32 ∧
    hC s.mem z < 2 ^ 40 ∧ NatLive s.mem R L (hP s.mem z) (hC s.mem z) ∧
    Outside (hP s.mem z) (8 * hC s.mem z) (win s 4560 32) ∧
    (0 < hC s.mem z → Apart (hP s.mem z) (8 * hC s.mem z) ((s.regs 28).toNat + 16) 8 ∧
      Apart (hP s.mem z) (8 * hC s.mem z) z 32 ∧
      (hP s.mem z = hP s.mem x ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem x) (8 * hL s.mem x)) ∧
      (hP s.mem z = hP s.mem y ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem y) (8 * hL s.mem y))) ∧
    s.mem.accessible wbA 4 false = true ∧ asCost (hL s.mem x) (hL s.mem y) ≤ b ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- The postcondition: `z` (returned in `X0`) holds `x ± y` with a canonical sign (`neg ∈ {0,1}`, no sign for 0), a
normalised `abs` in `z`'s old array (always when its capacity suffices) or a fresh one; writes only `z`'s header, `z`'s
old array, `R.rt` and the window. -/
def Post (sub : Bool) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s s' : State) : Prop :=
  s'.regs 0 = BitVec.ofNat 64 z ∧ intZ s'.mem z = resZ sub (intZ s.mem x) (intZ s.mem y) ∧
    hNeg s'.mem z ≤ 1 ∧ (hNeg s'.mem z = 1 → 0 < hL s'.mem z) ∧ NatNorm s'.mem (hP s'.mem z) (hL s'.mem z) ∧
    hL s'.mem z ≤ hC s'.mem z ∧ hL s'.mem z ≤ max (hL s.mem x) (hL s.mem y) + 1 ∧ hC s'.mem z < 2 ^ 40 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - asCost (hL s.mem x) (hL s.mem y) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' (hP s'.mem z) (hC s'.mem z) ∧
      ((hP s'.mem z = hP s.mem z ∧ hC s'.mem z = hC s.mem z) ∨
        (InRanges (hP s'.mem z) (8 * hC s'.mem z) R.rt ∧ ApartAll (hP s'.mem z) (8 * hC s'.mem z) L)) ∧
      (asNeed (hL s.mem x) (hL s.mem y) ≤ hC s.mem z → hP s'.mem z = hP s.mem z ∧ hC s'.mem z = hC s.mem z) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4560 32 ++ [(z, z + 32), (hP s.mem z, hP s.mem z + 8 * min (max (hL s.mem x) (hL s.mem y) + 1) (hC s.mem z))]) ∧
      LiveFrame s.mem s'.mem L [(z, z + 32), (hP s.mem z, hP s.mem z + 8 * min (max (hL s.mem x) (hL s.mem y) + 1) (hC s.mem z))]

/-! ## Library-program plumbing -/

theorem sub_of_all {ns ms : List String} (h : ns.all ms.contains = true) :
    ∀ x, ns.contains x = true → ms.contains x = true := by
  intro x hx
  rw [List.all_eq_true] at h
  exact h x (by simpa using hx)

theorem add_names : ∀ x, NatAdd.names.contains x = true → LibIntAS.names.contains x = true :=
  sub_of_all (by decide)

theorem sub_names : ∀ x, NatSub.names.contains x = true → LibIntAS.names.contains x = true :=
  sub_of_all (by decide)

/-- an `Ensures` of a callee whose functions are among `LibIntAS.names`, as a summary in `LibIntAS.program` -/
theorem hypSum {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibIntAS.names.contains x = true) {f : String} {args : List (BitVec 64)}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibIntAS.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.regs 30).toNat ∧ ArgsFrom s 0 args ∧ pre s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        post s s') := by
  have hS := Ensures.toSummaryIn h (noExit_restrict hap ns) (codeIn_restrict_mono hap hns)
  rw [← LibIntAS.eq_only] at hS
  exact hS

/-- `nat.cmp` (agent asm's `CmpSum.cmp_summary`, segment `Extracted.seg15`) in `LibIntAS.program` -/
theorem cmpSum (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibIntAS.program.link impl) 1782608 CmpSum.Pre CmpSum.Post := by
  have hseg : FvModexp.Lib.CmpA64.program.segments = [Extracted.program.segments[15]'(by decide)] := rfl
  have hc := Callees.codeIn_single (lp := FvModexp.Lib.CmpA64.program) (ns := LibIntAS.names) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 15) (by decide)) (by decide)
  rw [← LibIntAS.eq_only] at hc
  exact Janus.Contracts.EqHashModel.Summary.of_codeIn hc CmpSum.cmp_summary

/-- the write barrier contract moved into `LibIntAS.program` -/
theorem wbIn {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    WbLiveContract (LibIntAS.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2 := by
  have hc : CodeIn (Extracted.program.ofImpl impl) (LibIntAS.program.link impl) := by
    rw [LibIntAS.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap names
  exact WbLiveContract.of_codeIn hc hwb

/-! ## Small arithmetic helpers -/

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- a fact hidden from `janus_run` (which destructures every conjunction in the context: slow) -/
structure Box (P : Prop) : Prop where
  h : P

theorem ofNat_toNat64 (v : BitVec 64) : BitVec.ofNat 64 v.toNat = v := by simp

theorem asCost_add (xl yl : Nat) : makeCost (asNeed xl yl) ≤ asCost xl yl := by
  unfold asCost asNeed; exact Nat.le_max_left _ _

theorem asCost_sub (xl yl : Nat) : makeCost (max xl yl) ≤ asCost xl yl := by
  unfold asCost; exact Nat.le_max_right _ _

end FvModexp.Arm64.IntAS
