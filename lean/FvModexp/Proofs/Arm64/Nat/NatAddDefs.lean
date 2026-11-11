import FvModexp.Proofs.Arm64.Nat.LibNatAdd
import FvModexp.Proofs.Arm64.Nat.AsmCallees

/-!
# `nat.add` (go-bigmodexpfix nat.go:98), arm64: statement pieces (WIP — proof not started, see WIP-SORRY.txt)

```go
func (z nat) add(x, y nat) nat {
	m, n := len(x), len(y)
	switch {
	case m < n:  return z.add(y, x)          // the one self-call (then m ≥ n)
	case m == 0: return z[:0]
	case n == 0: return z.set(x)             // make(m) + copy
	}
	z = z.make(m + 1)
	c := addVV(z[:n], x[:n], y[:n])
	if m > n { c = addVW(z[n:m], x[n:], c) }
	z[m] = c
	return z.norm()
}
```
Frame 160 (`MOVD.W R30, -160(RSP)`), spills `X0, X3, X4, X5, X6, X7, X8` at `SP + 8 … SP + 72` (`above = 80`).
Deepest callee in the body (`len y ≤ len x`): `addVW` (`stk 4144`) → body `stk = 160 + 4144 = 4304`; the self-call adds one
frame: `stk = 160 + 4304 = 4464`. Plan: `body` = a `Summary` at the entry for `len y ≤ len x` (no `RetAddr` issue at the
self-call), `ens` = run until the self-call + `body`, or `Summary.returns body`.

Aliasing of the real call sites (`(*Int).Add/Sub` → `z.abs.add(x.abs, y.abs)` with `z = x` possible): `z = x ∨ Apart`,
`z = y ∨ Apart`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.NatAdd

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.add"
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- `max(len x, len y)`, the length of the longer operand. -/
@[reducible] def mx (xl yl : BitVec 64) : Nat := max xl.toNat yl.toNat

/-- The capacity `nat.add` needs: `m + 1` (`make(m + 1)`), or `m` for `z.set(x)` when the shorter operand is empty. -/
@[reducible] def need (xl yl : BitVec 64) : Nat := if min xl.toNat yl.toNat = 0 then mx xl yl else mx xl yl + 1

/-- The precondition (requests: one `makeslice` when `z` is too small, the `memmove` of `z.set(x)` and the `addVW`
copies, to any runtime-chosen destination). -/
def PreS (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64) (s : State) : Prop :=
  CallEnv R L s stk 80 ∧ Outside wordT 16 R.rt ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧ xc.toNat < 2 ^ 40 ∧ yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    Outside zp.toNat (8 * zc.toNat) (win s stk 80) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ NatNorm s.mem xp.toNat xl.toNat ∧ NatNorm s.mem yp.toNat yl.toNat ∧ Outside xp.toNat (8 * xl.toNat) (win s stk 80) ∧
    s.mem.accessible yp.toNat (8 * yl.toNat) false = true ∧ yp.toNat + 8 * yl.toNat ≤ 2 ^ 48 ∧
    Held R L yp.toNat (8 * yl.toNat) ∧ Outside yp.toNat (8 * yl.toNat) (win s stk 80) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < need xl yl → R.ok (cA "runtime.makeslice") [wordT, need xl yl, makeCap (need xl yl)] ∧
      makeCost (need xl yl) ≤ b) ∧
    (∀ d src k, k ≤ 8 * mx xl yl → R.ok (cA "runtime.memmove") [d, src, k])

/-- The precondition of the function (`stk = 4464`: the self-call adds one frame to the body's 4304). -/
@[reducible] def Pre := PreS 4464

/-- The postcondition: a normalised nat `(p', n', c')` holding `X + Y`, `z`'s array or a fresh one. -/
@[reducible] def PostS (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64) (s s' : State) :
    Prop :=
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 1).toNat = n' ∧ (s'.regs 2).toNat = c' ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat + natVal s.mem yp.toNat yl.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ mx xl yl + 1 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost (need xl yl) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s stk 80 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

@[reducible] def Post := PostS 4464

end FvModexp.Arm64.NatAdd

namespace FvModexp.Arm64.NatAdd

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- A call environment for more stack is one for less. -/
theorem callEnv_mono {R : RtInv} {L : List (Nat × Nat)} {s : State} {stk stk' above : Nat} (hk : stk' ≤ stk)
    (h : CallEnv R L s stk above) : CallEnv R L s stk' above := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hga, hgr, hLs, hro⟩ := h
  unfold Apart at hga
  refine ⟨⟨hg1, hg2, by omega⟩, ⟨hal, by omega, ha, Memory.accessible_mono _ hw (by omega) (by omega)⟩, hd,
    hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgr, fun r hr => ?_, hro⟩
  have := hLs r hr
  simp only [win, outside_cons, outside_nil, and_true] at this ⊢
  omega

theorem preS_mono {stk stk' : Nat} (hk : stk' ≤ stk) {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {zp zc xp xl xc yp yl yc : BitVec 64} {s : State} (h : PreS stk R b L zp zc xp xl xc yp yl yc s) :
    PreS stk' R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨hce, h1, h2, h3, h4, h5, h6, h7, h8, h9, hzo, hzw, h10, h11, h12, h13, h14, hxw, h15, h16, h17, hyw, h18⟩ := h
  have hsp := hce.2.1.2.1
  refine ⟨callEnv_mono hk hce, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, hzw, h10, h11, h12, h13, h14, ?_, h15, h16,
    h17, ?_, h18⟩
  · simp only [win, outside_cons, outside_nil, and_true] at hzo ⊢; omega
  · simp only [win, outside_cons, outside_nil, and_true] at hxw ⊢; omega
  · simp only [win, outside_cons, outside_nil, and_true] at hyw ⊢; omega

theorem postS_mono {stk stk' : Nat} (hk : stk ≤ stk') {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {zp zc xp xl yp yl : BitVec 64} {s s' : State} (hsp : stk' ≤ s.sp.toNat) (h : PostS stk R b L zp zc xp xl yp yl s s') :
    PostS stk' R b L zp zc xp xl yp yl s s' := by
  obtain ⟨p', n', c', h0, h1, h2, hv, hn, hnc, hnm, L', b', hext, hb, hinv, hl, hor, hmf, hlf⟩ := h
  refine ⟨p', n', c', h0, h1, h2, hv, hn, hnc, hnm, L', b', hext, hb, hinv, hl, hor, hmf.mono fun a n h => ?_, hlf⟩
  have e1 : s.sp.toNat - stk' ≤ s.sp.toNat - stk := Nat.sub_le_sub_left hk _
  simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨⟨hr, h1, h2⟩, h3⟩ := h
  exact ⟨⟨hr, by omega, h2⟩, h3⟩

end FvModexp.Arm64.NatAdd
