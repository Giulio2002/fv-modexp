import FvModexp.Proofs.Arm64.Nat.LibDiv
import FvModexp.Proofs.Arm64.Nat.DivLargeDefs
import FvModexp.Proofs.Arm64.Nat.DivWZ
import FvModexp.Proofs.Arm64.CmpSum

/-!
# `(z nat) div(stk *stack, z2, u, v nat) (q, r nat)` (go-bigmodexpfix natdiv.go:518), arm64 — statement and callees

```go
func (z nat) div(stk *stack, z2, u, v nat) (q, r nat) {
	if len(v) == 0 { panic("division by zero") }
	if len(v) == 1 { var r2 Word; q, r2 = z.divW(u, v[0]); r = z2.setWord(r2); return }
	if u.cmp(v) < 0 { q = z[:0]; r = z2.set(u); return }
	if stk == nil { stk = getStack(); defer stk.free() }
	q, r = z.divLarge(stk, z2, u, v)
	return
}
```
(`setWord`, `set`, `make` nat.go:49-95 inlined.) Arguments `X0..X2 = z`, `X3 = stk`, `X4..X6 = z2`, `X7..X9 = u`,
`X10..X12 = v`; results `X0..X2 = q`, `X3..X5 = r`. Frame 240 (`MOVD.W R30, -240(RSP)`; `SP' = SP - 240`): saved `X30`
at `SP - 240`, `X29` at `SP - 248`; spills `SP + 8 … SP + 104` (`above = 112`); result slots `q` `SP - 56 … -40`, `r`
`SP - 80 … -64`; defer bits `SP - 121`, `SP - 122`; defer record pointer `SP - 16`. Window `41504 = 240 + 41264`
(`divLarge`'s window).

The statement is agent expmc's `ExpHyp.DivHyp` (with `stk = 41504`, `above = 112`, `cost = NatDiv.cost dc`) plus
`st ≠ 0` (the `stk == nil` path, `sync.Pool`, is a separate statement). Callees: `nat.divW` (`DivW.ens2`, zero-length
`memmove` contract form), `nat.cmp` (`CmpSum.cmp_summary`), `nat.divLarge` (`DivLarge.Hyp`, premise here; proved by
`DivLarge.ens` from `DrsHyp`), `runtime.makeslice` / `memmove` (live contracts, `MemmoveZeroLive` for `len u = 0`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.RunIface (Serves)

namespace FvModexp.Arm64.NatDiv

def fn : String := ExpHyp.fnDiv
def names : List String := LibDiv.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- the budget: `divW`'s `z.make(len u)` + `setWord`'s `make(nat, 1)` (len v = 1), `z2.make(len u)` (u < v),
`divLarge` -/
@[reducible] def cost (dc : Nat → Nat → Nat → Nat) (l ul vl : Nat) : Nat :=
  makeCost ul + makeCost 1 + DivLarge.cost dc l ul vl

/-- the precondition: expmc's `DivPre` and a non-nil stack -/
@[reducible] def Pre (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c u ul v vl : Nat) (s : State) : Prop :=
  st ≠ 0 ∧ ExpHyp.DivPre R b (cost dc) L 41504 112 zp zl zc st z2 z2l z2c u ul v vl s

@[reducible] def Post (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  ExpHyp.DivPost R b (cost dc) L 41504 112 zp zc st z2 z2c u ul v vl s s'

/-- the return relation: callee-saved registers and `Post` -/
@[reducible] def RQ (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
    Post R b dc L zp zc st z2 z2c u ul v vl s s'

/-- `nat.div`'s `Ensures` = `ExpHyp.DivHyp impl R names 41504 112 (cost dc)` with `st ≠ 0` -/
def Hyp (impl : List Segment) (R : RtInv) (dc : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc st z2 z2l z2c u ul uc v vl vc : BitVec 64),
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, st, z2, z2l, z2c, u, ul, uc, v, vl, vc]
      (fun s => Pre R b dc L z.toNat zl.toNat zc.toNat st.toNat z2.toNat z2l.toNat z2c.toNat u.toNat ul.toNat
        v.toNat vl.toNat s)
      (fun s s' => Post R b dc L z.toNat zc.toNat st.toNat z2.toNat z2c.toNat u.toNat ul.toNat v.toNat vl.toNat s s')

/-- the precondition's conjuncts by name -/
structure PF (R : RtInv) (b : Nat) (dc : Nat → Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c u ul v vl : Nat) (s : State) : Prop where
  st0 : st ≠ 0
  ce : CallEnv R L s 41504 112
  sv : Serves R
  gl : RunIface.Globals R s.mem (win s 41504 112)
  zl : zl ≤ zc
  z2l : z2l ≤ z2c
  zo : ExpHyp.WrOut R L s 41504 112 zp zc
  z2o : ExpHyp.WrOut R L s 41504 112 z2 z2c
  uo : ExpHyp.RdIn R L s 41504 112 u ul
  vo : ExpHyp.RdIn R L s 41504 112 v vl
  ul9 : ul ≤ 2 ^ 9
  v0 : 0 < vl
  vl9 : vl ≤ 2 ^ 9
  un : NatNorm s.mem u ul
  vn : NatNorm s.mem v vl
  sok : ExpHyp.StackOK' s.mem R L st
  sw : Outside st 24 (win s 41504 112)
  sa : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 41504 112) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 28).toNat + 16) 8
  sl : stLen s.mem st + 16 * ul + 64 ≤ 2 ^ 16
  w0 : stCap s.mem st = 0 → stW s.mem st = 0
  us : Apart u (8 * ul) st 24
  uf : Apart u (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  vs : Apart v (8 * vl) st 24
  vf : Apart v (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  zg : 0 < zc → Apart zp (8 * zc) RunIface.gA 32
  z2g : 0 < z2c → Apart z2 (8 * z2c) RunIface.gA 32
  sg : Apart st 24 RunIface.gA 32
  fg : Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32
  zz2 : 0 < zc → 0 < z2c → Apart zp (8 * zc) z2 (8 * z2c)
  pw : ∀ p c, (p, c) ∈ [(zp, zc), (z2, z2c)] → 0 < c →
      Apart p (8 * c) u (8 * ul) ∧ Apart p (8 * c) v (8 * vl) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  cost : cost dc (stLen s.mem st) ul vl ≤ b
  inv : R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

theorem Pre.f {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul v vl : Nat} {s : State}
    (h : Pre R b dc L zp zl zc st z2 z2l z2c u ul v vl s) : PF R b dc L zp zl zc st z2 z2l z2c u ul v vl s := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, h31⟩

/-! ## Return addresses inside `nat.div`'s segment -/

theorem pw_forall {α : Type} {R : α → α → Prop} (hR : ∀ {a b}, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a}, a ∈ l → ∀ {b}, b ∈ l → a ≠ b → R a b
  | [], _, _, ha, _, _, _ => absurd ha (List.not_mem_nil)
  | x :: l, h, a, ha, b, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hne
    · exact h.1 _ hb'
    · exact hR (h.1 _ ha')
    · exact pw_forall hR h.2 ha' hb' hne

set_option maxRecDepth 20000 in
/-- a return site inside `nat.div`'s segment (`seg13`, base `0x1b9200`, 231 words) is admissible for a callee program
that does not keep `nat.div` -/
theorem raD (impl : List Segment) (hap : ImplApart Extracted.program impl) (ns : List String)
    (hn : ns.contains fn = false) (ret : Nat) (hal : ret % 4 = 0) (h1 : 0x1b9200 ≤ ret) (h2 : ret < 0x1b959c)
    (hst : ∀ st ∈ Extracted.program.stubs, st.addr ≠ ret) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) ret := by
  have hmem : Extracted.seg13 ∈ Extracted.program.segments := by
    have : Extracted.program.segments[13]'(by decide) = Extracted.seg13 := rfl
    rw [← this]; exact List.getElem_mem _
  have hb : Extracted.seg13.base = 0x1b9200 := rfl
  have hl : Extracted.seg13.words.length = 231 := rfl
  have hnm : Extracted.seg13.name = fn := rfl
  refine RetAddr.of_placement hal (by omega) ⟨_, hmem, by rw [hb]; omega, by rw [hb, hl]; omega⟩ hap.1 ?_ hst
  intro seg hm hc
  by_cases he : seg = Extracted.seg13
  · subst he; rw [hnm, hn] at hc; exact absurd hc (by decide)
  · have hpw := (List.pairwise_append.1 hap.1).1
    have := pw_forall (fun {a b} h => by unfold Segment.Apart at h ⊢; omega) hpw hm hmem he
    unfold Segment.Apart at this; rw [hb, hl] at this; omega

/-! ## Callees moved into `LibDiv.program` -/

set_option linter.defProp false in
/-- `nat.divW` (`DivW.ens2`) as a summary in `LibDiv.program.link impl` -/
def wsum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :=
  Ensures.toSummaryIn (DivW.ens2 impl hap R hmk hmv hmz b L zp zl zc xp xl xc y) (noExit_restrict hap DivW.names)
    (show CodeIn ((Extracted.program.onlySegments DivW.names).link impl) (LibDiv.program.link impl) by
      rw [LibDiv.eq_only]; exact codeIn_restrict_mono hap (Callees.sub_of_all (by decide)))

set_option linter.defProp false in
/-- `nat.divLarge` (premise `DivLarge.Hyp`) as a summary in `LibDiv.program.link impl` -/
def lsum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat → Nat) (hL : DivLarge.Hyp impl R dc) (b : Nat) (L : List (Nat × Nat))
    (z zl zc st u ul uc ip il ic vp vl vc : BitVec 64) :=
  Ensures.toSummaryIn (hL b L z zl zc st u ul uc ip il ic vp vl vc) (noExit_restrict hap DivLarge.names)
    (show CodeIn ((Extracted.program.onlySegments DivLarge.names).link impl) (LibDiv.program.link impl) by
      rw [LibDiv.eq_only]; exact codeIn_restrict_mono hap (Callees.sub_of_all (by decide)))

/-- `nat.cmp` (agent asm's `CmpSum.cmp_summary`, segment `Extracted.seg15`) in `LibDiv.program` -/
theorem csum (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibDiv.program.link impl) 1782608 CmpSum.Pre CmpSum.Post := by
  have hseg : FvModexp.Lib.CmpA64.program.segments = [Extracted.program.segments[15]'(by decide)] := rfl
  have hc := Callees.codeIn_single (lp := FvModexp.Lib.CmpA64.program) (ns := LibDiv.names) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 15) (by decide)) (by decide)
  rw [← LibDiv.eq_only] at hc
  exact Janus.Contracts.EqHashModel.Summary.of_codeIn hc CmpSum.cmp_summary

theorem codeIn_lib (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn (Extracted.program.ofImpl impl) (LibDiv.program.link impl) := by
  rw [LibDiv.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibDiv.names

/-! ## Small helpers -/

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_modL (x : Nat) : BitVec.ofNat 64 (x % 18446744073709551616) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- an array's range, empty when `c = 0` (a `cap = 0` nat has no array: its pointer is arbitrary) -/
@[reducible] def ar (p c : Nat) : List (Nat × Nat) := if 0 < c then [(p, p + 8 * c)] else []

theorem outside_ar {a n p c : Nat} (h : 0 < c → a + n ≤ p ∨ p + 8 * c ≤ a) : Outside a n (ar p c) := by
  unfold ar; split
  · simp only [outside_cons, outside_nil, and_true]; next hc => exact h hc
  · trivial

theorem ar_out {a n p c : Nat} (h : Outside a n (ar p c)) (hc : 0 < c) : a + n ≤ p ∨ p + 8 * c ≤ a := by
  unfold ar at h; rw [if_pos hc] at h; simpa only [outside_cons, outside_nil, and_true] using h

theorem outside_ar_of {a n p c : Nat} (h : Outside a n [(p, p + 8 * c)]) : Outside a n (ar p c) :=
  outside_ar fun _ => by simpa only [outside_cons, outside_nil, and_true] using h

/-- a fact hidden from `janus_run` (which destructures every conjunction in the context) -/
structure Box (P : Prop) : Prop where
  h : P

end FvModexp.Arm64.NatDiv
