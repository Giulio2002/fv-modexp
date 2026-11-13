import FvModexp.Proofs.Amd64.Nat.LibDiv
import FvModexp.Proofs.Amd64.NatQ.DivLargeDBR
import FvModexp.Proofs.Amd64.Nat.DivW
import FvModexp.Proofs.Amd64.CmpSum
import FvModexp.Proofs.Amd64.Exp.ExpHyp

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivDefs.lean, TIGHT COSTS, top s38)
# `(z nat) div(stk *stack, z2, u, v nat) (q, r nat)` (go-bigmodexpfix natdiv.go:518), amd64 — statement and callees

Twin of `Arm64/Nat/DivDefs.lean` (see the Go source there). amd64 ABIInternal: `z` = `RAX, RBX, RCX`, `stk` = `RDI`,
`z2` = `RSI, R8, R9`; `u`, `v` on the stack at `RSP + 8 … RSP + 56` (`ExpHyp.DivPre`'s first six conjuncts); results
`q` = `RAX, RBX, RCX` (`regs 0, 3, 1`), `r` = `RDI, RSI, R8` (`regs 7, 6, 8`). Frame: `PUSHQ BP; SUBQ $0xe0, SP`
(`SP' = RSP - 232`): saved `RBP` at `RSP - 8`; register spills `RSP + 56 … RSP + 112` (`above = 112`); result slots
`q` at `SP' + 0xb0 … 0xc0` (`RSP - 56 … - 40`), `r` at `SP' + 0x98 … 0xa8` (`RSP - 80 … - 64`); defer bits
`SP' + 0x6e`, `0x6f` (`RSP - 122`, `- 121`), defer record pointer `SP' + 0xd8` (`RSP - 16`). The `divLarge` call is at
`RSP - 240` (its window `41272`), so the window is `41512 = 240 + 41272`, `above = 112`.

The statement is `ExpHyp.DivHyp` (amd64) with `stk = 41512`, `above = 112`, `cost = NatDiv.cost dc` (its `DivPre`
contains `st ≠ 0`; the `stk == nil` path is a separate statement). Callees: `nat.divW` (`DivW.ens`), `nat.cmp`
(`CmpSum.cmp_summary`), `nat.divLarge` (`DivLarge.Hyp`, premise here; proved by `DivLarge.ens` from `DrsHyp`),
`runtime.makeslice` / `memmove` (live contracts).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.RunIface (Serves)

namespace FvModexp.Amd64.Q.NatDiv
variable {H : Nat}

def fn : String := ExpHyp.fnDiv
def names : List String := LibDiv.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- the precondition: `ExpHyp.DivPre` (amd64) at window `41512`, `above = 112` -/
@[reducible] def Pre (R : RtInv) (b H : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s : State) : Prop :=
  ExpHyp.DivPreQ R b H (costQ dc ul vl + stkR H s.mem st) L 41512 112 zp zl zc st z2 z2l z2c u ul uc v vl vc s

@[reducible] def PostL (R : RtInv) (b H : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  ExpHyp.DivPostLQ R b (costQ dc ul vl + stkR H s.mem st) (stkR H s'.mem st) L 41512 112 zp zc st z2 z2c u ul v vl s s'

/-- the return relation: callee-saved registers and `PostL` -/
@[reducible] def RQ (R : RtInv) (b H : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zc st z2 z2c u ul v vl : Nat) (s s' : State) : Prop :=
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
    PostL R b H dc L zp zc st z2 z2c u ul v vl s s'

/-- `nat.div`'s `Ensures` = `ExpHyp.DivHypLQ impl R names 41512 112 (costQ dc)` (definitionally) -/
def HypL (impl : List Amd64.Segment) (R : RtInv) (dc : Nat → Nat → Nat) : Prop :=
  ExpHyp.DivHypLQ impl R names 41512 112 (costQ dc)

/-- the precondition's conjuncts by name -/
structure PF (R : RtInv) (b H : Nat) (dc : Nat → Nat → Nat) (L : List (Nat × Nat))
    (zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat) (s : State) : Prop where
  ru : s.mem.readLE ((s.regs 4).toNat + 8) 8 = u
  rul : s.mem.readLE ((s.regs 4).toNat + 16) 8 = ul
  ruc : s.mem.readLE ((s.regs 4).toNat + 24) 8 = uc
  rv : s.mem.readLE ((s.regs 4).toNat + 32) 8 = v
  rvl : s.mem.readLE ((s.regs 4).toNat + 40) 8 = vl
  rvc : s.mem.readLE ((s.regs 4).toNat + 48) 8 = vc
  ce : CallEnv R L s 41512 112
  sv : Serves R
  gl : RunIface.Globals R s.mem (win s 41512 112)
  zl : zl ≤ zc
  z2l : z2l ≤ z2c
  zo : EvenHyp.WrOut R L s 41512 112 zp zc
  z2o : EvenHyp.WrOut R L s 41512 112 z2 z2c
  uo : EvenHyp.RdIn R L s 41512 112 u ul
  vo : EvenHyp.RdIn R L s 41512 112 v vl
  ul9 : ul ≤ 2 ^ 9
  v0 : 0 < vl
  vl9 : vl ≤ 2 ^ 9
  un : NatNorm s.mem u ul
  vn : NatNorm s.mem v vl
  sok : ExpHyp.StackOK' s.mem R L st
  sw : Outside st 24 (win s 41512 112)
  sa : 0 < stCap s.mem st → Outside (stW s.mem st) (8 * stCap s.mem st) (win s 41512 112) ∧
      Apart (stW s.mem st) (8 * stCap s.mem st) ((s.regs 14).toNat + 16) 8
  sl : stLen s.mem st + 16 * ul + 64 ≤ 2 ^ 16
  w0 : stCap s.mem st = 0 → stW s.mem st = 0
  us : Apart u (8 * ul) st 24
  uf : Apart u (8 * ul) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  vs : Apart v (8 * vl) st 24
  vf : Apart v (8 * vl) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  st0 : st ≠ 0
  hdr : Apart st 24 ((s.regs 14).toNat + 16) 8 ∧ Apart st 24 StackNat.wbA 4 ∧
      Apart st 24 (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  tls : Apart st 24 (s.fsBase.toNat - 8) 8 ∧
      Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) (s.fsBase.toNat - 8) 8
  zg : 0 < zc → Apart zp (8 * zc) RunIface.gA 32
  z2g : 0 < z2c → Apart z2 (8 * z2c) RunIface.gA 32
  sg : Apart st 24 RunIface.gA 32
  fg : Apart (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st)) RunIface.gA 32
  zz2 : 0 < zc → 0 < z2c → Apart zp (8 * zc) z2 (8 * z2c)
  pw : ∀ p c, (p, c) ∈ [(zp, zc), (z2, z2c)] → 0 < c →
      Apart p (8 * c) u (8 * ul) ∧ Apart p (8 * c) v (8 * vl) ∧ Apart p (8 * c) st 24 ∧
      Apart p (8 * c) (stW s.mem st + 8 * stLen s.mem st) (8 * (stCap s.mem st - stLen s.mem st))
  cost : stLen s.mem st + 16 * ul + 64 ≤ H ∧ costQ dc ul vl + stkR H s.mem st ≤ b
  inv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

theorem Pre.f {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat} {s : State}
    (h : Pre R b H dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s) :
    PF R b H dc L zp zl zc st z2 z2l z2c u ul uc v vl vc s := by
  obtain ⟨r1, r2, r3, r4, r5, r6, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h0, hH, hT, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
  exact ⟨r1, r2, r3, r4, r5, r6, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h0, hH, hT, h24, h25, h26, h27, h28, h29, h30, h31⟩

/-! ## Return addresses inside `nat.div`'s segment (`seg13`, base `0x5edf20`, `0x545` bytes) -/

theorem segA : segAddr Extracted.program fn = 6217504 := by decide

set_option maxRecDepth 20000 in
theorem raD {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0x545) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn + i) := by
  have := DivLarge.retAddr_restrict hap (cs := Extracted.seg13) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg13.name = fn from rfl]; exact hn) i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5edf20 + i < 2 ^ 47; omega)
  rw [show Extracted.seg13.base = 0x5edf20 from rfl] at this
  rw [segA]; exact this

/-! ## Callees moved into `LibDiv.program` -/

theorem codeIn_lib (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 (Extracted.program.ofImpl impl) (LibDiv.program.link impl) := by
  rw [LibDiv.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibDiv.names

set_option linter.defProp false in
/-- `nat.divW` (`DivW.ens`) as a summary in `LibDiv.program.link impl` -/
def wsum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :=
  Ensures.toSummaryIn (DivW.ens impl hap R hmk hmv b L zp zl zc xp xl xc y) (A64.noExit_restrict64 hap DivW.names)
    (by simp [numIntRegs])
    (show CodeIn64 ((Extracted.program.onlySegments DivW.names).link impl) (LibDiv.program.link impl) by
      rw [LibDiv.eq_only]; exact A64.codeIn_restrict_mono64 hap (Callees.sub_of_all (by decide)))

set_option linter.defProp false in
/-- `nat.divLarge` (premise `DivLarge.Hyp`) as a summary in `LibDiv.program.link impl` -/
def lsum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat) (hL : DivLarge.Hyp impl R dc) (H b : Nat) (L : List (Nat × Nat))
    (z zl zc st u ul uc : BitVec 64) (ip il vp vl : Nat) :=
  Ensures.toSummaryIn (hL H b L z zl zc st u ul uc ip il vp vl) (A64.noExit_restrict64 hap DivLarge.names)
    (by simp [numIntRegs])
    (show CodeIn64 ((Extracted.program.onlySegments DivLarge.names).link impl) (LibDiv.program.link impl) by
      rw [LibDiv.eq_only]; exact A64.codeIn_restrict_mono64 hap (Callees.sub_of_all (by decide)))

/-- `nat.cmp` (agent asm's `CmpSum.cmp_summary`, segment `Extracted.seg15`, entry `0x5e5cc0`) in `LibDiv.program` -/
theorem csum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    Summary (LibDiv.program.link impl) 6184128 CmpSum.Pre CmpSum.Post := by
  have hc : CodeIn64 FvModexp.Lib.CmpAmd64.program (LibDiv.program.link impl) := by
    rw [LibDiv.eq_only]
    exact Callees.codeIn_single hap (seg := Extracted.seg15) rfl
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide)
  exact Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc CmpSum.cmp_summary

/-! ## Small helpers -/

/-- an array's range, empty when `c = 0` -/
@[reducible] def ar (p c : Nat) : List (Nat × Nat) := if 0 < c then [(p, p + 8 * c)] else []

theorem outside_ar {a n p c : Nat} (h : 0 < c → a + n ≤ p ∨ p + 8 * c ≤ a) : Outside a n (ar p c) := by
  unfold ar; split
  · simp only [outside_cons, outside_nil, and_true]; next hc => exact h hc
  · trivial

theorem ar_out {a n p c : Nat} (h : Outside a n (ar p c)) (hc : 0 < c) : a + n ≤ p ∨ p + 8 * c ≤ a := by
  unfold ar at h; rw [if_pos hc] at h; simpa only [outside_cons, outside_nil, and_true] using h

theorem outside_ar_of {a n p c : Nat} (h : Outside a n [(p, p + 8 * c)]) : Outside a n (ar p c) :=
  outside_ar fun _ => by simpa only [outside_cons, outside_nil, and_true] using h

/-- a fact hidden from `janus64_run` (which destructures every conjunction in the context) -/
structure Box (P : Prop) : Prop where
  h : P

end FvModexp.Amd64.Q.NatDiv
