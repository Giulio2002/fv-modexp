import FvModexp.Proofs.Amd64.NatQ.DrsAt
import FvModexp.Proofs.Amd64.Nat.StackNatXDefs

set_option autoImplicit false

/-! (amd64 twin of Arm64/NatQ/DrsRel.lean, asm s45)
# `divRecursiveStep` (amd64), big path (`n ≥ 40`, `len u ≥ n`): the shared relations (no janus runs)

Every segment module of the big path imports this module only (ROW-TIME lesson: independent segments, one shared
relation module).

* `Cx`: the fixed quantities of one activation — the entry arguments (as `Nat`), the normalised `len u` (`u1`), the
  address `t0` of `qhat0 = stk.nat(B + 1)` and the live set `L1` right after that call.
* `Cr R c s`: the facts fixed from the call of `stk.nat(B + 1)` on (entry pre, return address, `qhat0`'s location and
  separation).
* `Ev R c s Lk bk M`: the environment at a later memory `M` (live set `Lk ⊇ L1`, budget `bk`, frames from the entry,
  the stack object kept healthy, its array the entry one or fresh, and when fresh an element of `Lk` with `0 < cap`).
* `Fp R c s Lk M lM`: the stack's free part `[w + 8·lM, w + 8·cap)` at the current length `lM`, separated from
  everything the body uses.
* `Sl c s M`: the fixed frame slots (return address, saved `RBP`, defer record and bit, `m`, `n`, `len u`, `B`,
  `qhat0`, the stack arguments `v`, the spills). Own stores go to `scr s` only (`Sl.scr`); callee frames avoid the own
  frame (`Sl.frame` with `FixOut`).

Frame (offsets from the entry `RSP` = `r`; `RSP' = r - 392`, a callee's entry `RSP` is `r - 400`): fixed byte `r-297`
(defer bit), `[r-232, r-208)` (`qhat0` len/cap, `m`), `[r-192, r-184)` (`n`), `[r-168, r-160)` (`B`), `[r-104, r-96)`
(`len u`), `[r-64, r-32)` (`qhat0` ptr, defer record), `[r-16, r+96)` (record pointer, saved `RBP`, return address,
`v`, spills). The loop's own stores (disassembly, natdiv.go:793-850) are all inside `scr s`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the fixed quantities of the big path -/
structure Cx where
  Hq : Nat
  b : Nat
  L : List (Nat × Nat)
  W : Nat
  qp : Nat
  ql : Nat
  qc : Nat
  st : Nat
  up : Nat
  ul : Nat
  uc : Nat
  vp : Nat
  vl : Nat
  vc : Nat
  d : Nat
  u1 : Nat
  t0 : Nat
  L1 : List (Nat × Nat)

/-- the wide digit `B = n / 2` -/
abbrev Cx.B (c : Cx) : Nat := c.vl / 2

/-- the stack length after `qhat0` -/
@[reducible] def Cx.l1 (c : Cx) (s : State) : Nat := stLen s.mem c.st + StackNat.rnd (c.vl / 2 + 1)

/-- the budget of one wide-digit step: the recursive call, `stk.nat(3n)`, `qhatv.mul(stk, qhat, v[:s])` -/
@[reducible] def Cx.K (c : Cx) (_s : State) : Nat :=
  drsCQ c.ul (c.vl - c.vl / 2 + 1) + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1)

/-- the part of the entry budget `b` that must be left at the return (`RtPostQ`); every budget invariant of the big
path carries it as `c.lo s + (what the rest of the path consumes) ≤ bk` -/
def Cx.lo (c : Cx) (s : State) : Nat := c.b - (drsCQ c.ul c.vl + stkR c.Hq s.mem c.st)

/-- the ranges of the entry the big path may write -/
@[reducible] def Cx.ws (c : Cx) (s : State) : List (Nat × Nat) :=
  [(c.qp, c.qp + 8 * c.ql), (c.up, c.up + 8 * c.ul)] ++ stkWs s.mem c.st

/-- the guard word of the goroutine -/
@[reducible] def grd (s : State) : Nat := (s.regs 14).toNat + 16

/-- the TLS slot of the goroutine pointer -/
@[reducible] def tls (s : State) : Nat := s.fsBase.toNat - 8

/-- the facts fixed from the `stk.nat(B + 1)` call on -/
structure Cr (R : RtInv) (c : Cx) (s : State) : Prop where
  pre : DrsPreW R c.b c.L c.Hq (drsCQ c.ul c.vl) c.W c.qp c.ql c.qc c.st c.up c.ul c.uc c.vp c.vl c.vc s
  ra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  x15 : s.xmm 15 = 0#128
  df : s.df = false
  hW : drsW64 c.vl ≤ c.W
  h40 : 40 ≤ c.vl
  vu1 : c.vl ≤ c.u1
  u1ul : c.u1 ≤ c.ul
  hU : natVal s.mem c.up c.u1 = natVal s.mem c.up c.ul
  hN : NatNorm s.mem c.up c.u1
  ext1 : LiveExt R c.L c.L1
  t0al : c.t0 % 8 = 0
  t048 : c.t0 + 8 * (c.vl / 2 + 1) ≤ 2 ^ 48
  t0h : Held R c.L1 c.t0 (8 * (c.vl / 2 + 1))
  t0acc : s.mem.accessible c.t0 (8 * (c.vl / 2 + 1)) true = true
  t0loc : (stW s.mem c.st + 8 * stLen s.mem c.st ≤ c.t0 ∧
      c.t0 + 8 * (c.vl / 2 + 1) ≤ stW s.mem c.st + 8 * stCap s.mem c.st) ∨
    (InRanges c.t0 (8 * (c.vl / 2 + 1)) R.rt ∧ ApartAll c.t0 (8 * (c.vl / 2 + 1)) c.L)
  t0w : Outside c.t0 (8 * (c.vl / 2 + 1)) (win s c.W 96)
  t0g : Apart c.t0 (8 * (c.vl / 2 + 1)) (grd s) 8
  t0fs : Apart c.t0 (8 * (c.vl / 2 + 1)) (tls s) 8
  t0gA : Apart c.t0 (8 * (c.vl / 2 + 1)) RunIface.gA 32
  t0st : Apart c.t0 (8 * (c.vl / 2 + 1)) c.st 24
  t0q : Apart c.t0 (8 * (c.vl / 2 + 1)) c.qp (8 * c.ql)
  t0u : Apart c.t0 (8 * (c.vl / 2 + 1)) c.up (8 * c.ul)
  t0v : Apart c.t0 (8 * (c.vl / 2 + 1)) c.vp (8 * c.vl)

/-- the environment at memory `M` (live set `Lk`, budget `bk`) -/
structure Ev (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) : Prop where
  ext : LiveExt R c.L1 Lk
  reg : M.regions = s.mem.regions
  inv : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk M)
  fr : MemFrame s.mem M (R.rt ++ win s c.W 96 ++ c.ws s)
  lf : LiveFrame s.mem M c.L (c.ws s)
  sok : StkOK M R Lk c.st
  sarr : (stW M c.st = stW s.mem c.st ∧ stCap M c.st = stCap s.mem c.st) ∨
    (InRanges (stW M c.st) (8 * stCap M c.st) R.rt ∧ ApartAll (stW M c.st) (8 * stCap M c.st) c.L)
  sarrL : ArrIn Lk c.st s.mem M

/-- the free part at the current stack length `lM` -/
structure Fp (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (M : Memory) (lM : Nat) : Prop where
  len : stLen M c.st = lM
  fh : Held R Lk (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM))
  fw : Outside (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) (win s c.W 96)
  fg : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) (grd s) 8
  ffs : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) (tls s) 8
  fst : Apart c.st 24 (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM))
  fgA : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) RunIface.gA 32
  fq : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) c.qp (8 * c.ql)
  fu : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) c.up (8 * c.ul)
  fv : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) c.vp (8 * c.vl)
  ft0 : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) c.t0 (8 * (c.vl / 2 + 1))

/-- the fixed frame slots at memory `M` -/
structure Sl (c : Cx) (s : State) (M : Memory) : Prop where
  ra : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  dbit : M.readLE ((s.regs 4).toNat - 297) 1 = 1
  q0l : M.readLE ((s.regs 4).toNat - 232) 8 = c.vl / 2 + 1
  q0c : M.readLE ((s.regs 4).toNat - 224) 8 = c.vl / 2 + 1
  mm : M.readLE ((s.regs 4).toNat - 216) 8 = c.u1 - c.vl
  nn : M.readLE ((s.regs 4).toNat - 192) 8 = c.vl
  bb : M.readLE ((s.regs 4).toNat - 168) 8 = c.vl / 2
  ul' : M.readLE ((s.regs 4).toNat - 104) 8 = c.u1
  q0p : M.readLE ((s.regs 4).toNat - 64) 8 = c.t0
  dfn : M.readLE ((s.regs 4).toNat - 56) 8 = 0x5f0800
  dst : M.readLE ((s.regs 4).toNat - 48) 8 = c.st
  dn : M.readLE ((s.regs 4).toNat - 40) 8 = stLen s.mem c.st
  dp : M.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 56
  vp : M.readLE ((s.regs 4).toNat + 8) 8 = c.vp
  vl : M.readLE ((s.regs 4).toNat + 16) 8 = c.vl
  vc : M.readLE ((s.regs 4).toNat + 24) 8 = c.vc
  s1 : M.readLE ((s.regs 4).toNat + 32) 8 = c.qp
  s2 : M.readLE ((s.regs 4).toNat + 40) 8 = c.ql
  s3 : M.readLE ((s.regs 4).toNat + 48) 8 = c.qc
  s4 : M.readLE ((s.regs 4).toNat + 56) 8 = c.st
  s5 : M.readLE ((s.regs 4).toNat + 64) 8 = c.up
  s7 : M.readLE ((s.regs 4).toNat + 80) 8 = c.uc
  s9 : M.readLE ((s.regs 4).toNat + 88) 8 = c.d

/-- the own scratch slots (every store of the big path after `stk.nat(B + 1)` goes here) -/
@[reducible] def scr (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 392, (s.regs 4).toNat - 297), ((s.regs 4).toNat - 296, (s.regs 4).toNat - 232), ((s.regs 4).toNat - 208, (s.regs 4).toNat - 192), ((s.regs 4).toNat - 184, (s.regs 4).toNat - 168),
    ((s.regs 4).toNat - 160, (s.regs 4).toNat - 104), ((s.regs 4).toNat - 96, (s.regs 4).toNat - 64), ((s.regs 4).toNat - 32, (s.regs 4).toNat - 16)]

/-- the fixed slots are outside `rs` -/
@[reducible] def FixOut (s : State) (rs : List (Nat × Nat)) : Prop :=
  Outside ((s.regs 4).toNat - 297) 1 rs ∧ Outside ((s.regs 4).toNat - 232) 24 rs ∧ Outside ((s.regs 4).toNat - 192) 8 rs ∧
    Outside ((s.regs 4).toNat - 168) 8 rs ∧ Outside ((s.regs 4).toNat - 104) 8 rs ∧ Outside ((s.regs 4).toNat - 64) 32 rs ∧ Outside ((s.regs 4).toNat - 16) 112 rs

theorem fixOut_scr {s : State} (h : 400 ≤ (s.regs 4).toNat) : FixOut s (scr s) := by
  simp only [FixOut, scr, outside_cons, outside_nil, and_true]; omega

/-- a callee's frame `R.rt ++ win S k a ++ ws` (`S`'s `RSP = r - 400`, `a ≤ 103`) avoids the fixed slots when every
range of `ws` does -/
theorem fixOut_callee {R : RtInv} {s S : State} {W k a : Nat} {ws : List (Nat × Nat)}
    (hout : Outside ((s.regs 4).toNat - W) (W + 96) R.rt) (hW : 408 ≤ W) (h0 : W ≤ (s.regs 4).toNat)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 400) (ha : a ≤ 103) (hws : FixOut s ws) :
    FixOut s (R.rt ++ win S k a ++ ws) := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := hws
  have o : ∀ x n, (s.regs 4).toNat - 408 ≤ x → x + n ≤ (s.regs 4).toNat + 96 → Outside x n R.rt :=
    fun x n h1 h2 => hout.of_sub (by omega) (by omega)
  simp only [FixOut, win, outside_append, outside_cons, outside_nil, and_true]
  rw [hsp]
  refine ⟨⟨⟨o _ _ (by omega) (by omega), by omega⟩, w1⟩, ⟨⟨o _ _ (by omega) (by omega), by omega⟩, w2⟩,
    ⟨⟨o _ _ (by omega) (by omega), by omega⟩, w3⟩, ⟨⟨o _ _ (by omega) (by omega), by omega⟩, w4⟩,
    ⟨⟨o _ _ (by omega) (by omega), by omega⟩, w5⟩, ⟨⟨o _ _ (by omega) (by omega), by omega⟩, w6⟩,
    ⟨⟨o _ _ (by omega) (by omega), by omega⟩, w7⟩⟩

/-- the fixed slots survive a frame avoiding them -/
theorem Sl.frame {c : Cx} {s : State} {M M' : Memory} {rs : List (Nat × Nat)} (h : Sl c s M) (hF : MemFrame M M' rs)
    (ho : FixOut s rs) : Sl c s M' := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := ho
  have r : ∀ {x n A N}, Outside A N rs → A ≤ x → x + n ≤ A + N → M'.readLE x n = M.readLE x n :=
    fun hA h1 h2 => hF.readLE _ _ (hA.of_sub h1 h2)
  exact ⟨by rw [r o7 (by omega) (by omega)]; exact h.ra, by rw [r o7 (by omega) (by omega)]; exact h.bp,
    by rw [r o1 (by omega) (by omega)]; exact h.dbit, by rw [r o2 (by omega) (by omega)]; exact h.q0l,
    by rw [r o2 (by omega) (by omega)]; exact h.q0c, by rw [r o2 (by omega) (by omega)]; exact h.mm,
    by rw [r o3 (by omega) (by omega)]; exact h.nn, by rw [r o4 (by omega) (by omega)]; exact h.bb,
    by rw [r o5 (by omega) (by omega)]; exact h.ul', by rw [r o6 (by omega) (by omega)]; exact h.q0p,
    by rw [r o6 (by omega) (by omega)]; exact h.dfn, by rw [r o6 (by omega) (by omega)]; exact h.dst,
    by rw [r o6 (by omega) (by omega)]; exact h.dn, by rw [r o7 (by omega) (by omega)]; exact h.dp,
    by rw [r o7 (by omega) (by omega)]; exact h.vp, by rw [r o7 (by omega) (by omega)]; exact h.vl,
    by rw [r o7 (by omega) (by omega)]; exact h.vc, by rw [r o7 (by omega) (by omega)]; exact h.s1,
    by rw [r o7 (by omega) (by omega)]; exact h.s2, by rw [r o7 (by omega) (by omega)]; exact h.s3,
    by rw [r o7 (by omega) (by omega)]; exact h.s4, by rw [r o7 (by omega) (by omega)]; exact h.s5,
    by rw [r o7 (by omega) (by omega)]; exact h.s7, by rw [r o7 (by omega) (by omega)]; exact h.s9⟩

theorem Sl.scr {c : Cx} {s : State} {M M' : Memory} (h : Sl c s M) (hF : MemFrame M M' (scr s)) (h0 : 400 ≤ (s.regs 4).toNat) :
    Sl c s M' :=
  h.frame hF (fixOut_scr h0)

/-- a Q-form budget fact moves to a memory with the same stack capacity -/
theorem bud_cap {H X bk : Nat} {M M' : Memory} {st : Nat} (e : stCap M' st = stCap M st)
    (h : X + stkR H M st ≤ bk) : X + stkR H M' st ≤ bk := by rw [stkR_congr e]; exact h

/-! ## The loop head (natdiv.go:793) -/

/-- the loop head `0x5efa5f` (`MOVQ 0xe0(SP), R11; CMPQ R11, DX; JLE`): `RDX = j`, `RAX, RBX, RCX = qhat0` -/
abbrev head : Nat := 0x5efa5f

/-- **the invariant of `for j > B`** at the head (state `S`, live set `Lk`, budget `bk`) -/
structure H (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) : Prop where
  pc : S.rip = BitVec.ofNat 64 head
  sp : S.regs 4 = s.regs 4 - 392#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  df : S.df = false
  x15 : S.xmm 15 = 0#128
  r0 : S.regs 0 = BitVec.ofNat 64 c.t0
  r3 : S.regs 3 = BitVec.ofNat 64 (c.vl / 2 + 1)
  r1 : S.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1)
  r2 : S.regs 2 = BitVec.ofNat 64 j
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s)
  sl : Sl c s S.mem
  li : Mdl.LI (Asm.limbs s.mem c.vp c.vl) c.vl (c.vl / 2) (c.u1 - c.vl) c.ql (natVal s.mem c.up c.u1) j
    (Asm.limbs S.mem c.qp c.ql) (Asm.limbs S.mem c.up c.u1)
  vk : S.mem.readLE c.vp (8 * c.vl) = s.mem.readLE c.vp (8 * c.vl)
  utl : S.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = s.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1))
  bud : c.lo s + (j / (c.vl / 2) + 1) * c.K s + stkR c.Hq S.mem c.st ≤ bk

end FvModexp.Amd64.Q.DivRec
