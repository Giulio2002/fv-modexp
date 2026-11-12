import FvModexp.Proofs.Arm64.Nat.DrsNat

/-!
# `divRecursiveStep` (arm64), big path (`n ≥ 40`, `len u ≥ n`): the shared relations (no janus runs)

Every segment module of the big path imports this module only (ROW-TIME lesson: independent segments, one shared
relation module).

* `Cx`: the fixed quantities of one activation — the entry arguments (as `Nat`), the normalised `len u` (`u1`), the
  address `t0` of `qhat0 = stk.nat(B + 1)` and the live set `L1` right after that call.
* `Cr R c s`: the facts fixed from the call of `stk.nat(B + 1)` on (entry pre, `qhat0`'s location and separation).
* `Ev R c s Lk bk M`: the environment at a later memory `M` (live set `Lk ⊇ L1`, budget `bk`, frames from the entry,
  the stack object kept healthy, its array the entry one or fresh). NOTE: no `ArrIn` (StackBackL) half yet —
  it needs `DrsPostW` (and divBasic's post) in the `StackBackL` form first, see NOTES-asm s22.
* `Fp R c s Lk M lM`: the stack's free part `[w + 8·lM, w + 8·cap)` at the current length `lM`, separated from
  everything the body uses.
* `Sl c s M`: the fixed frame slots (saved FP/LR, defer record and bit, `m`, `n`, `len u`, `B`, `qhat0`, the spills).
  Own stores go to `scr s` only (`Sl.scr`); callee frames avoid the own frame (`Sl.frame` with `FixOut`).

Frame (offsets from the entry `SP`, `SP' = SP - 400`): fixed `[SP-408, SP-392)` (FP, LR), byte `SP-297` (defer bit),
`[SP-224, SP-200)` (`qhat0` len/cap, `m`), `[SP-184, SP-168)` (`n`, `len u`), `[SP-152, SP-144)` (`B`),
`[SP-64, SP-32)` (`qhat0` ptr, defer record), `[SP-16, SP-8)` (record pointer), `[SP+8, SP+96)` (spills).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- the fixed quantities of the big path -/
structure Cx where
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
@[reducible] def Cx.K (c : Cx) (s : State) : Nat :=
  drsC (c.l1 s) c.ul (c.vl - c.vl / 2 + 1) + stackNatCost (c.l1 s) (3 * c.vl) +
    mulC (c.l1 s + StackNat.rnd (3 * c.vl)) (c.vl / 2 + 1) (c.vl / 2 - 1)

/-- the part of the entry budget `b` that must be left at the return (`RtPost`: `b - drsC … ≤ b'`); every budget
invariant of the big path carries it as `c.lo s + (what the rest of the path consumes) ≤ bk` -/
def Cx.lo (c : Cx) (s : State) : Nat := c.b - drsC (stLen s.mem c.st) c.ul c.vl

/-- the ranges of the entry the big path may write -/
@[reducible] def Cx.ws (c : Cx) (s : State) : List (Nat × Nat) :=
  [(c.qp, c.qp + 8 * c.ql), (c.up, c.up + 8 * c.ul)] ++ stkWs s.mem c.st

/-- the guard word of the goroutine -/
@[reducible] def grd (s : State) : Nat := (s.regs 28).toNat + 16

/-- the facts fixed from the `stk.nat(B + 1)` call on -/
structure Cr (R : RtInv) (c : Cx) (s : State) : Prop where
  pre : DrsPreW R c.b c.L (drsC (stLen s.mem c.st) c.ul c.vl) c.W c.qp c.ql c.qc c.st c.up c.ul c.uc c.vp c.vl c.vc s
  ra4 : (s.regs 30).toNat % 4 = 0
  ra48 : (s.regs 30).toNat < 2 ^ 48
  hW : drsW c.vl ≤ c.W
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
  t0gA : Apart c.t0 (8 * (c.vl / 2 + 1)) RunIface.gA 32
  t0st : Apart c.t0 (8 * (c.vl / 2 + 1)) c.st 24
  t0q : Apart c.t0 (8 * (c.vl / 2 + 1)) c.qp (8 * c.ql)
  t0u : Apart c.t0 (8 * (c.vl / 2 + 1)) c.up (8 * c.ul)
  t0v : Apart c.t0 (8 * (c.vl / 2 + 1)) c.vp (8 * c.vl)

/-- the environment at memory `M` (live set `Lk`, budget `bk`) -/
structure Ev (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) : Prop where
  ext : LiveExt R c.L1 Lk
  reg : M.regions = s.mem.regions
  inv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk M)
  fr : MemFrame s.mem M (R.rt ++ winA s c.W 96 ++ c.ws s)
  lf : LiveFrame s.mem M c.L (c.ws s)
  sok : StkOK M R Lk c.st
  sarr : (stW M c.st = stW s.mem c.st ∧ stCap M c.st = stCap s.mem c.st) ∨
    (InRanges (stW M c.st) (8 * stCap M c.st) R.rt ∧ ApartAll (stW M c.st) (8 * stCap M c.st) c.L)

/-- the free part at the current stack length `lM` -/
structure Fp (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (M : Memory) (lM : Nat) : Prop where
  len : stLen M c.st = lM
  fh : Held R Lk (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM))
  fw : Outside (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) (win s c.W 96)
  fg : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) (grd s) 8
  fst : Apart c.st 24 (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM))
  fgA : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) RunIface.gA 32
  fq : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) c.qp (8 * c.ql)
  fu : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) c.up (8 * c.ul)
  fv : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) c.vp (8 * c.vl)
  ft0 : Apart (stW M c.st + 8 * lM) (8 * (stCap M c.st - lM)) c.t0 (8 * (c.vl / 2 + 1))

/-- the fixed frame slots at memory `M` -/
structure Sl (c : Cx) (s : State) (M : Memory) : Prop where
  lr : M.readLE (s.sp.toNat - 400) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 408) 8 = (s.regs 29).toNat
  dbit : M.readLE (s.sp.toNat - 297) 1 = 1
  q0l : M.readLE (s.sp.toNat - 224) 8 = c.vl / 2 + 1
  q0c : M.readLE (s.sp.toNat - 216) 8 = c.vl / 2 + 1
  mm : M.readLE (s.sp.toNat - 208) 8 = c.u1 - c.vl
  nn : M.readLE (s.sp.toNat - 184) 8 = c.vl
  ul' : M.readLE (s.sp.toNat - 176) 8 = c.u1
  bb : M.readLE (s.sp.toNat - 152) 8 = c.vl / 2
  q0p : M.readLE (s.sp.toNat - 64) 8 = c.t0
  dfn : M.readLE (s.sp.toNat - 56) 8 = 0x1bae20
  dst : M.readLE (s.sp.toNat - 48) 8 = c.st
  dn : M.readLE (s.sp.toNat - 40) 8 = stLen s.mem c.st
  dp : M.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 56
  s1 : M.readLE (s.sp.toNat + 8) 8 = c.qp
  s2 : M.readLE (s.sp.toNat + 16) 8 = c.ql
  s3 : M.readLE (s.sp.toNat + 24) 8 = c.qc
  s4 : M.readLE (s.sp.toNat + 32) 8 = c.st
  s5 : M.readLE (s.sp.toNat + 40) 8 = c.up
  s7 : M.readLE (s.sp.toNat + 56) 8 = c.uc
  s8 : M.readLE (s.sp.toNat + 64) 8 = c.vp
  s10 : M.readLE (s.sp.toNat + 80) 8 = c.vc
  s11 : M.readLE (s.sp.toNat + 88) 8 = c.d

/-- the own scratch slots (every store of the big path after `stk.nat(B + 1)` goes here) -/
@[reducible] def scr (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 392, s.sp.toNat - 297), (s.sp.toNat - 296, s.sp.toNat - 224), (s.sp.toNat - 200, s.sp.toNat - 184),
    (s.sp.toNat - 168, s.sp.toNat - 152), (s.sp.toNat - 144, s.sp.toNat - 64), (s.sp.toNat - 32, s.sp.toNat - 16)]

/-- the fixed slots are outside `rs` -/
@[reducible] def FixOut (s : State) (rs : List (Nat × Nat)) : Prop :=
  Outside (s.sp.toNat - 408) 16 rs ∧ Outside (s.sp.toNat - 297) 1 rs ∧ Outside (s.sp.toNat - 224) 24 rs ∧
    Outside (s.sp.toNat - 184) 16 rs ∧ Outside (s.sp.toNat - 152) 8 rs ∧ Outside (s.sp.toNat - 64) 32 rs ∧
    Outside (s.sp.toNat - 16) 8 rs ∧ Outside (s.sp.toNat + 8) 88 rs

theorem fixOut_scr {s : State} (h : 408 ≤ s.sp.toNat) : FixOut s (scr s) := by
  simp only [FixOut, scr, outside_cons, outside_nil, and_true]; omega

/-- a callee's frame `R.rt ++ winA S k a ++ ws` (`S.sp = SP - 400`, `a ≤ 103`) avoids the fixed slots when every range
of `ws` does -/
theorem fixOut_callee {R : RtInv} {s S : State} {W k a : Nat} {ws : List (Nat × Nat)}
    (hout : Outside (s.sp.toNat - W) (W + 96) R.rt) (hW : 408 ≤ W) (h0 : W ≤ s.sp.toNat)
    (hsp : S.sp.toNat = s.sp.toNat - 400) (ha : a ≤ 103) (hws : FixOut s ws) :
    FixOut s (R.rt ++ winA S k a ++ ws) := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hws
  have o : ∀ x n, s.sp.toNat - 408 ≤ x → x + n ≤ s.sp.toNat + 96 → Outside x n R.rt :=
    fun x n h1 h2 => hout.of_sub (by omega) (by omega)
  simp only [FixOut, winA, outside_append, outside_cons, outside_nil, and_true]
  rw [hsp]
  refine ⟨⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w1⟩, ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w2⟩,
    ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w3⟩, ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w4⟩,
    ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w5⟩, ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w6⟩,
    ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w7⟩, ⟨⟨o _ _ (by omega) (by omega), by omega, by omega⟩, w8⟩⟩

/-- the fixed slots survive a frame avoiding them -/
theorem Sl.frame {c : Cx} {s : State} {M M' : Memory} {rs : List (Nat × Nat)} (h : Sl c s M) (hF : MemFrame M M' rs)
    (ho : FixOut s rs) : Sl c s M' := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := ho
  have r : ∀ {x n A N}, Outside A N rs → A ≤ x → x + n ≤ A + N → M'.readLE x n = M.readLE x n :=
    fun hA h1 h2 => hF.readLE _ _ (hA.of_sub h1 h2)
  exact ⟨by rw [r o1 (by omega) (by omega)]; exact h.lr, by rw [r o1 (by omega) (by omega)]; exact h.fp,
    by rw [r o2 (by omega) (by omega)]; exact h.dbit, by rw [r o3 (by omega) (by omega)]; exact h.q0l,
    by rw [r o3 (by omega) (by omega)]; exact h.q0c, by rw [r o3 (by omega) (by omega)]; exact h.mm,
    by rw [r o4 (by omega) (by omega)]; exact h.nn, by rw [r o4 (by omega) (by omega)]; exact h.ul',
    by rw [r o5 (by omega) (by omega)]; exact h.bb, by rw [r o6 (by omega) (by omega)]; exact h.q0p,
    by rw [r o6 (by omega) (by omega)]; exact h.dfn, by rw [r o6 (by omega) (by omega)]; exact h.dst,
    by rw [r o6 (by omega) (by omega)]; exact h.dn, by rw [r o7 (by omega) (by omega)]; exact h.dp,
    by rw [r o8 (by omega) (by omega)]; exact h.s1, by rw [r o8 (by omega) (by omega)]; exact h.s2,
    by rw [r o8 (by omega) (by omega)]; exact h.s3, by rw [r o8 (by omega) (by omega)]; exact h.s4,
    by rw [r o8 (by omega) (by omega)]; exact h.s5, by rw [r o8 (by omega) (by omega)]; exact h.s7,
    by rw [r o8 (by omega) (by omega)]; exact h.s8, by rw [r o8 (by omega) (by omega)]; exact h.s10,
    by rw [r o8 (by omega) (by omega)]; exact h.s11⟩

theorem Sl.scr {c : Cx} {s : State} {M M' : Memory} (h : Sl c s M) (hF : MemFrame M M' (scr s)) (h0 : 408 ≤ s.sp.toNat) :
    Sl c s M' :=
  h.frame hF (fixOut_scr h0)

/-! ## The loop head (`fn + 0x164`) -/

/-- the loop head `0x1ba504` (`CMP R11>>1, R3`): `R3 = j`, `R0..R2 = qhat0` -/
abbrev head : Nat := 0x1ba504

/-- **the invariant of `for j > B`** at the head (state `S`, live set `Lk`, budget `bk`) -/
structure H (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 head
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 c.t0
  r1 : S.regs 1 = BitVec.ofNat 64 (c.vl / 2 + 1)
  r2 : S.regs 2 = BitVec.ofNat 64 (c.vl / 2 + 1)
  r3 : S.regs 3 = BitVec.ofNat 64 j
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s)
  sl : Sl c s S.mem
  li : Mdl.LI (Asm.limbs s.mem c.vp c.vl) c.vl (c.vl / 2) (c.u1 - c.vl) c.ql (natVal s.mem c.up c.u1) j
    (Asm.limbs S.mem c.qp c.ql) (Asm.limbs S.mem c.up c.u1)
  vk : S.mem.readLE c.vp (8 * c.vl) = s.mem.readLE c.vp (8 * c.vl)
  utl : S.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1)) = s.mem.readLE (c.up + 8 * c.u1) (8 * (c.ul - c.u1))
  bud : c.lo s + (j / (c.vl / 2) + 1) * c.K s ≤ bk

end FvModexp.Arm64.DivRec
