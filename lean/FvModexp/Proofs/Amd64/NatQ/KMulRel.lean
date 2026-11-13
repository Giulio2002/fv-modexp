import FvModexp.Proofs.Amd64.NatQ.MulDefs
import FvModexp.Proofs.Amd64.NatQ.KSqrB

set_option autoImplicit false

/-!
# [amd64 port (divmc s47) of the Q-form Arm64/NatQ/KMulRel.lean — TIGHT COSTS] `karatsuba` (amd64, go-bigmodexpfix natmul.go:164-218): the relation between the call segments

Frame (`RSP' = RSP - 448` after `PUSHQ BP; SUBQ $0x1b8`, entry `RSP`): return address at `RSP`, saved `BP` at `RSP - 8`;
locals (offsets from `RSP`): defer bit `-369` (`0x4f(SP')`, 1 byte), `zc - n2` at `-360` (`0x58`, holds `2·n2` until
`ty` is built), `n2` at `-344` (`0x68`), `ty`'s pointer `zp + 8·n2` at `-336` (`0x70`); the nine stack `*Int`s
`ty -328`, `tx -296`, `z1 -264`, `z2 -208`, `z0 -176`, `y1 -144`, `y0 -112`, `x1 -80`, `x0 -48` (`neg` byte, `abs` =
ptr/len/cap at `+8/+16/+24`); the open-coded defer record `{deferwrap1, stk, len(stk.w)}` at `-232, -224, -216`, its
address at `-16`; register-argument spills `stk, zp, zl, zc, xp` at `RSP + 32 … RSP + 64`; `y` is passed on the stack
at `RSP + 8/16/24` (`above = 72`).

`KN … M Lk bk spent` = the facts at every call boundary after the prologue (`z1 := stk.nat(2·n2 + 1)` in the scratch
`t`, the `tx`/`ty` headers built): the frame record, the four halves `x0 x1 y0 y1` (constant), the runtime invariant at
`(Lk, bk)` with `spent` charged, the stack (`len` raised by `rnd (2·n2+1)`, array kept or fresh), `t` apart from the
stack's header and free part, and the frames relative to the entry (writes only `z[0:2n]`, the entry stack's header /
free part, `R.rt` and the window). The writable `*Int`s (`ty tx z1` in `[RSP-328, RSP-232)`, `z2 z0` in
`[RSP-208, RSP-144)`) and the contents of `z`/`t` change between segments and are stated by each segment.

`KN.step`: a callee at `RSP - 456` (its window `[RSP-456-k, RSP-456+a)`, `a ≤ 80`) whose writes are in `z[0:2n]`, `t`,
the two writable header areas or the stack's header/free part, which brings the stack back, keeps `KN`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep IntAt apart_of_held globals_frame stackBack_keep' tls)

/-- the length of the scratch `z1` (`stk.nat(2·n2 + 1)`) -/
abbrev kT (n : Nat) : Nat := 2 * kh n + 1
/-- `karatsuba.deferwrap1` (the defer record's code pointer) -/
abbrev kDfn : Nat := 0x5f2340

/-- the facts of `KPre` by name (`len x = len y = n`, `len z = 2n`) -/
structure KPF (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State) : Prop where
  env : CallEnv R L s W 72
  hW : kW64 n ≤ W
  sv : Serves R
  gl : Globals R s.mem (win s W 72)
  wt : Outside NatAdd.wordT 16 R.rt
  n40 : 40 ≤ n
  zc2 : 2 * n ≤ zc
  xcn : n ≤ xc
  xc40 : xc < 2 ^ 40
  n12 : n ≤ 2 ^ 12
  xacc : s.mem.accessible xp (8 * n) false = true
  xh : Held R L xp (8 * xc)
  x48 : xp + 8 * xc ≤ 2 ^ 48
  xw : Outside xp (8 * n) (win s W 72)
  xs : StkSep s.mem st xp (8 * n)
  ycn : n ≤ yc
  yc40 : yc < 2 ^ 40
  yacc : s.mem.accessible yp (8 * n) false = true
  yh : Held R L yp (8 * yc)
  y48 : yp + 8 * yc ≤ 2 ^ 48
  yw : Outside yp (8 * n) (win s W 72)
  ys : StkSep s.mem st yp (8 * n)
  zc40 : zc < 2 ^ 40
  zlive : NatLive s.mem R L zp zc
  zw : Outside zp (8 * zc) (win s W 72)
  zg : Apart zp (8 * zc) (NatSqr.guard s) 8
  zt : Apart zp (8 * zc) (tls s) 8
  zs : StkSep s.mem st zp (8 * zc)
  slb : stLen s.mem st + 4 * (n + n) + 64 ≤ 2 ^ 16
  zx : Apart zp (8 * zc) xp (8 * n)
  zy : Apart zp (8 * zc) yp (8 * n)
  nex : zp + 8 * zc ≠ xp + 8 * xc
  ney : zp + 8 * zc ≠ yp + 8 * yc
  stk : StkPre R L s W 72 st
  lvH : stLen s.mem st + 4 * (n + n) + 64 ≤ H
  cost : KCQ n + stkR H s.mem st ≤ b
  adx : s.mem.accessible Callees.adxAddr 1 false = true
  inv : R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

theorem KPre.F {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    (h : KPre R b H L W st zp (2 * n) zc xp n xc yp n yc s) : KPF R b H L W st zp zc xp n xc yp yc s := by
  obtain ⟨henv, hW, hsv, hgl, hwt, h40, -, -, hzc, ⟨⟨hxl, hxc40, hx12, hxacc, hxh, hxw⟩,
    ⟨hyl, hyc40, -, hyacc, hyh, hyw⟩, ⟨hzc40, hzlive, hzw, hzg, -, -⟩, hslb⟩, hzx, hzy, hnex, hney, hsp, ⟨hlvH, hcost⟩,
    hadx, hinv⟩ := h
  have hn : 0 < n := by omega
  exact ⟨henv, hW, hsv, hgl, hwt, h40, hzc, hxl, hxc40, hx12, hxacc (by omega), (hxh (by omega)).1, (hxh (by omega)).2,
    (hxw hn).1, (hxw hn).2, hyl, hyc40, hyacc (by omega), (hyh (by omega)).1, (hyh (by omega)).2, (hyw hn).1, (hyw hn).2,
    hzc40, hzlive, hzw, (hzg (by omega)).1, (hzg (by omega)).2.1, (hzg (by omega)).2.2, hslb, hzx, hzy, hnex, hney, hsp, hlvH, hcost,
    hadx, hinv⟩

/-- the writes `karatsuba` may make (relative to the entry): `z[0:2n]` and the entry stack's header / free part -/
@[reducible] def kws (s : State) (st zp n : Nat) : List (Nat × Nat) := (zp, zp + 8 * (2 * n)) :: stkWs s.mem st

/-- see the module doc -/
structure KN (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 t : Nat) (Lk : List (Nat × Nat)) (bk spent : Nat) (M : Memory) : Prop where
  pre : KPre R b H L W st zp (2 * n) zc xp n xc yp n yc s
  -- the halves of `x` and `y` (normalised lengths)
  l0 : lx0 ≤ kh n
  v0 : natVal s.mem xp lx0 = natVal s.mem xp (kh n)
  nn0 : NatNorm s.mem xp lx0
  l1 : lx1 ≤ n - kh n
  v1 : natVal s.mem (xp + 8 * kh n) lx1 = natVal s.mem (xp + 8 * kh n) (n - kh n)
  nn1 : NatNorm s.mem (xp + 8 * kh n) lx1
  m0 : ly0 ≤ kh n
  w0 : natVal s.mem yp ly0 = natVal s.mem yp (kh n)
  mn0 : NatNorm s.mem yp ly0
  m1 : ly1 ≤ n - kh n
  w1 : natVal s.mem (yp + 8 * kh n) ly1 = natVal s.mem (yp + 8 * kh n) (n - kh n)
  mn1 : NatNorm s.mem (yp + 8 * kh n) ly1
  -- the scratch `t` (`z1`'s array)
  scr : Scr R L Lk s.mem s.mem st t (kT n)
  tsep : StkSep M st t (8 * kT n)
  -- runtime
  ext : LiveExt R L Lk
  bud : b - (spent + stkR H s.mem st) + stkR H M st ≤ bk
  spk : spent ≤ KCQ n
  inv : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk M)
  reg : M.regions = s.mem.regions
  fr : MemFrame s.mem M (R.rt ++ win s W 72 ++ kws s st zp n)
  lf : LiveFrame s.mem M L (kws s st zp n)
  -- the stack
  sok : StkOK M R Lk st
  slen : stLen M st = stLen s.mem st + StackNat.rnd (kT n)
  sarr : (stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)
  smem : ArrIn Lk st s.mem M
  -- the frame record
  lr : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  fp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  bit : M.readLE ((s.regs 4).toNat - 369) 1 = 1
  q88 : M.readLE ((s.regs 4).toNat - 360) 8 = zc - kh n
  q104 : M.readLE ((s.regs 4).toNat - 344) 8 = kh n
  q112 : M.readLE ((s.regs 4).toNat - 336) 8 = zp + 8 * kh n
  dfn : M.readLE ((s.regs 4).toNat - 232) 8 = kDfn
  dst : M.readLE ((s.regs 4).toNat - 224) 8 = st
  dln : M.readLE ((s.regs 4).toNat - 216) 8 = stLen s.mem st
  dpt : M.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 232
  s1 : M.readLE ((s.regs 4).toNat + 32) 8 = st
  s2 : M.readLE ((s.regs 4).toNat + 40) 8 = zp
  s3 : M.readLE ((s.regs 4).toNat + 48) 8 = 2 * n
  s4 : M.readLE ((s.regs 4).toNat + 56) 8 = zc
  s5 : M.readLE ((s.regs 4).toNat + 64) 8 = xp
  x0h : IntAt M ((s.regs 4).toNat - 48) 0 xp lx0 xc
  x1h : IntAt M ((s.regs 4).toNat - 80) 0 (xp + 8 * kh n) lx1 (xc - kh n)
  y0h : IntAt M ((s.regs 4).toNat - 112) 0 yp ly0 yc
  y1h : IntAt M ((s.regs 4).toNat - 144) 0 (yp + 8 * kh n) ly1 (yc - kh n)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}

theorem KN.F (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    KPF R b H L W st zp zc xp n xc yp yc s := h.pre.F

/-- the window facts of the entry -/
theorem KN.lay (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    5424 ≤ W ∧ W ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat + 72 ≤ 2 ^ 48 ∧ 40 ≤ n ∧ n ≤ 2 ^ 12 ∧
      n ≤ xc ∧ xc < 2 ^ 40 ∧ n ≤ yc ∧ yc < 2 ^ 40 ∧ 2 * n ≤ zc ∧ zc < 2 ^ 40 ∧
      Outside ((s.regs 4).toNat - W) (W + 72) R.rt ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
      Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - W) (W + 72) := by
  have F := h.F
  obtain ⟨-, ⟨hb, ha, -⟩, hal, -, hout, hga, hgr, -, -, -⟩ := F.env
  have := kW64_ge n
  exact ⟨by have := F.hW; omega, hb, hal, ha, F.n40, F.n12, F.xcn, F.xc40, F.ycn, F.yc40, F.zc2, F.zc40, hout, hgr, hga⟩

/-- the ranges a callee at `RSP - 456` may write besides `R.rt` and its window: `z[0:2n]`, `t`, the two writable
header areas, the stack's current header and free part -/
def KNWs (s : State) (M : Memory) (st zp n t : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ r ∈ ws, r.1 ≤ r.2 ∧ ((zp ≤ r.1 ∧ r.2 ≤ zp + 8 * (2 * n)) ∨ (t ≤ r.1 ∧ r.2 ≤ t + 8 * kT n) ∨
    ((s.regs 4).toNat - 328 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 232) ∨ ((s.regs 4).toNat - 208 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 144) ∨
    (st ≤ r.1 ∧ r.2 ≤ st + 24) ∨
    (stW M st + 8 * stLen M st ≤ r.1 ∧ r.2 ≤ stW M st + 8 * stCap M st))

theorem KNWs.append {s : State} {M : Memory} {st zp n t : Nat} {ws ws' : List (Nat × Nat)}
    (h : KNWs s M st zp n t ws) (h' : KNWs s M st zp n t ws') : KNWs s M st zp n t (ws ++ ws') := by
  intro r hr; rcases List.mem_append.1 hr with hr | hr
  · exact h r hr
  · exact h' r hr

/-- the stack's current free part lies in the entry's free part, or is fresh -/
theorem KN.free (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    (stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st ∧ stLen s.mem st ≤ stLen M st) ∨
      (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L) := by
  rcases h.sarr with ⟨e1, e2⟩ | h2
  · exact Or.inl ⟨e1, e2, by rw [h.slen]; omega⟩
  · exact Or.inr h2

/-- every write range is in a header area of the frame, inside a range of `kws`, or fresh -/
theorem KN.wcls (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {ws : List (Nat × Nat)}
    (hws : KNWs s M st zp n t ws) :
    ∀ r ∈ ws, r.1 ≤ r.2 ∧ (((s.regs 4).toNat - 328 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 232) ∨
      ((s.regs 4).toNat - 208 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 144) ∨ (∃ q ∈ kws s st zp n, q.1 ≤ r.1 ∧ r.2 ≤ q.2) ∨
      (InRanges r.1 (r.2 - r.1) R.rt ∧ ApartAll r.1 (r.2 - r.1) L)) := by
  intro r hr
  obtain ⟨hle, hc⟩ := hws r hr
  refine ⟨hle, ?_⟩
  rcases hc with hc | hc | hc | hc | hc | hc
  · exact Or.inr (Or.inr (Or.inl ⟨_, List.mem_cons_self, hc.1, hc.2⟩))
  · rcases h.scr.loc with ⟨-, h1, h2⟩ | ⟨hin, hap⟩
    · exact Or.inr (Or.inr (Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        by simp only; omega, by simp only; omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩))
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hc.1, hc.2⟩))
  · rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, hap⟩
    · rw [e1, e2] at hc
      have := h.sok.2.2.2.2.2.1
      exact Or.inr (Or.inr (Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        by simp only; omega, by simp only; omega⟩))
    · have := h.sok.2.2.2.2.2.1
      exact Or.inr (Or.inr (Or.inr ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩))

/-- the ranges of `kws` are outside the window -/
theorem KN.kwsOut (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    ∀ q ∈ kws s st zp n, q.2 ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 72 ≤ q.1 := by
  have F := h.F
  have hzw := F.zw
  have hzl := F.zc2
  obtain ⟨-, -, hstw, -, -, -, hfw, -⟩ := F.stk
  simp only [win, outside_cons, outside_nil, and_true] at hzw hstw hfw
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw
  intro q hq
  simp only [kws, stkWs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> simp only <;> omega

theorem KN.wsep (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    LiveSep L (win s W 72) :=
  h.F.env.2.2.2.2.2.2.2.1

/-- a frame read that survives a callee's writes (window above `RSP - 376`, outside both header areas and the callee's
other writes) -/
theorem kn_rd {rt ws : List (Nat × Nat)} {M M' : Memory} {sp W k a x m : Nat} (hk : 456 + k ≤ W) (ha : a ≤ 80)
    (hWs : W ≤ sp) (hout : Outside (sp - W) (W + 72) rt)
    (hF : MemFrame M M' (rt ++ [(sp - 456 - k, sp - 456 + a)] ++ ws))
    (hws : Outside x m ws) (h1 : sp - 376 ≤ x) (h2 : x + m ≤ sp + 72) :
    M'.readLE x m = M.readLE x m := by
  refine hF.readLE _ _ ?_
  simp only [outside_append, outside_cons, outside_nil, and_true]
  exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, hws⟩

set_option maxRecDepth 20000 in
/-- **A callee at `RSP - 456` keeps `KN`**: it wrote `R.rt`, its window (inside ours, below the locals) and `KNWs`
ranges, extended the live set, charged at most `c`, and brought the stack back. -/
theorem KN.step (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {M' : Memory} {k a : Nat}
    (hk : 456 + k ≤ W) (ha : a ≤ 80) {ws : List (Nat × Nat)} (hws : KNWs s M st zp n t ws)
    (hF : MemFrame M M' (R.rt ++ [((s.regs 4).toNat - 456 - k, (s.regs 4).toNat - 456 + a)] ++ ws)) (hLF : LiveFrame M M' Lk ws) (hreg : M'.regions = M.regions)
    {Lk' : List (Nat × Nat)} {bk' c : Nat} (hext : LiveExt R Lk Lk')
    (hb : bk - (c + stkR H M st) + stkR H M' st ≤ bk' ∨ (bk - c ≤ bk' ∧ stCap M' st = stCap M st))
    (hc : spent + c ≤ KCQ n)
    (hinv : R.inv bk' Lk' (s.regs 14).toNat (view R.rt Lk' M')) (hsb : StackBackL R Lk Lk' st M M') :
    KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk' bk' (spent + c) M' := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, -, -, hout, -, -⟩ := h.lay
  have hcl := h.wcls hws
  have hko := h.kwsOut
  have hLs := h.wsep
  -- a read in our window above the callee's, outside both header areas, is unchanged
  have hrd : ∀ x m, (s.regs 4).toNat - 376 ≤ x → x + m ≤ (s.regs 4).toNat + 72 →
      (x + m ≤ (s.regs 4).toNat - 328 ∨ (s.regs 4).toNat - 232 ≤ x) → (x + m ≤ (s.regs 4).toNat - 208 ∨ (s.regs 4).toNat - 144 ≤ x) →
      M'.readLE x m = M.readLE x m := by
    intro x m h1 h2 h4 h5
    refine kn_rd hk ha hWs hout hF (outside_of_forall fun r hr => ?_) h1 h2
    obtain ⟨hle, hc⟩ := hcl r hr
    rcases hc with hc | hc | ⟨q, hq, q1, q2⟩ | ⟨hin, -⟩
    · omega
    · omega
    · have := hko q hq; omega
    · have := NatSub.outside_of_inRanges (hout.of_sub (a := x) (n := m) (by omega) (by omega)) hin; omega
  -- the stack after the call
  obtain ⟨⟨hok', hlen', harr'⟩, hmem'⟩ := hsb
  have hsarr : (stW M' st = stW s.mem st ∧ stCap M' st = stCap s.mem st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L) := by
    rcases harr' with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · rw [e1, e2]; exact h.sarr
    · exact Or.inr ⟨hin, fun r hr => hap r (h.ext.mem_old hr)⟩
  have htsep : StkSep M' st t (8 * kT n) := by
    refine ⟨h.tsep.1, ?_, h.tsep.2.2⟩
    rcases harr' with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · simp only [BasicSqr.freeP, BasicSqr.freeN] at h ⊢
      have := h.tsep.2.1; simp only [BasicSqr.freeP, BasicSqr.freeN] at this
      rw [e1, e2, hlen']; exact this
    · have hap' := apart_of_held h.scr.held hin hap
      have := h.sok.2.2.2.2.2.1
      have hl := hok'.2.2.2.2.2.1
      simp only [BasicSqr.freeP, BasicSqr.freeN]
      unfold Apart at hap' ⊢; omega
  have R2 : ∀ x m, (s.regs 4).toNat - 376 ≤ x → x + m ≤ (s.regs 4).toNat - 328 → M'.readLE x m = M.readLE x m :=
    fun x m h1 h2 => hrd x m h1 (by omega) (Or.inl h2) (Or.inl (by omega))
  have R3 : ∀ x m, (s.regs 4).toNat - 232 ≤ x → x + m ≤ (s.regs 4).toNat - 208 → M'.readLE x m = M.readLE x m :=
    fun x m h1 h2 => hrd x m (by omega) (by omega) (Or.inr h1) (Or.inl h2)
  have R4 : ∀ x m, (s.regs 4).toNat - 144 ≤ x → x + m ≤ (s.regs 4).toNat + 72 → M'.readLE x m = M.readLE x m :=
    fun x m h1 h2 => hrd x m (by omega) h2 (Or.inr (by omega)) (Or.inr h1)
  have I4 : ∀ {a ng p l c' : Nat}, (s.regs 4).toNat - 144 ≤ a → a + 32 ≤ (s.regs 4).toNat - 16 → IntAt M a ng p l c' →
      IntAt M' a ng p l c' := fun h1 h2 hh => NatSqr.IntAt.keep hh fun x m q1 q2 => R4 x m (by omega) (by omega)
  refine
    { pre := h.pre, l0 := h.l0, v0 := h.v0, nn0 := h.nn0, l1 := h.l1, v1 := h.v1, nn1 := h.nn1,
      m0 := h.m0, w0 := h.w0, mn0 := h.mn0, m1 := h.m1, w1 := h.w1, mn1 := h.mn1,
      scr := { h.scr with held := hext.held h.scr.held }, tsep := htsep, ext := h.ext.trans hext,
      bud := ?_, spk := hc, inv := hinv, reg := hreg.trans h.reg, fr := ?_, lf := ?_, sok := hok',
      slen := by rw [hlen']; exact h.slen, sarr := hsarr, smem := h.smem.trans hmem' hext,
      lr := by rw [R4 _ _ (by omega) (by omega)]; exact h.lr,
      fp := by rw [R4 _ _ (by omega) (by omega)]; exact h.fp,
      bit := by rw [R2 _ _ (by omega) (by omega)]; exact h.bit,
      q88 := by rw [R2 _ _ (by omega) (by omega)]; exact h.q88,
      q104 := by rw [R2 _ _ (by omega) (by omega)]; exact h.q104,
      q112 := by rw [R2 _ _ (by omega) (by omega)]; exact h.q112,
      dfn := by rw [R3 _ _ (by omega) (by omega)]; exact h.dfn,
      dst := by rw [R3 _ _ (by omega) (by omega)]; exact h.dst,
      dln := by rw [R3 _ _ (by omega) (by omega)]; exact h.dln,
      dpt := by rw [R4 _ _ (by omega) (by omega)]; exact h.dpt,
      s1 := by rw [R4 _ _ (by omega) (by omega)]; exact h.s1,
      s2 := by rw [R4 _ _ (by omega) (by omega)]; exact h.s2,
      s3 := by rw [R4 _ _ (by omega) (by omega)]; exact h.s3,
      s4 := by rw [R4 _ _ (by omega) (by omega)]; exact h.s4,
      s5 := by rw [R4 _ _ (by omega) (by omega)]; exact h.s5,
      x0h := I4 (by omega) (by omega) h.x0h, x1h := I4 (by omega) (by omega) h.x1h,
      y0h := I4 (by omega) (by omega) h.y0h, y1h := I4 (by omega) (by omega) h.y1h }
  · have h0 := h.bud; have h1 := h.F.cost
    rcases hb with hb | ⟨hb, hcp⟩
    · omega
    · rw [stkR_congr hcp]; omega
  · refine h.fr.trans hF fun x m ho => ⟨ho, ?_⟩
    rw [outside_append, outside_append] at ho
    obtain ⟨⟨hrt, hwa⟩, hz⟩ := ho
    simp only [win, outside_cons, outside_nil, and_true] at hwa
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hrt, by omega⟩, outside_of_forall fun r hr => ?_⟩
    obtain ⟨hle, hc⟩ := hcl r hr
    rcases hc with hc | hc | ⟨q, hq, q1, q2⟩ | ⟨hin, -⟩
    · omega
    · omega
    · have := MemFrame.outside_mem hz hq; omega
    · have := NatSub.outside_of_inRanges hrt hin; omega
  · refine ⟨fun x m hin hz => ?_⟩
    rw [hLF.readLE x m (h.ext.inRanges_old hin) (outside_of_forall fun r hr => ?_)]
    · exact h.lf.readLE x m hin hz
    · obtain ⟨hle, hc⟩ := hcl r hr
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      rcases hc with hc | hc | ⟨q', hq', q1, q2⟩ | ⟨-, hap⟩
      · have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this; omega
      · have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this; omega
      · have := MemFrame.outside_mem hz hq'; omega
      · have := hap q hq; unfold Apart at this; omega

/-- the read-only data stays loaded -/
theorem KN.dl (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    Extracted.program.DataLoaded M := by
  have F := h.F
  obtain ⟨-, ⟨hb, ha', hw⟩, hal, hdl, -, -, -, -, hro, -⟩ := F.env
  simp only [regSP] at hb ha' hw
  have hzl := F.zc2
  have hzlive := F.zlive
  obtain ⟨-, ⟨-, -, hsacc, -, hnl, hlc, -⟩, -⟩ := F.stk
  have hfr : MemFrame s.mem M (R.rt ++ (win s W 72 ++ kws s st zp n)) := by
    rw [← List.append_assoc]; exact h.fr
  refine dataLoaded_frame64 hdl h.reg hro hfr fun r hr hlt => ?_
  simp only [win, kws, stkWs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
  · obtain ⟨-, -, hacc, -⟩ := hzlive (by simp only at hlt; omega)
    exact Janus.Arm64.Memory.accessible_mono _ hacc (by simp only; omega) (by simp only; omega)
  · exact Janus.Arm64.Memory.accessible_mono _ hsacc (by simp only; omega) (by simp only; omega)
  · simp only at hlt
    obtain ⟨-, -, hacc, -⟩ := hnl (by omega)
    exact Janus.Arm64.Memory.accessible_mono _ hacc (by simp only; omega) (by simp only; omega)

/-- the stack-guard word keeps its value -/
theorem KN.grd (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    M.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, -, -, hout, hgr, hga⟩ := h.lay
  have F := h.F
  have hzg := F.zg
  have hzl := F.zc2
  obtain ⟨-, -, -, hstg, -, hfg, -⟩ := F.stk
  simp only [NatSqr.guard, BasicSqr.freeP, BasicSqr.freeN] at hzg hstg hfg
  unfold Apart at hzg hstg hfg hga
  refine h.fr.readLE _ _ ?_
  simp only [win, kws, stkWs, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨hgr, by omega⟩, by omega, by omega, by omega⟩

/-- the TLS slot keeps its value (amd64) -/
theorem KN.tlsv (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    M.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
  have F := h.F
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, htrt, htw⟩⟩ := F.env
  have hzt := F.zt
  have hzl := F.zc2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hstt, -, hft⟩ := F.stk
  simp only [tls, BasicSqr.freeP, BasicSqr.freeN] at hzt hstt hft
  unfold Apart at hzt hstt hft htw
  refine h.fr.readLE _ _ ?_
  simp only [win, kws, stkWs, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨htrt, by omega⟩, by omega, by omega, by omega⟩

/-- the call environment of a callee at `RSP - 456` (window inside ours, below the locals) -/
theorem KN.callee (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {S1 : State}
    {stk1 above1 : Nat} (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456) (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = M)
    (hfs : S1.fsBase = s.fsBase) (hk : 456 + stk1 ≤ W) (ha : above1 ≤ 80) : CallEnv R Lk S1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha', hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := h.F.env
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb ha' hw
  unfold Apart at hga htw
  have hgrd := h.grd
  have htv := h.tlsv
  obtain ⟨ns, hLk, hn, -⟩ := h.ext
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [stackguard0Offset, regG]; rw [hg]; exact hg1
  · simp only [stackguard0Offset, regG]; rw [hg, hm, h.fr.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [hg, hm, hgrd, hsp]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; rw [hm, h.fr.accessible, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · omega
  · rw [hm]; exact h.dl
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr
    simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]
    rw [hLk] at hr
    rcases List.mem_append.1 hr with hr | hr
    · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · have := NatSub.outside_of_inRanges hout (hn r hr).1; omega
  · rw [hfs]; exact htb
  · rw [hfs, hm, h.fr.accessible]; exact htr
  · rw [hfs, hm, htv, htg, hg]
  · rw [hfs]; exact htrt
  · rw [hfs, hsp]; unfold Apart; omega

/-- the stack's current array and free part are apart from the TLS slot (amd64) -/
theorem KN.stkT (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    (0 < stCap M st → Apart (stW M st) (8 * stCap M st) (tls s) 8) ∧
    Apart (BasicSqr.freeP M st) (BasicSqr.freeN M st) (tls s) 8 := by
  have F := h.F
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, htrt, -⟩⟩ := F.env
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hsatl, hftl⟩ := F.stk
  have hlc := h.sok.2.2.2.2.2.1
  simp only [tls, BasicSqr.freeP, BasicSqr.freeN] at hsatl hftl hlc ⊢
  rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, -⟩
  · simp only [e1, e2] at hlc ⊢
    refine ⟨hsatl, ?_⟩
    have := hftl; unfold Apart at this ⊢; omega
  · have hto := NatSub.outside_of_inRanges htrt hin
    exact ⟨fun _ => by unfold Apart; omega, by unfold Apart; omega⟩

/-- the stack's current array and free part: outside the window, apart from the guard word and the header, held -/
theorem KN.stk (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    (0 < stCap M st → Outside (stW M st) (8 * stCap M st) (win s W 72) ∧
      Apart (stW M st) (8 * stCap M st) (NatSqr.guard s) 8) ∧
    Apart (BasicSqr.freeP M st) (BasicSqr.freeN M st) (NatSqr.guard s) 8 ∧
    Outside (BasicSqr.freeP M st) (BasicSqr.freeN M st) (win s W 72) ∧
    Apart st 24 (BasicSqr.freeP M st) (BasicSqr.freeN M st) ∧ Held R Lk (BasicSqr.freeP M st) (BasicSqr.freeN M st) ∧
    Apart (BasicSqr.freeP M st) (BasicSqr.freeN M st) RunIface.gA 32 := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, -, -, hout, hgr, hga⟩ := h.lay
  have F := h.F
  have hgrt : Outside RunIface.gA 32 R.rt := F.gl.2.2.2.2.2.2.2.2.1
  obtain ⟨-, ⟨-, hsth, -, -, -, hlc0, -⟩, -, -, hsarr, hfg, hfw, hstf, -, hfh, -, hfgA⟩ := F.stk
  have hlc := h.sok.2.2.2.2.2.1
  have hnl := h.sok.2.2.2.2.1
  simp only [NatSqr.guard, BasicSqr.freeP, BasicSqr.freeN] at hfg hfw hstf hfh hsarr hfgA ⊢
  rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, hap⟩
  · rw [e1, e2] at hnl ⊢; rw [e2] at hlc
    refine ⟨hsarr, ?_, ?_, ?_, h.ext.held (hfh.sub (by omega) (by omega)), ?_⟩
    · unfold Apart at hfg ⊢; omega
    · exact hfw.of_sub (by omega) (by omega)
    · unfold Apart at hstf ⊢; omega
    · unfold Apart at hfgA ⊢; omega
  · have hgo := NatSub.outside_of_inRanges hgr hin
    have hst := apart_of_held hsth hin hap
    have hcap : 0 < stCap M st := by
      have := h.slen; simp only [StackNat.rnd, kT] at this; omega
    obtain ⟨-, hh, -, -⟩ := hnl hcap
    have hw : ∀ a k, stW M st ≤ a → a + k ≤ stW M st + 8 * stCap M st → Outside a k (win s W 72) := by
      intro a k h1 h2
      have := NatSub.outside_of_inRanges (hout.of_sub (a := (s.regs 4).toNat - W) (n := W + 72) (by omega) (by omega)) hin
      simp only [win, outside_cons, outside_nil, and_true]; omega
    refine ⟨fun _ => ⟨hw _ _ (by omega) (by omega), by unfold Apart; omega⟩, by unfold Apart; omega,
      hw _ _ (by omega) (by omega), by unfold Apart at hst ⊢; omega, hh.sub (by omega) (by omega), ?_⟩
    have := NatSub.outside_of_inRanges hgrt hin
    unfold Apart; omega

/-- a range outside our window is outside an inner window (`RSP - 456`, `W' + 456 ≤ W`, above `≤ 80`) -/
theorem KN.winIn (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {S1 : State} {W' a : Nat}
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456) (hk : 456 + W' ≤ W) (ha : a ≤ 80) {x k : Nat}
    (hx : Outside x k (win s W 72)) : Outside x k (win S1 W' a) := by
  obtain ⟨hW, hWs, -⟩ := h.lay
  simp only [win, outside_cons, outside_nil, and_true] at hx ⊢; rw [hsp]; omega

/-- **`StkPre` at an inner call** (`RSP - 456`, window `W' + 456 ≤ W`, above `≤ 80`) -/
theorem KN.stkPre (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {S1 : State} {W' a : Nat}
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456) (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = M)
    (hfs : S1.fsBase = s.fsBase) (hk : 456 + W' ≤ W) (ha : a ≤ 80) : StkPre R Lk S1 W' a st := by
  obtain ⟨hst0, -, hstw, hstg, -, -, -, -, hstwb, -, hsgA, -, hsttl, -, -⟩ := h.F.stk
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.stk
  obtain ⟨t1, t2⟩ := h.stkT
  have hwin : ∀ x k, Outside x k (win s W 72) → Outside x k (win S1 W' a) := fun x k hx => h.winIn hsp hk ha hx
  subst hm
  simp only [StkPre, NatSqr.guard, tls, hg, hfs] at h1 h2 hstg hsttl t1 t2 ⊢
  exact ⟨hst0, h.sok, hwin _ _ hstw, hstg, fun hc => ⟨hwin _ _ (h1 hc).1, (h1 hc).2⟩, h2, hwin _ _ h3, h4, hstwb, h5,
    hsgA, h6, hsttl, t1, t2⟩

/-- the threshold globals at `M` -/
theorem KN.glob (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {w' : List (Nat × Nat)}
    (hw : ∀ x k, Outside x k (win s W 72) → Outside x k w') : Globals R M w' := by
  have F := h.F
  have hgl := F.gl
  have hzs := F.zs
  have hzl := F.zc2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsgA, hfgA⟩ := F.stk
  have hgw : Outside RunIface.gA 32 (win s W 72) := hgl.2.2.2.2.2.2.2.2.2.1
  have hfr : MemFrame s.mem M (R.rt ++ (win s W 72 ++ kws s st zp n)) := by
    rw [← List.append_assoc]; exact h.fr
  refine globals_frame hgl hfr ?_ hw
  have hz := hzs.2.2
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfgA
  simp only [win, outside_cons, outside_nil, and_true] at hgw
  unfold Apart at hz hsgA hfgA
  simp only [win, kws, stkWs, outside_append, outside_cons, outside_nil, and_true]
  omega

/-- a range separated from the entry stack (and held) is separated from the current one -/
theorem KN.sepOf (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {p k : Nat}
    (hs : StkSep s.mem st p k) (hh : Held R L p k) : StkSep M st p k := by
  refine ⟨hs.1, ?_, hs.2.2⟩
  have hf := hs.2.1
  have hlc := h.sok.2.2.2.2.2.1
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hf hlc ⊢
  rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, hap⟩
  · rw [e2] at hlc; rw [e1, e2]; unfold Apart at hf ⊢; omega
  · have := apart_of_held hh hin hap; unfold Apart at this ⊢; omega

/-- `x` is never written -/
theorem KN.xrd (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {a k : Nat} (h1 : xp ≤ a)
    (h2 : a + k ≤ xp + 8 * n) : M.readLE a k = s.mem.readLE a k := by
  have F := h.F
  have hxh := F.xh
  have hxw := F.xw
  have hzx := F.zx
  have hxc := F.xcn
  have hzl := F.zc2
  obtain ⟨hs1, hs2, -⟩ := F.xs
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hs2
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  unfold Apart at hzx hs1 hs2
  refine Held.readLE2 (hxh.sub (by omega) (by omega)) h.fr h.lf ?_ ?_
  · simp only [win, outside_cons, outside_nil, and_true]; omega
  · simp only [kws, stkWs, outside_cons, outside_nil, and_true]; omega

/-- `y` is never written -/
theorem KN.yrd (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {a k : Nat} (h1 : yp ≤ a)
    (h2 : a + k ≤ yp + 8 * n) : M.readLE a k = s.mem.readLE a k := by
  have F := h.F
  have hyh := F.yh
  have hyw := F.yw
  have hzy := F.zy
  have hyc := F.ycn
  have hzl := F.zc2
  obtain ⟨hs1, hs2, -⟩ := F.ys
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hs2
  simp only [win, outside_cons, outside_nil, and_true] at hyw
  unfold Apart at hzy hs1 hs2
  refine Held.readLE2 (hyh.sub (by omega) (by omega)) h.fr h.lf ?_ ?_
  · simp only [win, outside_cons, outside_nil, and_true]; omega
  · simp only [kws, stkWs, outside_cons, outside_nil, and_true]; omega

/-- what is left of the budget -/
theorem KN.costQ (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {c : Nat}
    (hc : spent + c ≤ KCQ n) : c + stkR H M st ≤ bk := by
  have hb := h.F.cost
  have := h.bud; omega

/-- what is left of the budget -/
theorem KN.cost (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {c : Nat}
    (hc : spent + c ≤ KCQ n) : c ≤ bk := by
  have := h.costQ hc; omega

theorem KN.weaken (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {spent' : Nat}
    (hs : spent ≤ spent') (hs' : spent' ≤ KCQ n) : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent' M :=
  { h with bud := by have := h.bud; omega, spk := hs' }

/-- the live set is apart from our window -/
theorem KN.lsep (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    ∀ r ∈ Lk, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 72 ≤ r.1 := by
  obtain ⟨-, -, -, -, hout, -, -, hLs, -⟩ := h.F.env
  obtain ⟨ns, hLk, hn, -⟩ := h.ext
  intro r hr
  rw [hLk] at hr
  rcases List.mem_append.1 hr with hr | hr
  · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  · have := NatSub.outside_of_inRanges hout (hn r hr).1; omega

end

/-- the registers at a segment boundary (`RSP' = RSP - 448`, frame pointer `RSP - 8`) -/
@[reducible] def KNAt (s S : State) (pc : Nat) : Prop :=
  S.rip = BitVec.ofNat 64 pc ∧ S.regs 4 = s.regs 4 - 448#64 ∧ S.regs 14 = s.regs 14 ∧ S.regs 5 = s.regs 4 - 8#64 ∧
    S.fsBase = s.fsBase ∧ S.df = s.df ∧ S.xmm 15 = s.xmm 15

/-- the goal of every segment -/
@[reducible] def KNGoal (impl : List Amd64.Segment) (R : RtInv) (H b : Nat) (L : List (Nat × Nat)) (W st zp xp n yp : Nat)
    (s S : State) : Prop :=
  ReachesRet (LibMul.program.link impl) (retAddrOf s) S fun s' =>
    Kept s s' ∧ KPost R b H L W st zp (2 * n) xp n yp n s s'

/-- the values of the halves -/
@[reducible] def kX0 (s : State) (xp n : Nat) : Nat := natVal s.mem xp (kh n)
@[reducible] def kX1 (s : State) (xp n : Nat) : Nat := natVal s.mem (xp + 8 * kh n) (n - kh n)

/-- the budget charged after each call (`ℓ` the entry stack length): `stk.nat`, `tx.Sub`, `ty.Sub`, the three inner
products, the two `z1.Add` -/
def kcI (n : Nat) : Nat := MCQ (kh n) (kh n)
def kc1 (_n : Nat) : Nat := 0
def kc2 (n : Nat) : Nat := kc1 n + asB (kT n)
def kc2b (n : Nat) : Nat := kc2 n + asB (kT n)
def kc3 (n : Nat) : Nat := kc2b n + kcI n
def kc4 (n : Nat) : Nat := kc3 n + kcI n
def kc5 (n : Nat) : Nat := kc4 n + kcI n
def kc6 (n : Nat) : Nat := kc5 n + asB (kT n)
def kc7 (n : Nat) : Nat := kc6 n + asB (kT n)

theorem kc7_le (n : Nat) : kc7 n ≤ KCQ n := by
  unfold kc7 kc6 kc5 kc4 kc3 kc2b kc2 kc1 kcI KCQ; simp only [kT]; omega

end FvModexp.Amd64.Q.NatMul
