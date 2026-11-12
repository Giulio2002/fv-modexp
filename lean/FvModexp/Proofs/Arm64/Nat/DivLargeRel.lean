import FvModexp.Proofs.Arm64.Nat.DivLargePro

/-!
# `divLarge` (arm64): the segment relations after `v := stk.nat(n)`

`AfterNat`: the return of `(*stack).nat` (`fn + 0xcc`); `Env`: the facts fixed from then on (scratch `v` at `t`, live set
`L1`, budget `b1`, stack array `(w1, c1)`); `Mem`: the memory facts kept by every later segment (frame slots, spills,
stack header, `vIn` unchanged, written ranges, invariant).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivLarge

/-- the facts at the return of `stk.nat(n)` (state `S2`; `P` the state at the call) -/
structure AfterNat (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (st vl : Nat) (s P S2 : State) (stkSN abSN : Nat)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop where
  pc : S2.pc = BitVec.ofNat 64 (callNat + 4)
  sp : S2.sp = s.sp - 304#64
  r28 : S2.regs 28 = s.regs 28
  r29 : S2.regs 29 = s.sp - 312#64
  r18 : S2.regs 18 = s.regs 18
  r0 : S2.regs 0 = BitVec.ofNat 64 (stW S2.mem st + 8 * stLen s.mem st)
  r1 : S2.regs 1 = BitVec.ofNat 64 vl
  r2 : S2.regs 2 = BitVec.ofNat 64 vl
  ext : LiveExt R L L1
  bud : b - stackNatCost (stLen s.mem st) vl ≤ b1
  inv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 S2.mem)
  ok : StkOK S2.mem R L1 st
  len : stLen S2.mem st = stLen s.mem st + StackNat.rnd vl
  same : stLen s.mem st + StackNat.rnd vl ≤ stCap s.mem st →
    stW S2.mem st = stW s.mem st ∧ stCap S2.mem st = stCap s.mem st
  grow : stCap s.mem st < stLen s.mem st + StackNat.rnd vl →
    InRanges (stW S2.mem st) (8 * stCap S2.mem st) R.rt ∧ ApartAll (stW S2.mem st) (8 * stCap S2.mem st) L
  F2 : MemFrame P.mem S2.mem (R.rt ++ [(s.sp.toNat - 304 - stkSN, s.sp.toNat - 312),
    (s.sp.toNat - 296, s.sp.toNat - 304 + abSN)] ++ stkWs s.mem st)
  LF2 : LiveFrame P.mem S2.mem L (stkWs s.mem st)

/-- the facts fixed from the `stk.nat` call on: the scratch `v` at `t` (`n` words), the live set `L1`, the budget `b1`,
the stack array `(w1, c1)` -/
structure Env (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) : Prop where
  pre : Pre R b L c zp zc st up uc ip il vp vl s
  t_eq : t = w1 + 8 * stLen s.mem st
  scr : Scr R L L1 s.mem s.mem st t vl
  ext : LiveExt R L L1
  bud : b - stackNatCost (stLen s.mem st) vl ≤ b1
  arr : (w1 = stW s.mem st ∧ c1 = stCap s.mem st) ∨ (InRanges w1 (8 * c1) R.rt ∧ ApartAll w1 (8 * c1) L)
  c1len : stLen s.mem st + StackNat.rnd vl ≤ c1
  c1b : c1 < 2 ^ 40
  w1live : NatLive s.mem R L1 w1 c1

/-- a nat's array as a written range (none when `cap = 0`: the pointer of an empty nat is arbitrary) -/
@[reducible] def ar (p c : Nat) : List (Nat × Nat) := if 0 < c then [(p, p + 8 * c)] else []

/-- the ranges written after the `stk.nat` call: the scratch `v`, `z`'s and `u`'s arrays -/
@[reducible] def wsL (zp zc up uc vl t : Nat) : List (Nat × Nat) :=
  (t, t + 8 * vl) :: (ar zp zc ++ ar up uc)

/-- the memory facts at every point after the `stk.nat` call (memory `M`, live set `Lk`, budget `bk`) -/
structure Mem (R : RtInv) (L : List (Nat × Nat)) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) : Prop where
  lr : M.readLE (s.sp.toNat - 304) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 312) 8 = (s.regs 29).toNat
  dbit : M.readLE (s.sp.toNat - 201) 1 = 1
  vtop : M.readLE (s.sp.toNat - 168) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8
  il1 : M.readLE (s.sp.toNat - 136) 8 = il + 1
  mm : M.readLE (s.sp.toNat - 128) 8 = il - vl
  vt : M.readLE (s.sp.toNat - 96) 8 = t
  vn1 : M.readLE (s.sp.toNat - 160) 8 = vl
  vn2 : M.readLE (s.sp.toNat - 152) 8 = vl
  dfn : M.readLE (s.sp.toNat - 40) 8 = dfnL
  dst : M.readLE (s.sp.toNat - 32) 8 = st
  dn : M.readLE (s.sp.toNat - 24) 8 = stLen s.mem st
  dp : M.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 40
  s1 : M.readLE (s.sp.toNat + 8) 8 = zp
  s3 : M.readLE (s.sp.toNat + 24) 8 = zc
  s4 : M.readLE (s.sp.toNat + 32) 8 = st
  s5 : M.readLE (s.sp.toNat + 40) 8 = up
  s7 : M.readLE (s.sp.toNat + 56) 8 = uc
  s8 : M.readLE (s.sp.toNat + 64) 8 = ip
  s9 : M.readLE (s.sp.toNat + 72) 8 = il
  s10 : M.readLE (s.sp.toNat + 80) 8 = ic
  s11 : M.readLE (s.sp.toNat + 88) 8 = vp
  s12 : M.readLE (s.sp.toNat + 96) 8 = vl
  s13 : M.readLE (s.sp.toNat + 104) 8 = vc
  hw : M.readLE st 8 = w1
  hlen : M.readLE (st + 8) 8 = stLen s.mem st + StackNat.rnd vl
  hcap : M.readLE (st + 16) 8 = c1
  vs : ∀ a n, vp ≤ a → a + n ≤ vp + 8 * vl → M.readLE a n = s.mem.readLE a n
  fr : MemFrame s.mem M (R.rt ++ winA s 41264 112 ++ wsL zp zc up uc vl t ++ stkWs s.mem st)
  lf : LiveFrame s.mem M L (wsL zp zc up uc vl t ++ stkWs s.mem st)
  inv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk M)

/-- `Env` from `stk.nat`'s post (pure) -/
theorem env_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat} {s : State}
    (hpre : Pre R b L c zp zc st up uc ip il vp vl s) {S2 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hext : LiveExt R L L1) (hbud : b - stackNatCost (stLen s.mem st) vl ≤ b1) (hok : StkOK S2 R L1 st)
    (hlen : stLen S2 st = stLen s.mem st + StackNat.rnd vl)
    (hsame : stLen s.mem st + StackNat.rnd vl ≤ stCap s.mem st → stW S2 st = stW s.mem st ∧ stCap S2 st = stCap s.mem st)
    (hgrow : stCap s.mem st < stLen s.mem st + StackNat.rnd vl → InRanges (stW S2 st) (8 * stCap S2 st) R.rt ∧
      ApartAll (stW S2 st) (8 * stCap S2 st) L)
    (hacc2 : ∀ a n v, S2.accessible a n v = s.mem.accessible a n v) :
    Env R b L c zp zc st up uc ip il vp vl s (stW S2 st + 8 * stLen s.mem st) L1 b1 (stW S2 st) (stCap S2 st) := by
  have hv2 := hpre.v2
  have hscr := Scr.of_post (m0 := s.mem) (k := vl) hok hlen (by omega) hsame hgrow rfl
  have hok' := hok
  obtain ⟨-, -, -, -, hnl, hlc, hcb⟩ := hok'
  refine ⟨hpre, rfl, ⟨hscr.b48, ?_, hscr.al, hscr.held, hscr.loc⟩, hext, hbud, ?_, ?_, hcb, ?_⟩
  · rw [← hacc2]; exact hscr.acc
  · by_cases hc : stLen s.mem st + StackNat.rnd vl ≤ stCap s.mem st
    · left; exact hsame hc
    · right; exact hgrow (by omega)
  · rw [← hlen]; exact hlc
  · intro h0
    obtain ⟨a1, a2, a3, a4⟩ := hnl h0
    exact ⟨a1, a2, by rw [← hacc2]; exact a3, a4⟩

end FvModexp.Arm64.DivLarge
