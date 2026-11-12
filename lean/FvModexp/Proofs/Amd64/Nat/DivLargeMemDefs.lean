import FvModexp.Proofs.Amd64.Nat.DivLargeRel

set_option autoImplicit false

/-!
# `divLarge` (amd64): the memory relation after `v := stk.nat(n)` and the join after `u.make(len uIn + 1)`

The twin of the second half of `Arm64/Nat/DivLargeRel.lean` (`Mem`, `UArr`, `AtU`), with the amd64 frame slots
(offsets from the entry `RSP`, see `DivLargeDefs`): `v` ptr/len/cap at `-96, -160, -152` (stored right after the call),
`u` ptr/len/cap at `-104, -200, -184` (stored at `joinU`), the stack args `uIn`, `vIn` at `+8 … +48`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.DivLarge

/-- the ranges written after the `stk.nat` call: the scratch `v`, `z`'s and `u`'s arrays -/
@[reducible] def wsL (zp zc up uc vl t : Nat) : List (Nat × Nat) :=
  (t, t + 8 * vl) :: (ar zp zc ++ ar up uc)

/-- the memory facts at every point after the `stk.nat` call (memory `M`, live set `Lk`, budget `bk`) -/
structure Mem (R : RtInv) (L : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) : Prop where
  ra : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  dbit : M.readLE ((s.regs 4).toNat - 209) 1 = 1
  vtop : M.readLE ((s.regs 4).toNat - 168) 8 = s.mem.readLE (vp + 8 * (vl - 1)) 8
  il1 : M.readLE ((s.regs 4).toNat - 136) 8 = il + 1
  mm : M.readLE ((s.regs 4).toNat - 128) 8 = il - vl
  vt : M.readLE ((s.regs 4).toNat - 96) 8 = t
  vn1 : M.readLE ((s.regs 4).toNat - 160) 8 = vl
  vn2 : M.readLE ((s.regs 4).toNat - 152) 8 = vl
  dfn : M.readLE ((s.regs 4).toNat - 40) 8 = dfnL
  dst : M.readLE ((s.regs 4).toNat - 32) 8 = st
  dn : M.readLE ((s.regs 4).toNat - 24) 8 = stLen s.mem st
  dp : M.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 40
  ipS : M.readLE ((s.regs 4).toNat + 8) 8 = ip
  ilS : M.readLE ((s.regs 4).toNat + 16) 8 = il
  vpS : M.readLE ((s.regs 4).toNat + 32) 8 = vp
  vlS : M.readLE ((s.regs 4).toNat + 40) 8 = vl
  s1 : M.readLE ((s.regs 4).toNat + 56) 8 = zp
  s3 : M.readLE ((s.regs 4).toNat + 72) 8 = zc
  s4 : M.readLE ((s.regs 4).toNat + 80) 8 = st
  s5 : M.readLE ((s.regs 4).toNat + 88) 8 = up
  s7 : M.readLE ((s.regs 4).toNat + 104) 8 = uc
  hw : M.readLE st 8 = w1
  hlen : M.readLE (st + 8) 8 = stLen s.mem st + StackNat.rnd vl
  hcap : M.readLE (st + 16) 8 = c1
  tls : M.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat
  vs : ∀ a n, vp ≤ a → a + n ≤ vp + 8 * vl → M.readLE a n = s.mem.readLE a n
  fr : MemFrame s.mem M (R.rt ++ win s 41272 112 ++ wsL zp zc up uc vl t ++ stkWs s.mem st)
  lf : LiveFrame s.mem M L (wsL zp zc up uc vl t ++ stkWs s.mem st)
  inv : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk M)

/-- the remainder's array `u = u.make(len uIn + 1)` = `(P, C)` (live set `Lk`, memory `M`) -/
structure UArr (R : RtInv) (zp zc st up uc ip il vp vl : Nat) (s : State) (t w1 c1 : Nat)
    (L1 Lk : List (Nat × Nat)) (P C : Nat) (M : Memory) : Prop where
  cap : il + 1 ≤ C
  c40 : C < 2 ^ 40
  p8 : P % 8 = 0
  p48 : P + 8 * C ≤ 2 ^ 48
  pacc : M.accessible P (8 * C) true = true
  pw : P + 8 * C ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ P
  pg : Apart P (8 * C) ((s.regs 14).toNat + 16) 8
  pt : Apart P (8 * C) (s.fsBase.toNat - 8) 8
  pheld : Held R Lk P (8 * C)
  ror : (P = up ∧ C = uc) ∨ (uc < il + 1 ∧ InRanges P (8 * C) R.rt ∧ ApartAll P (8 * C) L1)
  pi : P = ip ∨ Apart P (8 * C) ip (8 * il)
  pv : Apart P (8 * C) vp (8 * vl)
  pvt : Apart P (8 * C) t (8 * vl)
  ps : Apart P (8 * C) st 24
  pz : 0 < zc → Apart P (8 * C) zp (8 * zc)
  pf : Apart P (8 * C) (w1 + 8 * (stLen s.mem st + StackNat.rnd vl)) (8 * (c1 - (stLen s.mem st + StackNat.rnd vl)))

/-- the join after `u = u.make(len uIn + 1)` (`fn + 0x216`, `MOVQ SI, 0x78(SP)`) -/
abbrev joinU : Nat := segAddr Extracted.program fn + 0x216

/-- the state at `joinU` (`RSI = cap u`, `RDI = len u`, `R8 = u.ptr`, `RAX, RBX, RCX = v`, `RDX = bsr vIn[n-1]`) -/
structure AtU (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat) (S : State) : Prop where
  pc : S.rip = BitVec.ofNat 64 joinU
  sp : S.regs 4 = s.regs 4 - 304#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  x15 : S.xmm 15 = 0#128
  df : S.df = false
  r0 : S.regs 0 = BitVec.ofNat 64 t
  r3 : S.regs 3 = BitVec.ofNat 64 vl
  r1 : S.regs 1 = BitVec.ofNat 64 vl
  r2 : S.regs 2 = BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8))
  r6 : S.regs 6 = BitVec.ofNat 64 C
  r7 : S.regs 7 = BitVec.ofNat 64 (il + 1)
  r8 : S.regs 8 = BitVec.ofNat 64 P
  mem : Mem R L zp zc st up uc ip il vp vl s t w1 c1 Lk bk S.mem
  ua : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lk P C S.mem
  ext2 : LiveExt R L1 Lk
  bud2 : b1 - makeCost (il + 1) ≤ bk
  is : ∀ a n, ip ≤ a → a + n ≤ ip + 8 * il → S.mem.readLE a n = s.mem.readLE a n
  reg : S.mem.regions = s.mem.regions

end FvModexp.Amd64.DivLarge
