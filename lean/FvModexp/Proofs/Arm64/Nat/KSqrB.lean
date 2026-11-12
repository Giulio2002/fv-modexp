import FvModexp.Proofs.Arm64.Nat.KSqrCall

/-!
# `karatsubaSqr` (arm64): the segment boundaries

Every segment lemma of `karatsubaSqr` starts at one boundary `KBi … S` (state `S` at a fixed `pc`, `KM` at `S.mem`,
plus the stage facts: the `*Int` headers of the frame and the contents of `z` / the scratch `t`) and takes the next
boundary as a continuation (`∀ S', KBj … S' → KGoal … S'`). All segment modules import this one only (ROW-TIME
LESSON); `KStep` composes them.

Boundaries (`X0 = kX0`, `X1 = kX1` the halves of `x`, `E = 2^(64·n2)`):
* `KB1` `0x1bc428` (after `z1 := stk.nat(2·n2 + 1)`): `R0..R2 = t, kT, kT`, `z0`/`z2` headers as built by the prologue;
* `KB2` `0x1bc470` (after `tx.Sub(x0, x1)`): `tx = (·, zp, ltx, zc)` holds `|X0 - X1|`;
* `KB3` `0x1bc4ac` (after `z1.abs.sqr`, `z1.neg = true`, `clear(z)`): `z1 = -(X0-X1)²` in `t`, `z[0:2n] = 0`;
* `KB4` `0x1bc4d0` (after `z0.abs.sqr`): `z0 = X0²` in `z[0:2·n2]`, `z[2n2:2n] = 0`;
* `KB5` `0x1bc4f4` (after `z2.abs.sqr`): `z2 = X1²` in `z[2n2:2n]`;
* `KB7` `0x1bc514` (after both `z1.Add`): `z1 = 2·X0·X1` (sign clear) in `t`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- `z0`'s header (frame `SP - 112`) as built by the prologue: `z[0:2·n2]` -/
@[reducible] def Z0H (s : State) (M : Memory) (zp zc n : Nat) : Prop :=
  IntAt M (s.sp.toNat - 112) 0 zp (2 * kn2 n) zc
/-- `z2`'s header (frame `SP - 144`) as built by the prologue: `z[2·n2:]` -/
@[reducible] def Z2H (s : State) (M : Memory) (zp zc n : Nat) : Prop :=
  IntAt M (s.sp.toNat - 144) 0 (zp + 16 * kn2 n) (2 * n - 2 * kn2 n) (zc - 2 * kn2 n)

/-- `|X0 - X1|` -/
@[reducible] def kD (s : State) (xp n : Nat) : Nat := ((kX0 s xp n : Int) - (kX1 s xp n : Int)).natAbs

structure KB1 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State)
    (lx0 lx1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk : Nat) : Prop where
  pos : KAt s S 0x1bc428
  km : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc1 (stLen s.mem st) n) S.mem
  r0 : S.regs 0 = BitVec.ofNat 64 t
  r1 : S.regs 1 = BitVec.ofNat 64 (kT n)
  r2 : S.regs 2 = BitVec.ofNat 64 (kT n)
  z0h : Z0H s S.mem zp zc n
  z2h : Z2H s S.mem zp zc n

structure KB2 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State)
    (lx0 lx1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk tng ltx : Nat) : Prop where
  pos : KAt s S 0x1bc470
  km : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc2 (stLen s.mem st) n) S.mem
  z1h : IntAt S.mem (s.sp.toNat - 200) 0 t (kT n) (kT n)
  z0h : Z0H s S.mem zp zc n
  z2h : Z2H s S.mem zp zc n
  txh : IntAt S.mem (s.sp.toNat - 232) tng zp ltx zc
  htng : tng ≤ 1
  hltx : ltx ≤ kn2 n
  tv : natVal S.mem zp ltx = kD s xp n
  tnn : NatNorm S.mem zp ltx

structure KB3 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State)
    (lx0 lx1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk l1 : Nat) : Prop where
  pos : KAt s S 0x1bc4ac
  km : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc3 (stLen s.mem st) n) S.mem
  z1h : IntAt S.mem (s.sp.toNat - 200) 1 t l1 (kT n)
  hl1 : l1 ≤ 2 * kn2 n
  z1v : natVal S.mem t l1 = kD s xp n * kD s xp n
  z1n : NatNorm S.mem t l1
  z0h : Z0H s S.mem zp zc n
  z2h : Z2H s S.mem zp zc n
  zz : natVal S.mem zp (2 * n) = 0

structure KB4 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State)
    (lx0 lx1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk l1 l0 : Nat) : Prop where
  pos : KAt s S 0x1bc4d0
  km : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc4 (stLen s.mem st) n) S.mem
  z1h : IntAt S.mem (s.sp.toNat - 200) 1 t l1 (kT n)
  hl1 : l1 ≤ 2 * kn2 n
  z1v : natVal S.mem t l1 = kD s xp n * kD s xp n
  z1n : NatNorm S.mem t l1
  z0h : IntAt S.mem (s.sp.toNat - 112) 0 zp l0 zc
  hl0 : l0 ≤ 2 * kn2 n
  z0v : natVal S.mem zp l0 = kX0 s xp n * kX0 s xp n
  z0n : NatNorm S.mem zp l0
  z2h : Z2H s S.mem zp zc n
  zlo : natVal S.mem zp (2 * kn2 n) = kX0 s xp n * kX0 s xp n
  zhi : natVal S.mem (zp + 16 * kn2 n) (2 * n - 2 * kn2 n) = 0

structure KB5 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State)
    (lx0 lx1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk l1 l0 l2 : Nat) : Prop where
  pos : KAt s S 0x1bc4f4
  km : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc5 (stLen s.mem st) n) S.mem
  z1h : IntAt S.mem (s.sp.toNat - 200) 1 t l1 (kT n)
  hl1 : l1 ≤ 2 * kn2 n
  z1v : natVal S.mem t l1 = kD s xp n * kD s xp n
  z1n : NatNorm S.mem t l1
  z0h : IntAt S.mem (s.sp.toNat - 112) 0 zp l0 zc
  hl0 : l0 ≤ 2 * kn2 n
  z0v : natVal S.mem zp l0 = kX0 s xp n * kX0 s xp n
  z0n : NatNorm S.mem zp l0
  z2h : IntAt S.mem (s.sp.toNat - 144) 0 (zp + 16 * kn2 n) l2 (zc - 2 * kn2 n)
  hl2 : l2 ≤ 2 * (n - kn2 n)
  z2v : natVal S.mem (zp + 16 * kn2 n) l2 = kX1 s xp n * kX1 s xp n
  z2n : NatNorm S.mem (zp + 16 * kn2 n) l2
  zlo : natVal S.mem zp (2 * kn2 n) = kX0 s xp n * kX0 s xp n
  zhi : natVal S.mem (zp + 16 * kn2 n) (2 * n - 2 * kn2 n) = kX1 s xp n * kX1 s xp n

structure KB7 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State)
    (lx0 lx1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk l : Nat) : Prop where
  pos : KAt s S 0x1bc514
  km : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc7 (stLen s.mem st) n) S.mem
  z1h : IntAt S.mem (s.sp.toNat - 200) 0 t l (kT n)
  hl : l ≤ kT n
  z1v : natVal S.mem t l = 2 * kX0 s xp n * kX1 s xp n
  zlo : natVal S.mem zp (2 * kn2 n) = kX0 s xp n * kX0 s xp n
  zhi : natVal S.mem (zp + 16 * kn2 n) (2 * n - 2 * kn2 n) = kX1 s xp n * kX1 s xp n

/-! ## Helpers shared by the segments -/

/-- a read in our frame above a callee's window (`SP - 256 ≤ x`, below `SP + 48`) and outside the callee's writes
keeps its bytes -/
theorem KM.rdW {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) {M' : Memory} {k a : Nat}
    (hk : 320 + k ≤ W) (ha : a ≤ 64) {ws : List (Nat × Nat)}
    (hF : MemFrame M M' (R.rt ++ [(s.sp.toNat - 320 - k, s.sp.toNat - 320 - 8), (s.sp.toNat - 320 + 8,
      s.sp.toNat - 320 + a)] ++ ws)) {x m : Nat} (h1 : s.sp.toNat - 256 ≤ x) (h2 : x + m ≤ s.sp.toNat + 48)
    (hws : Outside x m ws) : M'.readLE x m = M.readLE x m := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, hout, -, -⟩ := h.lay
  refine hF.readLE _ _ ?_
  simp only [outside_append, outside_cons, outside_nil, and_true]
  exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, hws⟩

theorem IntAt.keep {M M' : Memory} {a ng p l c : Nat} (h : IntAt M a ng p l c)
    (hk : ∀ x m, a ≤ x → x + m ≤ a + 32 → M'.readLE x m = M.readLE x m) : IntAt M' a ng p l c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨(hk _ _ (by omega) (by omega)).trans h1, (hk _ _ (by omega) (by omega)).trans h2,
    (hk _ _ (by omega) (by omega)).trans h3, (hk _ _ (by omega) (by omega)).trans h4⟩

/-- the scratch `t`: live, outside the window, apart from the guard word, from `z` and from `x` -/
theorem KM.tops {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    NatLive M R Lk t (kT n) ∧ Outside t (8 * kT n) (win s W 48) ∧ Apart t (8 * kT n) (guard s) 8 ∧
      Apart t (8 * kT n) zp (8 * zc) ∧ Apart t (8 * kT n) xp (8 * n) ∧ t + 8 * kT n ≤ 2 ^ 48 := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, hout, hgr, hga⟩ := h.lay
  have hsp : StkPre R L s W 48 st := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzlive : NatLive s.mem R L zp zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzs : StkSep s.mem st zp (8 * zc) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxh : Held R L xp (8 * xc) := h.pre.2.2.2.2.2.2.2.2.2.2.1
  have hxc : n ≤ xc := h.pre.2.2.2.2.2.2.1
  have hzl : 2 * n ≤ zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h80 := h.lay.2.2.2.2.1
  obtain ⟨-, -, -, -, -, hfg, hfw, -⟩ := hsp
  obtain ⟨-, hzh, -, -⟩ := hzlive (by omega)
  have hsc := h.scr
  have hlive : NatLive M R Lk t (kT n) := fun _ =>
    ⟨hsc.al, hsc.held, by rw [h.fr.accessible]; exact hsc.acc, hsc.b48⟩
  have hzt : Apart t (8 * kT n) zp (8 * zc) := hsc.apart hzh (fun _ => by
    have := hzs.2.1; simp only [BasicSqr.freeP, BasicSqr.freeN] at this; exact this)
  simp only [BasicSqr.freeP, BasicSqr.freeN, guard] at hfg hfw
  simp only [win, outside_cons, outside_nil, and_true] at hfw ⊢
  rcases hsc.loc with ⟨-, h1, h2⟩ | ⟨hin, hap⟩
  · -- `t` in the entry stack's free part
    have hxs : StkSep s.mem st xp (8 * n) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hx2 := hxs.2.1; simp only [BasicSqr.freeP, BasicSqr.freeN] at hx2
    refine ⟨hlive, by omega, by simp only [guard]; unfold Apart at hfg ⊢; omega, hzt, by unfold Apart at hx2 ⊢; omega, hsc.b48⟩
  · have ho := NatSub.outside_of_inRanges hout hin
    have hg := NatSub.outside_of_inRanges hgr hin
    exact ⟨hlive, by omega, by simp only [guard]; unfold Apart; omega, hzt, apart_of_held (hxh.sub (by omega) (by omega)) hin hap, hsc.b48⟩

/-! ## Calls out of `karatsubaSqr` -/

set_option maxRecDepth 20000 in
/-- a return address inside `karatsubaSqr` (segment `seg56`, base `0x1bc2b0`, 204 words) -/
theorem ks_ra {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fnK = false) (i : Nat) (hi : i < 204) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (0x1bc2b0 + 4 * i) := by
  have := IntAS.retAddr_restrict hap (cs := Extracted.seg56)
    (show Extracted.seg56 ∈ Extracted.program.segments from
      List.getElem_mem (l := Extracted.program.segments) (n := 56) (by decide))
    (show ns.contains Extracted.seg56.name = false from hn) i
    (by simp [Extracted.seg56]; omega) (by simp [Extracted.seg56]; omega) (by decide)
  simpa [Extracted.seg56] using this

/-- `(*Int).Add` / `(*Int).Sub` (`IntAS.ens`) as a summary in `LibSqr.program` -/
theorem ksIntSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : BitVec 64) :
    Summary (LibSqr.program.link impl) (IntAS.entry sub)
      (fun s => RetAddr ((Extracted.program.onlySegments IntAS.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [z, x, y] ∧ IntAS.Pre R b L z.toNat x.toNat y.toNat s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        IntAS.Post sub R b L z.toNat x.toNat y.toNat s s') := by
  have hS := Ensures.toSummaryIn (IntAS.ens impl hap R hmk hmv hwb sub b L z x y)
    (noExit_restrict hap IntAS.names) (codeIn_restrict_mono hap (IntAS.sub_of_all (ms := LibSqr.names) (by decide)))
  rw [← LibSqr.eq_only, IntAS.entry_eq] at hS
  exact hS

/-- **A `(*Int).Add/Sub(z, x, y)` call from `karatsubaSqr`'s frame** (at the callee entry, return address inside
`karatsubaSqr`): `KM.intPre` discharges the callee's precondition; the continuation gets its postcondition. -/
theorem ks_intcall (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) (sub : Bool)
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 (IntAS.entry sub)) (hsp : S1.sp.toNat = s.sp.toNat - 320)
    (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = M) {i : Nat} (hi : i < 204)
    (hra : S1.regs 30 = BitVec.ofNat 64 (0x1bc2b0 + 4 * i))
    {z x y : Nat} (r0 : S1.regs 0 = BitVec.ofNat 64 z) (r1 : S1.regs 1 = BitVec.ofNat 64 x)
    (r2 : S1.regs 2 = BitVec.ofNat 64 y)
    (hz1 : s.sp.toNat - 232 ≤ z) (hz2 : z + 32 ≤ s.sp.toNat - 16)
    (hx1 : s.sp.toNat - 232 ≤ x) (hx2 : x + 32 ≤ s.sp.toNat - 16)
    (hy1 : s.sp.toNat - 232 ≤ y) (hy2 : y + 32 ≤ s.sp.toNat - 16)
    (hzx : z = x ∨ Apart z 32 x 32) (hzy : Apart z 32 y 32)
    (hox : IOp R Lk s W M x) (hoy : IOp R Lk s W M y)
    (hzc : IntAS.hC M z < 2 ^ 40) (hzl : NatLive M R Lk (IntAS.hP M z) (IntAS.hC M z))
    (hzw : Outside (IntAS.hP M z) (8 * IntAS.hC M z) (win s W 48))
    (hza : 0 < IntAS.hC M z → Apart (IntAS.hP M z) (8 * IntAS.hC M z) (guard s) 8 ∧
      (IntAS.hP M z = IntAS.hP M x ∨ Apart (IntAS.hP M z) (8 * IntAS.hC M z) (IntAS.hP M x) (8 * IntAS.hL M x)) ∧
      (IntAS.hP M z = IntAS.hP M y ∨ Apart (IntAS.hP M z) (8 * IntAS.hC M z) (IntAS.hP M y) (8 * IntAS.hL M y)))
    (hcost : IntAS.asCost (IntAS.hL M x) (IntAS.hL M y) ≤ bk)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ s2 : State, s2.pc = S1.regs 30 → s2.mem.regions = M.regions →
      (s2.sp = S1.sp ∧ s2.regs 28 = S1.regs 28 ∧ s2.regs 29 = S1.regs 29 ∧ s2.regs 18 = S1.regs 18) →
      IntAS.Post sub R bk Lk z x y S1 s2 → ReachesRet (LibSqr.program.link impl) ret s2 Q) :
    ReachesRet (LibSqr.program.link impl) ret S1 Q := by
  have hb := h.lay
  have hz64 : z < 2 ^ 64 := by omega
  have hx64 : x < 2 ^ 64 := by omega
  have hy64 : y < 2 ^ 64 := by omega
  have hP := h.intPre hsp hg hm hz1 hz2 hx1 hx2 hy1 hy2 hzx hzy hox hoy hzc hzl hzw hza hcost
  refine ReachesRet.call_regions (ksIntSum impl hap R hmk hmv hwb sub bk Lk (BitVec.ofNat 64 z)
    (BitVec.ofNat 64 x) (BitVec.ofNat 64 y)) hpc ⟨?_, ⟨r0, r1, r2, trivial⟩, ?_⟩ fun s2 hr hq hreg => ?_
  · rw [hra, tN' (by omega)]; exact ks_ra hap (by decide) i hi
  · rw [tN' hz64, tN' hx64, tN' hy64]; exact hP
  · obtain ⟨hk, hq⟩ := hq
    rw [tN' hz64, tN' hx64, tN' hy64] at hq
    exact hK s2 hr (by rw [hreg, hm]) hk hq

/-- **After an `(*Int).Add/Sub` call** (header `z` in the `tx`/`z1` or `z2`/`z0` area, array writes inside `z[0:2n]` or
`t`): `KM` holds again -/
theorem KM.intStep {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) {M' : Memory} {S1 : State}
    (hsp : S1.sp.toNat = s.sp.toNat - 320) {z q w : Nat}
    (hz : (s.sp.toNat - 232 ≤ z ∧ z + 32 ≤ s.sp.toNat - 168) ∨ (s.sp.toNat - 144 ≤ z ∧ z + 32 ≤ s.sp.toNat - 80))
    (hq : (zp ≤ q ∧ q + 8 * w ≤ zp + 8 * (2 * n)) ∨ (t ≤ q ∧ q + 8 * w ≤ t + 8 * kT n))
    (hF : MemFrame M M' (R.rt ++ winA S1 4560 32 ++ [(z, z + 32), (q, q + 8 * w)]))
    (hLF : LiveFrame M M' Lk [(z, z + 32), (q, q + 8 * w)]) (hreg : M'.regions = M.regions)
    {Lk' : List (Nat × Nat)} {bk' c : Nat} (hext : LiveExt R Lk Lk') (hb : bk - c ≤ bk')
    (hinv : R.inv bk' Lk' (s.regs 28).toNat (view R.rt Lk' M')) :
    KM R b L W st zp zc xp n xc s lx0 lx1 t Lk' bk' (spent + c) M' := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, hout, -, -⟩ := h.lay
  have hstw : Outside st 24 (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hzs : StkSep s.mem st zp (8 * zc) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzl : 2 * n ≤ zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hts := h.tsep.1
  have hzs1 := hzs.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  unfold Apart at hts hzs1
  simp only [winA, hsp] at hF
  have hF' : MemFrame M M' (R.rt ++ ([(s.sp.toNat - 320 - 4560, s.sp.toNat - 320 - 8),
      (s.sp.toNat - 320 + 8, s.sp.toNat - 320 + 32)] ++ [(z, z + 32), (q, q + 8 * w)])) := by
    rw [← List.append_assoc]; exact hF
  have hsb : StackBack R Lk Lk' st M M' := by
    refine stackBack_keep' h.sok hF' (FvModexp.LiveFrame.mono_ws hLF fun a k ho => by rw [outside_append] at ho; exact ho.2) ?_ hext
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  refine h.step (k := 4560) (a := 32) (by omega) (by omega) (fun r hr => ?_) hF hLF hreg hext hb hinv hsb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hz with hz | hz
    · exact ⟨by simp only; omega, Or.inr (Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩))⟩
    · exact ⟨by simp only; omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩)))⟩
  · rcases hq with hq | hq
    · exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩
    · exact ⟨by simp only; omega, Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩)⟩

/-- **After an inner `nat.sqr` that reused its result array** (writes `[q, q + 8w)` inside `z[0:2n]` or `t`, the
stack's header and free part): `KM` holds again -/
theorem KM.sqStep {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) {M' : Memory} {S1 : State}
    (hsp : S1.sp.toNat = s.sp.toNat - 320) {q w : Nat}
    (hq : (zp ≤ q ∧ q + 8 * w ≤ zp + 8 * (2 * n)) ∨ (t ≤ q ∧ q + 8 * w ≤ t + 8 * kT n))
    (hF : MemFrame M M' (R.rt ++ winA S1 (W - 320) 64 ++ [(q, q + 8 * w)] ++ stkWs M st))
    (hLF : LiveFrame M M' Lk ([(q, q + 8 * w)] ++ stkWs M st)) (hreg : M'.regions = M.regions)
    {Lk' : List (Nat × Nat)} {bk' c : Nat} (hext : LiveExt R Lk Lk') (hb : bk - c ≤ bk')
    (hinv : R.inv bk' Lk' (s.regs 28).toNat (view R.rt Lk' M')) (hsb : StackBack R Lk Lk' st M M') :
    KM R b L W st zp zc xp n xc s lx0 lx1 t Lk' bk' (spent + c) M' := by
  obtain ⟨hW, -⟩ := h.lay
  have hlc := h.sok.2.2.2.2.2.1
  simp only [winA, hsp] at hF
  rw [List.append_assoc] at hF
  refine h.step (k := W - 320) (a := 64) (by omega) (by omega) (fun r hr => ?_) hF hLF hreg hext hb hinv hsb
  simp only [stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases hq with hq | hq
    · exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩
    · exact ⟨by simp only; omega, Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩)⟩
  · exact ⟨by simp only; omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩))))⟩
  · exact ⟨by simp only; omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Nat.le_refl _, Nat.le_refl _⟩))))⟩

/-- the operand facts of `x0 = x[:len x0]` -/
theorem KM.x0ops {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    lx0 ≤ xc ∧ xc < 2 ^ 40 ∧ M.accessible xp (8 * lx0) false = true ∧
      (0 < xc → Held R Lk xp (8 * xc) ∧ xp + 8 * xc ≤ 2 ^ 48) ∧ (0 < lx0 → Outside xp (8 * lx0) (win s W 48)) ∧
      (0 < lx0 → StkSep M st xp (8 * lx0)) ∧ Apart zp (8 * zc) xp (8 * lx0) := by
  have hxc : n ≤ xc := h.pre.2.2.2.2.2.2.1
  have hxc40 : xc < 2 ^ 40 := h.pre.2.2.2.2.2.2.2.1
  have hxacc : s.mem.accessible xp (8 * n) false = true := h.pre.2.2.2.2.2.2.2.2.2.1
  have hxh : Held R L xp (8 * xc) := h.pre.2.2.2.2.2.2.2.2.2.2.1
  have hx48 : xp + 8 * xc ≤ 2 ^ 48 := h.pre.2.2.2.2.2.2.2.2.2.2.2.1
  have hxw : Outside xp (8 * n) (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzx : Apart zp (8 * zc) xp (8 * n) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxs : StkSep s.mem st xp (8 * n) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hl0 := h.l0
  simp only [kn2] at hl0
  have hacc : M.accessible xp (8 * lx0) false = true := by
    rw [h.fr.accessible]; exact Memory.accessible_sub _ hxacc (Or.inl rfl) (by omega) (by omega)
  refine ⟨by omega, hxc40, hacc, fun _ => ⟨h.ext.held hxh, hx48⟩, fun _ => hxw.of_sub (by omega) (by omega),
    fun _ => h.sepOf (hxs.sub (by omega)) (hxh.sub (by omega) (by omega)), by unfold Apart at hzx ⊢; omega⟩

/-- `z`'s array facts at `M` -/
theorem KM.zops {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    zc < 2 ^ 40 ∧ NatLive M R Lk zp zc ∧ Outside zp (8 * zc) (win s W 48) ∧
      Apart zp (8 * zc) (guard s) 8 ∧ StkSep M st zp (8 * zc) ∧ zp + 8 * zc ≠ xp + 8 * xc ∧ 2 * n ≤ zc ∧
      zp % 8 = 0 ∧ Held R Lk zp (8 * zc) ∧ zp + 8 * zc ≤ 2 ^ 48 := by
  have hzl : 2 * n ≤ zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzc40 : zc < 2 ^ 40 := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzlive : NatLive s.mem R L zp zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzw : Outside zp (8 * zc) (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzg : Apart zp (8 * zc) (guard s) 8 := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzs : StkSep s.mem st zp (8 * zc) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hne : zp + 8 * zc ≠ xp + 8 * xc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h80 := h.lay.2.2.2.2.1
  obtain ⟨hal, hh, hacc, h48⟩ := hzlive (by omega)
  exact ⟨hzc40, fun _ => ⟨hal, h.ext.held hh, by rw [h.fr.accessible]; exact hacc, h48⟩, hzw, hzg,
    h.sepOf hzs hh, hne, hzl, hal, h.ext.held hh, h48⟩

/-! ## Small facts -/

theorem KM.weaken {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) {spent' : Nat} (hs : spent ≤ spent') :
    KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent' M :=
  { h with bud := by have := h.bud; omega }

theorem asCost_le_asB {a b k : Nat} (h1 : a ≤ k) (h2 : b ≤ k) : IntAS.asCost a b ≤ asB k := by
  have e1 := makeCost_le_makeB (if min a b = 0 then max a b else max a b + 1)
  have e2 := makeCost_le_makeB (max a b)
  unfold IntAS.asCost
  unfold makeB asB allocCost at *
  by_cases hm : min a b = 0
  · rw [if_pos hm] at e1 ⊢; omega
  · rw [if_neg hm] at e1 ⊢; omega

theorem natNorm_le {m : Memory} {p l k : Nat} (hn : NatNorm m p l) (hv : natVal m p l < 2 ^ (64 * k)) : l ≤ k := by
  rcases Nat.lt_or_ge k l with hc | hc
  · exfalso
    have h1 := SubMod2N.natVal_lower m p l hn (by omega)
    have h2 : 2 ^ (64 * k) ≤ 2 ^ (64 * (l - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · exact hc

theorem natAbs_of_signed {ng v : Nat} {d : Int} (h : (if ng = 0 then (v : Int) else -(v : Int)) = d) :
    v = d.natAbs := by
  by_cases hg : ng = 0
  · rw [if_pos hg] at h; subst h; simp
  · rw [if_neg hg] at h; subst h; simp

/-- `x0`'s header and value (frame `SP - 48`) -/
theorem KM.x0op {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    IOp R Lk s W M (s.sp.toNat - 48) ∧ IntAS.intZ M (s.sp.toNat - 48) = (kX0 s xp n : Int) ∧
      IntAS.hP M (s.sp.toNat - 48) = xp ∧ IntAS.hL M (s.sp.toNat - 48) = lx0 := by
  obtain ⟨q1, q2, q3, q4⟩ := h.x0h
  obtain ⟨hl0, hxc40, hacc, hxh, hxw, -, -⟩ := h.x0ops
  have h80 := h.lay.2.2.2.2.1
  have hl := h.l0; simp only [kn2] at hl
  have hxc : n ≤ xc := h.pre.2.2.2.2.2.2.1
  have hxs : Held R Lk xp (8 * xc) ∧ xp + 8 * xc ≤ 2 ^ 48 := hxh (by omega)
  have hv : natVal M xp lx0 = natVal s.mem xp lx0 := by
    unfold natVal; exact h.xrd (Nat.le_refl _) (by omega)
  have hnn : NatNorm M xp lx0 := by
    rcases h.nn0 with h0 | h0
    · exact Or.inl h0
    · right; rwa [h.xrd (by omega) (by omega)]
  have hn12 := h.lay.2.2.2.2.2.1
  refine ⟨?_, ?_, q2, q3⟩
  · simp only [IOp, IntAS.hNeg, IntAS.hP, IntAS.hL, IntAS.hC, q1, q2, q3, q4]
    refine ⟨by omega, by omega, hxc40, by omega, hacc, by omega, hxs.1.sub (by omega) (by omega), hnn, ?_⟩
    have hxw' : Outside xp (8 * n) (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact hxw'.of_sub (by omega) (by omega)
  · simp only [IntAS.intZ, IntAS.hNeg, IntAS.hP, IntAS.hL, q1, q2, q3, if_true, hv, h.v0]

/-- `x1`'s header and value (frame `SP - 80`) -/
theorem KM.x1op {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    IOp R Lk s W M (s.sp.toNat - 80) ∧ IntAS.intZ M (s.sp.toNat - 80) = (kX1 s xp n : Int) ∧
      IntAS.hP M (s.sp.toNat - 80) = xp + 8 * kn2 n ∧ IntAS.hL M (s.sp.toNat - 80) = lx1 := by
  obtain ⟨q1, q2, q3, q4⟩ := h.x1h
  have h80 := h.lay.2.2.2.2.1
  have hn12 := h.lay.2.2.2.2.2.1
  have hl := h.l1; simp only [kn2] at hl
  have hxc : n ≤ xc := h.pre.2.2.2.2.2.2.1
  have hxc40 : xc < 2 ^ 40 := h.pre.2.2.2.2.2.2.2.1
  have hxacc : s.mem.accessible xp (8 * n) false = true := h.pre.2.2.2.2.2.2.2.2.2.1
  have hxh : Held R L xp (8 * xc) := h.pre.2.2.2.2.2.2.2.2.2.2.1
  have hx48 : xp + 8 * xc ≤ 2 ^ 48 := h.pre.2.2.2.2.2.2.2.2.2.2.2.1
  have hxw : Outside xp (8 * n) (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv : natVal M (xp + 8 * kn2 n) lx1 = natVal s.mem (xp + 8 * kn2 n) lx1 := by
    unfold natVal; exact h.xrd (by omega) (by simp only [kn2]; omega)
  have hnn : NatNorm M (xp + 8 * kn2 n) lx1 := by
    rcases h.nn1 with h0 | h0
    · exact Or.inl h0
    · right; rwa [h.xrd (by omega) (by simp only [kn2]; omega)]
  refine ⟨?_, ?_, q2, q3⟩
  · simp only [IOp, IntAS.hNeg, IntAS.hP, IntAS.hL, IntAS.hC, q1, q2, q3, q4]
    refine ⟨by omega, by simp only [kn2]; omega, by omega, by omega, ?_, by simp only [kn2]; omega,
      (h.ext.held hxh).sub (by omega) (by simp only [kn2]; omega), hnn,
      hxw.of_sub (by omega) (by simp only [kn2]; omega)⟩
    rw [h.fr.accessible]; exact Memory.accessible_sub _ hxacc (Or.inl rfl) (by omega) (by simp only [kn2]; omega)
  · simp only [IntAS.intZ, IntAS.hNeg, IntAS.hP, IntAS.hL, q1, q2, q3, if_true, hv, h.v1]

/-- **An inner `nat.sqr` whose result array is reused** (`2·xl' ≤ zc'`, cap ends differ; the written part
`[zp', zp' + 16·xl')` inside `z[0:2n]` or `t`): the continuation gets `KM` (charged `kcS`), the result registers, the
value and the exact frames of the call. -/
theorem ks_sqcallR (impl : List Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) (ih : ∀ a, IH impl R (2 * n) (false, a))
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 0x1bb420) (hsp : S1.sp.toNat = s.sp.toNat - 320)
    (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = M)
    (hl4 : (S1.regs 30).toNat % 4 = 0) (hl48 : (S1.regs 30).toNat < 2 ^ 48)
    {zp' zl' zc' xp' xl' xc' : Nat} (b0 : zp' < 2 ^ 64) (b1 : zl' < 2 ^ 64) (b2 : zc' < 2 ^ 64) (b3 : st < 2 ^ 64)
    (b4 : xp' < 2 ^ 64) (b5 : xl' < 2 ^ 64) (b6 : xc' < 2 ^ 64)
    (r0 : S1.regs 0 = BitVec.ofNat 64 zp') (r1 : S1.regs 1 = BitVec.ofNat 64 zl')
    (r2 : S1.regs 2 = BitVec.ofNat 64 zc') (r3 : S1.regs 3 = BitVec.ofNat 64 st)
    (r4 : S1.regs 4 = BitVec.ofNat 64 xp') (r5 : S1.regs 5 = BitVec.ofNat 64 xl')
    (r6 : S1.regs 6 = BitVec.ofNat 64 xc')
    (hxl : xl' ≤ kn2 n) (hxc : xl' ≤ xc') (hxc40 : xc' < 2 ^ 40)
    (hxacc : M.accessible xp' (8 * xl') false = true)
    (hxh : 0 < xc' → Held R Lk xp' (8 * xc') ∧ xp' + 8 * xc' ≤ 2 ^ 48)
    (hxw : 0 < xl' → Outside xp' (8 * xl') (win s W 48))
    (hzc40 : zc' < 2 ^ 40) (hzl : NatLive M R Lk zp' zc') (hzw : Outside zp' (8 * zc') (win s W 48))
    (hzg : 0 < zc' → Apart zp' (8 * zc') (guard s) 8 ∧ StkSep M st zp' (8 * zc'))
    (hal : 0 < zc' → 0 < xl' → Apart zp' (8 * zc') xp' (8 * xl'))
    (hxs : 0 < xl' → StkSep M st xp' (8 * xl'))
    (hru : 2 * xl' ≤ zc') (hne : zp' + 8 * zc' ≠ xp' + 8 * xc')
    (hq : (zp ≤ zp' ∧ zp' + 8 * (2 * xl') ≤ zp + 8 * (2 * n)) ∨ (t ≤ zp' ∧ zp' + 8 * (2 * xl') ≤ t + 8 * kT n))
    (hsc : spent + kcS (stLen s.mem st) n ≤ ksqrC (stLen s.mem st) n)
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ (s2 : State) (Lk' : List (Nat × Nat)) (bk' l' : Nat), s2.pc = S1.regs 30 → s2.mem.regions = M.regions →
      Kept S1 s2 → KM R b L W st zp zc xp n xc s lx0 lx1 t Lk' bk' (spent + kcS (stLen s.mem st) n) s2.mem →
      s2.regs 0 = BitVec.ofNat 64 zp' → s2.regs 1 = BitVec.ofNat 64 l' → s2.regs 2 = BitVec.ofNat 64 zc' →
      natVal s2.mem zp' l' = natVal M xp' xl' * natVal M xp' xl' → NatNorm s2.mem zp' l' → l' ≤ 2 * xl' →
      natVal s2.mem zp' (2 * xl') = natVal M xp' xl' * natVal M xp' xl' →
      MemFrame M s2.mem (R.rt ++ winA S1 (W - 320) 64 ++ [(zp', zp' + 8 * (2 * xl'))] ++ stkWs M st) →
      LiveFrame M s2.mem Lk ([(zp', zp' + 8 * (2 * xl'))] ++ stkWs M st) →
      ReachesRet (LibSqr.program.link impl) ret s2 Q) :
    ReachesRet (LibSqr.program.link impl) ret S1 Q := by
  have hcost : sqrC (stLen M st) xl' ≤ bk := by
    refine Nat.le_trans ?_ (h.cost (c := kcS (stLen s.mem st) n) hsc)
    rw [h.slen]; exact sqrC_le_inner hxl
  refine ks_sqcall impl R h ih S1 hpc hsp hg hm hl4 hl48 b0 b1 b2 b3 b4 b5 b6 r0 r1 r2 r3 r4 r5 r6 hxl hxc hxc40
    hxacc hxh hxw hzc40 hzl hzw hzg (Or.inr hal) hxs hcost fun s2 hr hreg hk hP => ?_
  obtain ⟨p', l', c', e0, e1, e2, hval, hnn, -, hl2, -, L', b', hext, hbud, hinv, -, -, -, hreu, hsb, -, -⟩ := hP
  obtain ⟨ep, ec, hv2, hF, hLF⟩ := hreu hru hne
  subst ep ec
  rw [hm] at hval hv2 hF hLF hsb hbud
  rw [hg] at hinv
  have hkm := h.sqStep hsp hq hF hLF hreg hext (c := kcS (stLen s.mem st) n)
    (by have hle : sqrC (stLen M st) xl' ≤ kcS (stLen s.mem st) n := by rw [h.slen]; exact sqrC_le_inner hxl
        omega) hinv hsb
  exact hK s2 L' b' l' hr hreg hk hkm e0 e1 e2 hval hnn hl2 hv2 hF hLF

end FvModexp.Arm64.NatSqr
