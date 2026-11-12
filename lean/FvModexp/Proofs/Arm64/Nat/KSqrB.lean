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

end FvModexp.Arm64.NatSqr
