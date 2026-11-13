import FvModexp.Proofs.Amd64.NatQ.KMulRel

set_option autoImplicit false

/-!
# [amd64 port (divmc s47) of the Q-form Arm64/NatQ/KMulB.lean — TIGHT COSTS] `karatsuba` (amd64): the segment boundaries and the calls out of the frame

Every segment lemma of `karatsuba` starts at one boundary `KMi … S` (state `S` at a fixed `pc`, `KN` at `S.mem`, plus
the stage facts: the `*Int` headers of the frame and the contents of `z` / the scratch `t`) and takes the next
boundary as a continuation (`∀ S', KMj … S' → KNGoal … S'`). All segment modules import this one only (ROW-TIME
LESSON); `kar_step` composes them.

Boundaries (`X0 X1 Y0 Y1` the halves of `x`, `y`; `E = 2^(64·n2)`):
* `KM1` `0x5f2149` (prologue done: `z1 = (0, t, kT, kT)`, `tx = (0, zp, n2, zc)`, `ty = (0, zp+8n2, n2, zc-n2)`,
  `z0`/`z2` headers);
* `KM2` `0x5f2166` (after `tx.Sub(x0, x1)`): `tx = X0 - X1` (signed) in `z[0:ltx]`;
* `KM2b` `0x5f2185` (after `ty.Sub(y1, y0)`): `ty = Y1 - Y0` in `z[n2:n2+lty]`;
* `KM3` `0x5f21c6` (after `z1.mul(stk, tx, ty)`, `clear(z)`): `z1 = (X0-X1)(Y1-Y0)` in `t`, `z[0:2n] = 0`;
* `KM4` `0x5f21eb` (after `z0.mul(stk, x0, y0)`): `z[0:2n2] = X0·Y0`, `z[2n2:2n] = 0`;
* `KM5` `0x5f2210` (after `z2.mul(stk, x1, y1)`): `z[2n2:2n] = X1·Y1`;
* `KM6` `0x5f2228` (after `z1.Add(z1, z0)`); `KM7` `0x5f2245` (after `z1.Add(z1, z2)`): `z1 = X0·Y1 + X1·Y0` in `t`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep IntAt apart_of_held tN' tls)

/-- `z0`'s header (frame `SP - 176`) as built by the prologue: `z[0:2·n2]` -/
@[reducible] def Z0H (s : State) (M : Memory) (zp zc n : Nat) : Prop :=
  IntAt M ((s.regs 4).toNat - 176) 0 zp (2 * kh n) zc
/-- `z2`'s header (frame `SP - 208`) as built by the prologue: `z[2·n2:]` -/
@[reducible] def Z2H (s : State) (M : Memory) (zp zc n : Nat) : Prop :=
  IntAt M ((s.regs 4).toNat - 208) 0 (zp + 16 * kh n) (2 * n - 2 * kh n) (zc - 2 * kh n)

/-- the signed value of a header `(ng, ·, l)` over `v` -/
@[reducible] def sgnV (ng v : Nat) : Int := if ng = 0 then (v : Int) else -(v : Int)

structure KM1 (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk : Nat) : Prop where
  pos : KNAt s S 0x5f2149
  km : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc1 n) S.mem
  z1h : IntAt S.mem ((s.regs 4).toNat - 264) 0 t (kT n) (kT n)
  txh : IntAt S.mem ((s.regs 4).toNat - 296) 0 zp (kh n) zc
  tyh : IntAt S.mem ((s.regs 4).toNat - 328) 0 (zp + 8 * kh n) (kh n) (zc - kh n)
  z0h : Z0H s S.mem zp zc n
  z2h : Z2H s S.mem zp zc n

structure KM2 (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk tng ltx : Nat) : Prop where
  pos : KNAt s S 0x5f2166
  km : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc2 n) S.mem
  z1h : IntAt S.mem ((s.regs 4).toNat - 264) 0 t (kT n) (kT n)
  txh : IntAt S.mem ((s.regs 4).toNat - 296) tng zp ltx zc
  htng : tng ≤ 1
  tcan : tng = 1 → 0 < ltx
  hltx : ltx ≤ kh n
  tv : sgnV tng (natVal S.mem zp ltx) = (kX0 s xp n : Int) - (kX1 s xp n : Int)
  tnn : NatNorm S.mem zp ltx
  tyh : IntAt S.mem ((s.regs 4).toNat - 328) 0 (zp + 8 * kh n) (kh n) (zc - kh n)
  z0h : Z0H s S.mem zp zc n
  z2h : Z2H s S.mem zp zc n

structure KM2b (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk tng ltx yng lty : Nat) : Prop where
  pos : KNAt s S 0x5f2185
  km : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc2b n) S.mem
  z1h : IntAt S.mem ((s.regs 4).toNat - 264) 0 t (kT n) (kT n)
  txh : IntAt S.mem ((s.regs 4).toNat - 296) tng zp ltx zc
  htng : tng ≤ 1
  hltx : ltx ≤ kh n
  tv : sgnV tng (natVal S.mem zp ltx) = (kX0 s xp n : Int) - (kX1 s xp n : Int)
  tnn : NatNorm S.mem zp ltx
  tyh : IntAt S.mem ((s.regs 4).toNat - 328) yng (zp + 8 * kh n) lty (zc - kh n)
  hyng : yng ≤ 1
  hlty : lty ≤ kh n
  yv : sgnV yng (natVal S.mem (zp + 8 * kh n) lty) = (kX1 s yp n : Int) - (kX0 s yp n : Int)
  ynn : NatNorm S.mem (zp + 8 * kh n) lty
  z0h : Z0H s S.mem zp zc n
  z2h : Z2H s S.mem zp zc n

structure KM3 (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk ng l1 : Nat) : Prop where
  pos : KNAt s S 0x5f21c6
  km : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc3 n) S.mem
  z1h : IntAt S.mem ((s.regs 4).toNat - 264) ng t l1 (kT n)
  hng : ng ≤ 1
  hcan : ng = 1 → 0 < l1
  hl1 : l1 ≤ 2 * kh n
  z1v : sgnV ng (natVal S.mem t l1) =
    ((kX0 s xp n : Int) - (kX1 s xp n : Int)) * ((kX1 s yp n : Int) - (kX0 s yp n : Int))
  z1n : NatNorm S.mem t l1
  z0h : Z0H s S.mem zp zc n
  z2h : Z2H s S.mem zp zc n
  zz : natVal S.mem zp (2 * n) = 0

structure KM4 (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk ng l1 l0 : Nat) : Prop where
  pos : KNAt s S 0x5f21eb
  km : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc4 n) S.mem
  z1h : IntAt S.mem ((s.regs 4).toNat - 264) ng t l1 (kT n)
  hng : ng ≤ 1
  hcan : ng = 1 → 0 < l1
  hl1 : l1 ≤ 2 * kh n
  z1v : sgnV ng (natVal S.mem t l1) =
    ((kX0 s xp n : Int) - (kX1 s xp n : Int)) * ((kX1 s yp n : Int) - (kX0 s yp n : Int))
  z1n : NatNorm S.mem t l1
  z0h : IntAt S.mem ((s.regs 4).toNat - 176) 0 zp l0 zc
  hl0 : l0 ≤ 2 * kh n
  z0v : natVal S.mem zp l0 = kX0 s xp n * kX0 s yp n
  z0n : NatNorm S.mem zp l0
  z2h : Z2H s S.mem zp zc n
  zlo : natVal S.mem zp (2 * kh n) = kX0 s xp n * kX0 s yp n
  zhi : natVal S.mem (zp + 16 * kh n) (2 * n - 2 * kh n) = 0

structure KM5 (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk ng l1 l0 l2 : Nat) : Prop where
  pos : KNAt s S 0x5f2210
  km : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc5 n) S.mem
  z1h : IntAt S.mem ((s.regs 4).toNat - 264) ng t l1 (kT n)
  hng : ng ≤ 1
  hcan : ng = 1 → 0 < l1
  hl1 : l1 ≤ 2 * kh n
  z1v : sgnV ng (natVal S.mem t l1) =
    ((kX0 s xp n : Int) - (kX1 s xp n : Int)) * ((kX1 s yp n : Int) - (kX0 s yp n : Int))
  z1n : NatNorm S.mem t l1
  z0h : IntAt S.mem ((s.regs 4).toNat - 176) 0 zp l0 zc
  hl0 : l0 ≤ 2 * kh n
  z0v : natVal S.mem zp l0 = kX0 s xp n * kX0 s yp n
  z0n : NatNorm S.mem zp l0
  z2h : IntAt S.mem ((s.regs 4).toNat - 208) 0 (zp + 16 * kh n) l2 (zc - 2 * kh n)
  hl2 : l2 ≤ 2 * (n - kh n)
  z2v : natVal S.mem (zp + 16 * kh n) l2 = kX1 s xp n * kX1 s yp n
  z2n : NatNorm S.mem (zp + 16 * kh n) l2
  zlo : natVal S.mem zp (2 * kh n) = kX0 s xp n * kX0 s yp n
  zhi : natVal S.mem (zp + 16 * kh n) (2 * n - 2 * kh n) = kX1 s xp n * kX1 s yp n

/-- after `z1.Add(z1, z0)` (`0x5f2228`): `z1 = (X0-X1)(Y1-Y0) + X0·Y0` (signed) in `t` -/
structure KM6 (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk ng l l2 : Nat) : Prop where
  pos : KNAt s S 0x5f2228
  km : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc6 n) S.mem
  z1h : IntAt S.mem ((s.regs 4).toNat - 264) ng t l (kT n)
  hng : ng ≤ 1
  hcan : ng = 1 → 0 < l
  hl : l ≤ 2 * kh n
  z1v : sgnV ng (natVal S.mem t l) =
    ((kX0 s xp n : Int) - (kX1 s xp n : Int)) * ((kX1 s yp n : Int) - (kX0 s yp n : Int)) +
      ((kX0 s xp n * kX0 s yp n : Nat) : Int)
  z1n : NatNorm S.mem t l
  z2h : IntAt S.mem ((s.regs 4).toNat - 208) 0 (zp + 16 * kh n) l2 (zc - 2 * kh n)
  hl2 : l2 ≤ 2 * (n - kh n)
  z2v : natVal S.mem (zp + 16 * kh n) l2 = kX1 s xp n * kX1 s yp n
  z2n : NatNorm S.mem (zp + 16 * kh n) l2
  zlo : natVal S.mem zp (2 * kh n) = kX0 s xp n * kX0 s yp n
  zhi : natVal S.mem (zp + 16 * kh n) (2 * n - 2 * kh n) = kX1 s xp n * kX1 s yp n

structure KM7 (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 t : Nat) (S : State) (Lk : List (Nat × Nat)) (bk l : Nat) : Prop where
  pos : KNAt s S 0x5f2245
  km : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc7 n) S.mem
  z1h : IntAt S.mem ((s.regs 4).toNat - 264) 0 t l (kT n)
  hl : l ≤ kT n
  z1v : natVal S.mem t l = kX0 s xp n * kX1 s yp n + kX1 s xp n * kX0 s yp n
  zlo : natVal S.mem zp (2 * kh n) = kX0 s xp n * kX0 s yp n
  zhi : natVal S.mem (zp + 16 * kh n) (2 * n - 2 * kh n) = kX1 s xp n * kX1 s yp n

/-! ## Helpers shared by the segments -/

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}

/-- a read in our frame above a callee's window (`RSP - 376 ≤ x`, below `RSP + 72`) and outside the callee's writes
keeps its bytes -/
theorem KN.rdW (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {M' : Memory} {k a : Nat}
    (hk : 456 + k ≤ W) (ha : a ≤ 80) {ws : List (Nat × Nat)}
    (hF : MemFrame M M' (R.rt ++ [((s.regs 4).toNat - 456 - k, (s.regs 4).toNat - 456 + a)] ++ ws)) {x m : Nat}
    (h1 : (s.regs 4).toNat - 376 ≤ x) (h2 : x + m ≤ (s.regs 4).toNat + 72)
    (hws : Outside x m ws) : M'.readLE x m = M.readLE x m := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, -, -, hout, -, -⟩ := h.lay
  exact kn_rd hk ha hWs hout hF hws h1 h2

/-- the scratch `t`: live, outside the window, apart from the guard word, from `z`, `x` and `y` -/
theorem KN.tops (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    NatLive M R Lk t (kT n) ∧ Outside t (8 * kT n) (win s W 72) ∧ Apart t (8 * kT n) (NatSqr.guard s) 8 ∧
      Apart t (8 * kT n) zp (8 * zc) ∧ Apart t (8 * kT n) xp (8 * n) ∧ Apart t (8 * kT n) yp (8 * n) ∧
      t + 8 * kT n ≤ 2 ^ 48 := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, -, -, hout, hgr, hga⟩ := h.lay
  have F := h.F
  have hzs := F.zs
  have hxh := F.xh
  have hyh := F.yh
  have hxc := F.xcn
  have hyc := F.ycn
  have hzl := F.zc2
  have h40 := F.n40
  obtain ⟨-, -, -, -, -, hfg, hfw, -⟩ := F.stk
  obtain ⟨-, hzh, -, -⟩ := F.zlive (by omega)
  have hsc := h.scr
  have hlive : NatLive M R Lk t (kT n) := fun _ =>
    ⟨hsc.al, hsc.held, by rw [h.fr.accessible]; exact hsc.acc, hsc.b48⟩
  have hzt : Apart t (8 * kT n) zp (8 * zc) := hsc.apart hzh (fun _ => by
    have := hzs.2.1; simp only [BasicSqr.freeP, BasicSqr.freeN] at this; exact this)
  simp only [BasicSqr.freeP, BasicSqr.freeN, NatSqr.guard] at hfg hfw
  simp only [win, outside_cons, outside_nil, and_true] at hfw ⊢
  rcases hsc.loc with ⟨-, h1, h2⟩ | ⟨hin, hap⟩
  · have hx2 := F.xs.2.1; simp only [BasicSqr.freeP, BasicSqr.freeN] at hx2
    have hy2 := F.ys.2.1; simp only [BasicSqr.freeP, BasicSqr.freeN] at hy2
    refine ⟨hlive, by omega, by simp only [NatSqr.guard]; unfold Apart at hfg ⊢; omega, hzt,
      by unfold Apart at hx2 ⊢; omega, by unfold Apart at hy2 ⊢; omega, hsc.b48⟩
  · have ho := NatSub.outside_of_inRanges hout hin
    have hg := NatSub.outside_of_inRanges hgr hin
    exact ⟨hlive, by omega, by simp only [NatSqr.guard]; unfold Apart; omega, hzt,
      apart_of_held (hxh.sub (by omega) (by omega)) hin hap, apart_of_held (hyh.sub (by omega) (by omega)) hin hap,
      hsc.b48⟩

/-- `z`'s array facts at `M` -/
theorem KN.zops (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    zc < 2 ^ 40 ∧ NatLive M R Lk zp zc ∧ Outside zp (8 * zc) (win s W 72) ∧
      Apart zp (8 * zc) (NatSqr.guard s) 8 ∧ StkSep M st zp (8 * zc) ∧ 2 * n ≤ zc ∧
      zp % 8 = 0 ∧ Held R Lk zp (8 * zc) ∧ zp + 8 * zc ≤ 2 ^ 48 := by
  have F := h.F
  have hzl := F.zc2
  have h40 := F.n40
  obtain ⟨hal, hh, hacc, h48⟩ := F.zlive (by omega)
  exact ⟨F.zc40, fun _ => ⟨hal, h.ext.held hh, by rw [h.fr.accessible]; exact hacc, h48⟩, F.zw, F.zg,
    h.sepOf F.zs hh, hzl, hal, h.ext.held hh, h48⟩

/-- the scratch `t` and `z` are apart from the TLS slot (amd64) -/
theorem KN.ttls (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) :
    Apart t (8 * kT n) (tls s) 8 ∧ Apart zp (8 * zc) (tls s) 8 := by
  have F := h.F
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, htrt, -⟩⟩ := F.env
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hftl⟩ := F.stk
  refine ⟨?_, F.zt⟩
  simp only [tls, BasicSqr.freeP, BasicSqr.freeN] at hftl htrt ⊢
  rcases h.scr.loc with ⟨-, h1, h2⟩ | ⟨hin, -⟩
  · unfold Apart at hftl ⊢; omega
  · have := NatSub.outside_of_inRanges htrt hin; unfold Apart; omega

/-- the live set is apart from a frame range -/
theorem KN.frameHeld (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {a k : Nat}
    (h1 : (s.regs 4).toNat - W ≤ a) (h2 : a + k ≤ (s.regs 4).toNat + 72) : Held R Lk a k := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, -, -, hout, -, -⟩ := h.lay
  exact Or.inr (hout.of_sub h1 (by omega))

end

/-! ## Calls out of `karatsuba` -/

set_option maxRecDepth 20000 in
/-- a return address inside `karatsuba` (segment `seg57`, base `0x5f1da0`, `0x597` bytes) -/
theorem kn_ra {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fnK = false) (i : Nat) (hi : i < 0x597) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (0x5f1da0 + i) := by
  have := IntAS.retAddr_restrict hap (cs := Extracted.seg57) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5f1da0 + i < 2 ^ 47; omega)
  rw [show Extracted.seg57.base = 0x5f1da0 from rfl] at this; exact this

/-- the facts about a read-only `*Int` operand's `abs` (`IntAS.OpR` without the header, which is in our frame) -/
@[reducible] def KIOp (R : RtInv) (Lk : List (Nat × Nat)) (s : State) (W : Nat) (M : Memory) (a : Nat) : Prop :=
  IntAS.hNeg M a ≤ 1 ∧ IntAS.hL M a ≤ IntAS.hC M a ∧ IntAS.hC M a < 2 ^ 40 ∧ IntAS.hL M a ≤ 2 ^ 16 ∧
    M.accessible (IntAS.hP M a) (8 * IntAS.hL M a) false = true ∧ IntAS.hP M a + 8 * IntAS.hL M a ≤ 2 ^ 48 ∧
    Held R Lk (IntAS.hP M a) (8 * IntAS.hL M a) ∧ NatNorm M (IntAS.hP M a) (IntAS.hL M a) ∧
    Outside (IntAS.hP M a) (8 * IntAS.hL M a) (win s W 72)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}

/-- frame header ranges are readable and writable -/
theorem KN.facc (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {q : Nat} (v : Bool)
    (h1 : (s.regs 4).toNat - 456 ≤ q) (h2 : q + 32 ≤ (s.regs 4).toNat + 72) : M.accessible q 32 v = true := by
  obtain ⟨hW, hWs, -⟩ := h.lay
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := h.F.env.2.1.2.2
  rw [h.fr.accessible]
  cases v
  · exact Janus.Arm64.Memory.accessible_sub _ hw0 (Or.inr rfl) (by omega) (by omega)
  · exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)

set_option maxRecDepth 20000 in
/-- **`IntAS.Pre` of `(*Int).Add/Sub(z, x, y)` at `RSP - 456`** with the three headers in our frame -/
theorem KN.intPre (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {S1 : State}
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456) (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = M)
    (hfs : S1.fsBase = s.fsBase) {z x y : Nat} (hz1 : (s.regs 4).toNat - 328 ≤ z) (hz2 : z + 32 ≤ (s.regs 4).toNat - 16)
    (hx1 : (s.regs 4).toNat - 328 ≤ x) (hx2 : x + 32 ≤ (s.regs 4).toNat - 16)
    (hy1 : (s.regs 4).toNat - 328 ≤ y) (hy2 : y + 32 ≤ (s.regs 4).toNat - 16)
    (hzx : z = x ∨ Apart z 32 x 32) (hzy : Apart z 32 y 32)
    (hox : KIOp R Lk s W M x) (hoy : KIOp R Lk s W M y)
    (hzc : IntAS.hC M z < 2 ^ 40) (hzl : NatLive M R Lk (IntAS.hP M z) (IntAS.hC M z))
    (hzw : Outside (IntAS.hP M z) (8 * IntAS.hC M z) (win s W 72))
    (hza : 0 < IntAS.hC M z → Apart (IntAS.hP M z) (8 * IntAS.hC M z) (NatSqr.guard s) 8 ∧
      Apart (IntAS.hP M z) (8 * IntAS.hC M z) (tls s) 8 ∧
      (IntAS.hP M z = IntAS.hP M x ∨ Apart (IntAS.hP M z) (8 * IntAS.hC M z) (IntAS.hP M x) (8 * IntAS.hL M x)) ∧
      (IntAS.hP M z = IntAS.hP M y ∨ Apart (IntAS.hP M z) (8 * IntAS.hC M z) (IntAS.hP M y) (8 * IntAS.hL M y)))
    (hcost : IntAS.asCost (IntAS.hL M x) (IntAS.hL M y) ≤ bk) :
    IntAS.Pre R bk Lk z x y S1 := by
  obtain ⟨hW, hWs, hal, ha48, -, -, -, -, -, -, -, -, hout, hgr, hga⟩ := h.lay
  have F := h.F
  have htw : Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - W) (W + 72) := F.env.2.2.2.2.2.2.2.2.2.2.2
  have hgl : Globals R M (win s W 72) := h.glob fun _ _ hx => hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwbacc, -, hwbw⟩ := hgl
  have hwin : ∀ q k, Outside q k (win s W 72) → Outside q k (win S1 4536 32) :=
    fun q k hq => h.winIn hsp (by omega) (by omega) hq
  have hfw : ∀ q, (s.regs 4).toNat - 328 ≤ q → q + 32 ≤ (s.regs 4).toNat - 16 → Outside q 32 (win S1 4536 32) := by
    intro q h1 h2; simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  have hrt : ∀ q, (s.regs 4).toNat - 328 ≤ q → q + 32 ≤ (s.regs 4).toNat - 16 → Outside q 32 R.rt :=
    fun q h1 h2 => hout.of_sub (by omega) (by omega)
  have hop : ∀ q, (s.regs 4).toNat - 328 ≤ q → q + 32 ≤ (s.regs 4).toNat - 16 → KIOp R Lk s W M q → IntAS.OpR R Lk S1 q := by
    intro q h1 h2 ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩
    subst hm
    exact ⟨o1, h.facc false (by omega) (by omega), by omega, hfw q h1 h2, o2, o3, o4, o5, o6, o7, o8, hwin _ _ o9⟩
  simp only [win, outside_cons, outside_nil, and_true] at hwbw
  subst hm
  refine ⟨h.callee hsp hg rfl hfs (by omega) (by omega), F.sv, F.wt, hop x hx1 hx2 hox, hop y hy1 hy2 hoy,
    h.facc true (by omega) (by omega), by omega, hfw z hz1 hz2, Or.inr (hrt z hz1 hz2),
    by rw [hg]; unfold Apart at hga ⊢; omega,
    by rw [hfs]; unfold Apart at htw ⊢; omega,
    by show Apart z 32 RunIface.wbA 4; unfold Apart; omega, hzx, hzy, hzc, hzl, hwin _ _ hzw, fun hc => ?_, hwbacc,
    hcost, by rw [hg]; exact h.inv⟩
  obtain ⟨q1, q1t, q2, q3⟩ := hza hc
  simp only [win, outside_cons, outside_nil, and_true] at hzw
  refine ⟨by simp only [NatSqr.guard] at q1; rw [hg]; exact q1, by simp only [tls] at q1t; rw [hfs]; exact q1t,
    by unfold Apart; omega, q2, q3⟩

end

set_option maxRecDepth 20000 in
/-- **A `(*Int).Add/Sub(z, x, y)` call from `karatsuba`'s frame** (at the callee entry, return address inside
`karatsuba`): `KN.intPre` discharges the callee's precondition; the continuation gets its postcondition. -/
theorem kn_intcall (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) (sub : Bool)
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 (IntAS.entry sub)) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456)
    (hg : S1.regs 14 = s.regs 14) (hm : S1.mem = M) (hfs : S1.fsBase = s.fsBase) {i : Nat} (hi : i < 0x597)
    (hrd : S1.mem.readLE (S1.regs 4).toNat 8 = 0x5f1da0 + i) (hx15 : S1.xmm 15 = 0#128) (hdf : S1.df = false)
    {z x y : Nat} (r0 : S1.regs 0 = BitVec.ofNat 64 z) (r1 : S1.regs 3 = BitVec.ofNat 64 x)
    (r2 : S1.regs 1 = BitVec.ofNat 64 y)
    (hz1 : (s.regs 4).toNat - 328 ≤ z) (hz2 : z + 32 ≤ (s.regs 4).toNat - 16)
    (hx1 : (s.regs 4).toNat - 328 ≤ x) (hx2 : x + 32 ≤ (s.regs 4).toNat - 16)
    (hy1 : (s.regs 4).toNat - 328 ≤ y) (hy2 : y + 32 ≤ (s.regs 4).toNat - 16)
    (hzx : z = x ∨ Apart z 32 x 32) (hzy : Apart z 32 y 32)
    (hox : KIOp R Lk s W M x) (hoy : KIOp R Lk s W M y)
    (hzc : IntAS.hC M z < 2 ^ 40) (hzl : NatLive M R Lk (IntAS.hP M z) (IntAS.hC M z))
    (hzw : Outside (IntAS.hP M z) (8 * IntAS.hC M z) (win s W 72))
    (hza : 0 < IntAS.hC M z → Apart (IntAS.hP M z) (8 * IntAS.hC M z) (NatSqr.guard s) 8 ∧
      Apart (IntAS.hP M z) (8 * IntAS.hC M z) (tls s) 8 ∧
      (IntAS.hP M z = IntAS.hP M x ∨ Apart (IntAS.hP M z) (8 * IntAS.hC M z) (IntAS.hP M x) (8 * IntAS.hL M x)) ∧
      (IntAS.hP M z = IntAS.hP M y ∨ Apart (IntAS.hP M z) (8 * IntAS.hC M z) (IntAS.hP M y) (8 * IntAS.hL M y)))
    (hcost : IntAS.asCost (IntAS.hL M x) (IntAS.hL M y) ≤ bk)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ s2 : State, s2.rip = BitVec.ofNat 64 (0x5f1da0 + i) → s2.mem.regions = M.regions →
      (s2.regs 4 = S1.regs 4 + 8 ∧ s2.regs 5 = S1.regs 5 ∧ s2.regs 14 = S1.regs 14 ∧ s2.xmm 15 = S1.xmm 15) →
      IntAS.Post sub R bk Lk z x y S1 s2 → ReachesRet (LibMul.program.link impl) ret s2 Q) :
    ReachesRet (LibMul.program.link impl) ret S1 Q := by
  have hb := h.lay
  have hz64 : z < 2 ^ 64 := by omega
  have hx64 : x < 2 ^ 64 := by omega
  have hy64 : y < 2 ^ 64 := by omega
  have hP := h.intPre hsp hg hm hfs hz1 hz2 hx1 hx2 hy1 hy2 hzx hzy hox hoy hzc hzl hzw hza hcost
  have hS := IntAS.sum impl hap R hmk hmv hwb sub bk Lk (BitVec.ofNat 64 z) (BitVec.ofNat 64 x) (BitVec.ofNat 64 y)
    LibMul.names (IntAS.sub_of_all (by decide))
  rw [← LibMul.eq_only, IntAS.entry_eq] at hS
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, by simp [ArgsFrom64, argReg, intArgRegs, r0, r1, r2], hdf, ?_⟩ fun s2 hr hq hreg => ?_
  · simp only [regSP]; rw [hrd]; exact kn_ra hap (by decide) i hi
  · rw [tN' hz64, tN' hx64, tN' hy64]; exact hP
  · obtain ⟨hk, hq⟩ := hq
    rw [tN' hz64, tN' hx64, tN' hy64] at hq
    exact hK s2 (by rw [hr, retAddrOf, hrd]) (by rw [hreg, hm]) hk hq

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}

set_option maxRecDepth 20000 in
/-- **After an `(*Int).Add/Sub` call** (header `z` in a writable header area, array writes inside `z[0:2n]` or `t`):
`KN` holds again -/
theorem KN.intStep (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {M' : Memory}
    {S1 : State} (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456) {z q w : Nat}
    (hz : ((s.regs 4).toNat - 328 ≤ z ∧ z + 32 ≤ (s.regs 4).toNat - 232) ∨ ((s.regs 4).toNat - 208 ≤ z ∧ z + 32 ≤ (s.regs 4).toNat - 144))
    (hq : (zp ≤ q ∧ q + 8 * w ≤ zp + 8 * (2 * n)) ∨ (t ≤ q ∧ q + 8 * w ≤ t + 8 * kT n))
    (hF : MemFrame M M' (R.rt ++ win S1 4536 32 ++ [(z, z + 32), (q, q + 8 * w)]))
    (hLF : LiveFrame M M' Lk [(z, z + 32), (q, q + 8 * w)]) (hreg : M'.regions = M.regions)
    {Lk' : List (Nat × Nat)} {bk' c : Nat} (hext : LiveExt R Lk Lk') (hb : bk - c ≤ bk')
    (hc : spent + c ≤ KCQ n)
    (hinv : R.inv bk' Lk' (s.regs 14).toNat (view R.rt Lk' M')) :
    KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk' bk' (spent + c) M' := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, -, -, hout, -, -⟩ := h.lay
  have F := h.F
  have hstw : Outside st 24 (win s W 72) := F.stk.2.2.1
  have hzs := F.zs
  have hzl := F.zc2
  have hts := h.tsep.1
  have hzs1 := hzs.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  unfold Apart at hts hzs1
  simp only [win, hsp] at hF
  have hF' : MemFrame M M' (R.rt ++ ([((s.regs 4).toNat - 456 - 4536, (s.regs 4).toNat - 456 + 32)] ++
      [(z, z + 32), (q, q + 8 * w)])) := by
    rw [← List.append_assoc]; exact hF
  have hsbC : StackBackL R Lk Lk' st M M' ∧ stCap M' st = stCap M st := by
    refine NatSqr.stackBack_keepC h.sok hF'
      (FvModexp.LiveFrame.mono_ws hLF fun a k ho => by rw [outside_append] at ho; exact ho.2) ?_ hext
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨by omega, by omega, by omega⟩
  refine h.step (k := 4536) (a := 32) (by omega) (by omega) (fun r hr => ?_) hF hLF hreg hext (Or.inr ⟨hb, hsbC.2⟩) hc
    hinv hsbC.1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hz with hz | hz
    · exact ⟨by simp only; omega, Or.inr (Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩))⟩
    · exact ⟨by simp only; omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩)))⟩
  · rcases hq with hq | hq
    · exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩
    · exact ⟨by simp only; omega, Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩)⟩

set_option maxRecDepth 20000 in
/-- **Stores in the frame's writable header areas keep `KN`** -/
theorem KN.store (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {M' : Memory}
    {ws : List (Nat × Nat)}
    (hws : ∀ r ∈ ws, r.1 ≤ r.2 ∧ (((s.regs 4).toNat - 328 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 232) ∨
      ((s.regs 4).toNat - 208 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat - 144)))
    (hF : MemFrame M M' ws) (hreg : M'.regions = M.regions) :
    KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M' := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, -, -, hout, -, -⟩ := h.lay
  have hstw : Outside st 24 (win s W 72) := h.F.stk.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hrt : ∀ r ∈ ws, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    obtain ⟨h1, h2 | h2⟩ := hws r hr <;> exact hout.of_sub (by omega) (by omega)
  have hF' : MemFrame M M' (R.rt ++ [((s.regs 4).toNat - 456 - 0, (s.regs 4).toNat - 456 + 8)] ++ ws) :=
    hF.mono fun a k ho => by simp only [outside_append] at ho; exact ho.2
  have hLF : LiveFrame M M' Lk ws := ⟨fun a k _ ho => hF.readLE a k ho⟩
  have hinv := RtInv.inv_frame' hF (fun r hr => Or.inl (hrt r hr)) h.inv
  have hsbC := NatSqr.stackBack_keepC h.sok (hF.mono fun a k ho => by
      simp only [outside_append] at ho; exact ho.2) hLF (outside_of_forall fun r hr => by
      obtain ⟨h1, h2 | h2⟩ := hws r hr <;> omega) (LiveExt.refl R Lk)
  have hsb : StackBackL R Lk Lk st M M' := hsbC.1
  have := h.step (k := 0) (a := 8) (by omega) (by omega) (fun r hr => by
      obtain ⟨h1, h2 | h2⟩ := hws r hr
      · exact ⟨h1, Or.inr (Or.inr (Or.inl h2))⟩
      · exact ⟨h1, Or.inr (Or.inr (Or.inr (Or.inl h2)))⟩) hF' hLF hreg (LiveExt.refl R Lk) (c := 0)
    (Or.inr ⟨by omega, hsbC.2⟩) (by have := h.spk; omega) hinv hsb
  simpa using this

/-- an `KIOp` from a header in our frame and the facts about its array -/
theorem KN.iop (_h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {a ng p l c : Nat}
    (hh : IntAt M a ng p l c) (hng : ng ≤ 1) (hlc : l ≤ c) (hc : c < 2 ^ 40) (hl : l ≤ 2 ^ 16)
    (hacc : M.accessible p (8 * l) false = true) (h48 : p + 8 * l ≤ 2 ^ 48) (hH : Held R Lk p (8 * l))
    (hn : NatNorm M p l) (hw : Outside p (8 * l) (win s W 72)) : KIOp R Lk s W M a := by
  obtain ⟨q1, q2, q3, q4⟩ := hh
  simp only [KIOp, IntAS.hNeg, IntAS.hP, IntAS.hL, IntAS.hC, q1, q2, q3, q4]
  exact ⟨hng, hlc, hc, hl, hacc, h48, hH, hn, hw⟩

/-- a half `x[o:o+l]` of `x` (or `y`): the operand facts at `M` -/
theorem KN.halfX (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {o l : Nat}
    (hol : o + l ≤ n) :
    M.accessible (xp + 8 * o) (8 * l) false = true ∧ xp + 8 * o + 8 * l ≤ 2 ^ 48 ∧
      Held R Lk (xp + 8 * o) (8 * (xc - o)) ∧ xp + 8 * o + 8 * (xc - o) ≤ 2 ^ 48 ∧
      Outside (xp + 8 * o) (8 * l) (win s W 72) ∧ StkSep M st (xp + 8 * o) (8 * l) ∧
      Apart zp (8 * zc) (xp + 8 * o) (8 * l) ∧ natVal M (xp + 8 * o) l = natVal s.mem (xp + 8 * o) l ∧
      (NatNorm s.mem (xp + 8 * o) l → NatNorm M (xp + 8 * o) l) := by
  have F := h.F
  have hxc := F.xcn
  have hxh := h.ext.held F.xh
  have hrd : ∀ a k, xp + 8 * o ≤ a → a + k ≤ xp + 8 * o + 8 * l → M.readLE a k = s.mem.readLE a k :=
    fun a k h1 h2 => h.xrd (by omega) (by omega)
  have hs : StkSep M st (xp + 8 * o) (8 * l) := by
    obtain ⟨q1, q2, q3⟩ := h.sepOf F.xs (F.xh.sub (Nat.le_refl _) (by omega))
    simp only [BasicSqr.freeP, BasicSqr.freeN] at q2
    unfold Apart at q1 q2 q3
    exact ⟨by unfold Apart; omega, by simp only [BasicSqr.freeP, BasicSqr.freeN]; unfold Apart; omega, by unfold Apart; omega⟩
  have hzx := F.zx
  refine ⟨?_, by have := F.x48; omega, hxh.sub (by omega) (by omega), by have := F.x48; omega,
    F.xw.of_sub (by omega) (by omega), hs, by unfold Apart at hzx ⊢; omega, ?_, ?_⟩
  · rw [h.fr.accessible]; exact Janus.Arm64.Memory.accessible_sub _ F.xacc (Or.inl rfl) (by omega) (by omega)
  · unfold natVal; exact hrd _ _ (Nat.le_refl _) (Nat.le_refl _)
  · intro hn
    rcases hn with h0 | h0
    · exact Or.inl h0
    · by_cases hl0 : l = 0
      · exact Or.inl hl0
      · right; rwa [hrd _ _ (by omega) (by omega)]

theorem KN.halfY (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {o l : Nat}
    (hol : o + l ≤ n) :
    M.accessible (yp + 8 * o) (8 * l) false = true ∧ yp + 8 * o + 8 * l ≤ 2 ^ 48 ∧
      Held R Lk (yp + 8 * o) (8 * (yc - o)) ∧ yp + 8 * o + 8 * (yc - o) ≤ 2 ^ 48 ∧
      Outside (yp + 8 * o) (8 * l) (win s W 72) ∧ StkSep M st (yp + 8 * o) (8 * l) ∧
      Apart zp (8 * zc) (yp + 8 * o) (8 * l) ∧ natVal M (yp + 8 * o) l = natVal s.mem (yp + 8 * o) l ∧
      (NatNorm s.mem (yp + 8 * o) l → NatNorm M (yp + 8 * o) l) := by
  have F := h.F
  have hyc := F.ycn
  have hyh := h.ext.held F.yh
  have hrd : ∀ a k, yp + 8 * o ≤ a → a + k ≤ yp + 8 * o + 8 * l → M.readLE a k = s.mem.readLE a k :=
    fun a k h1 h2 => h.yrd (by omega) (by omega)
  have hs : StkSep M st (yp + 8 * o) (8 * l) := by
    obtain ⟨q1, q2, q3⟩ := h.sepOf F.ys (F.yh.sub (Nat.le_refl _) (by omega))
    simp only [BasicSqr.freeP, BasicSqr.freeN] at q2
    unfold Apart at q1 q2 q3
    exact ⟨by unfold Apart; omega, by simp only [BasicSqr.freeP, BasicSqr.freeN]; unfold Apart; omega, by unfold Apart; omega⟩
  have hzy := F.zy
  refine ⟨?_, by have := F.y48; omega, hyh.sub (by omega) (by omega), by have := F.y48; omega,
    F.yw.of_sub (by omega) (by omega), hs, by unfold Apart at hzy ⊢; omega, ?_, ?_⟩
  · rw [h.fr.accessible]; exact Janus.Arm64.Memory.accessible_sub _ F.yacc (Or.inl rfl) (by omega) (by omega)
  · unfold natVal; exact hrd _ _ (Nat.le_refl _) (Nat.le_refl _)
  · intro hn
    rcases hn with h0 | h0
    · exact Or.inl h0
    · by_cases hl0 : l = 0
      · exact Or.inl hl0
      · right; rwa [hrd _ _ (by omega) (by omega)]

/-- a part `z[o:o+l]` (inside `z[0:2n]`) of `z` with the capacity to `z`'s end: the operand facts at `M` -/
theorem KN.partZ (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {o l : Nat}
    (hol : o + l ≤ 2 * n) :
    M.accessible (zp + 8 * o) (8 * l) false = true ∧ zp + 8 * o + 8 * l ≤ 2 ^ 48 ∧
      Held R Lk (zp + 8 * o) (8 * (zc - o)) ∧ zp + 8 * o + 8 * (zc - o) ≤ 2 ^ 48 ∧
      Outside (zp + 8 * o) (8 * l) (win s W 72) ∧ StkSep M st (zp + 8 * o) (8 * l) ∧
      NatLive M R Lk (zp + 8 * o) (zc - o) ∧ Outside (zp + 8 * o) (8 * (zc - o)) (win s W 72) ∧
      Apart (zp + 8 * o) (8 * (zc - o)) (NatSqr.guard s) 8 ∧ StkSep M st (zp + 8 * o) (8 * (zc - o)) := by
  obtain ⟨hzc40, hzlive, hzw, hzg, hzs, hzl, hal, hzh, hz48⟩ := h.zops
  have h40 := h.F.n40
  obtain ⟨-, -, hacc, -⟩ := hzlive (by omega)
  obtain ⟨q1, q2, q3⟩ := hzs
  simp only [BasicSqr.freeP, BasicSqr.freeN] at q2
  simp only [NatSqr.guard] at hzg ⊢
  unfold Apart at q1 q2 q3 hzg
  have hacc' : M.accessible (zp + 8 * o) (8 * (zc - o)) true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have s1 : StkSep M st (zp + 8 * o) (8 * l) := by
    refine ⟨?_, ?_, ?_⟩ <;> (try simp only [BasicSqr.freeP, BasicSqr.freeN]) <;> unfold Apart <;> omega
  have s2 : StkSep M st (zp + 8 * o) (8 * (zc - o)) := by
    refine ⟨?_, ?_, ?_⟩ <;> (try simp only [BasicSqr.freeP, BasicSqr.freeN]) <;> unfold Apart <;> omega
  have hl : NatLive M R Lk (zp + 8 * o) (zc - o) := fun _ => ⟨by omega, hzh.sub (by omega) (by omega), hacc', by omega⟩
  exact ⟨Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega), by omega, hzh.sub (by omega) (by omega),
    by omega, hzw.of_sub (by omega) (by omega), s1, hl, hzw.of_sub (by omega) (by omega), by unfold Apart; omega, s2⟩
end

end FvModexp.Amd64.Q.NatMul
