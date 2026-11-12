import FvModexp.Proofs.Arm64.Exp.LibExp
import FvModexp.Proofs.Common.BitLemmas

/-!
# `(*Int).exp` (arm64), segment A: entry → the `m != nil` test done (int.go:575-593; fn+0x0 .. fn+0xcc)

`z.exp(x = z, y, m, slow = false)` as `Run` calls it (X0 = X1 = z, X2 = y, X3 = m, X4 = 0): stack check (falls
through), frame 320 (`STP (R29, R30), -8(R20)` at `SP - 328`), the spills of `z`, `x`, `m`, `slow`
(`SP + 8, + 16, + 32`, byte `+ 40`), `xWords = x.abs` (X14..X16), `y.neg = false` (`TBZ` taken), `yWords = y.abs`
(X7..X9, spilled at `SP' + 152, + 216`), `m ≠ nil`, `z ≠ m`; stops at fn+0xcc (`MOVD 24(R0), R17`, the alias test).
Off-path targets (y.neg, `m == nil`, `z == m`, morestack) are refuted by the premises.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IExp

/-- `(*Int).exp`'s entry -/
abbrev fnI : Nat := 0x1b12f0
/-- `nat.expNN`'s entry -/
abbrev fnN : Nat := 0x1b42b0
/-- the return point of the `expNN` call (fn+0x2dc) -/
abbrev raN : Nat := 0x1b15cc
/-- the alias test `alias(z.abs, m.abs)` (fn+0xcc) -/
abbrev pA : Nat := 0x1b13bc
/-- the join after the alias test (fn+0x28c: `LDP 8(R17), (R19, R20)` with `R17 = m`) -/
abbrev pJ : Nat := 0x1b157c

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runA (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibExp.program.link impl) ret0)
    (Q : Outcome → Prop)
    (t g ret zA yA mA zp zl zc yp yl yc : Nat) (r29 : BitVec 64) (M : Memory)
    (hal : t % 16 = 0) (ht1 : 336 ≤ t) (ht2 : t + 48 ≤ 2 ^ 48)
    (hacc : M.accessible (t - 328) 376 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + 192 < t)
    (hret48 : ret < 2 ^ 48)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : M.accessible zA 32 false = true) (hzS : zA + 32 ≤ t - 328 ∨ t + 48 ≤ zA)
    (hyA : yA + 32 ≤ 2 ^ 48) (hya : M.accessible yA 32 false = true) (hyS : yA + 32 ≤ t - 328 ∨ t + 48 ≤ yA)
    (hmA0 : mA ≠ 0) (hmA : mA < 2 ^ 64) (hzm : zA ≠ mA)
    (hz8 : M.readLE (zA + 8) 8 = zp) (hz16 : M.readLE (zA + 16) 8 = zl) (hz24 : M.readLE (zA + 24) 8 = zc)
    (hy0 : M.readLE yA 1 = 0)
    (hy8 : M.readLE (yA + 8) 8 = yp) (hy16 : M.readLE (yA + 16) 8 = yl) (hy24 : M.readLE (yA + 24) 8 = yc)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 fnI) (hsp : S.sp = BitVec.ofNat 64 t)
    (h0 : S.regs 0 = BitVec.ofNat 64 zA) (h1 : S.regs 1 = BitVec.ofNat 64 zA) (h2 : S.regs 2 = BitVec.ofNat 64 yA)
    (h3 : S.regs 3 = BitVec.ofNat 64 mA) (h4 : S.regs 4 = 0#64)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29)
    (h30 : S.regs 30 = BitVec.ofNat 64 ret) (hmem : S.mem = M)
    (KA : ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 pA → S'.sp = BitVec.ofNat 64 (t - 320) →
      S'.regs 0 = BitVec.ofNat 64 zA → S'.regs 1 = BitVec.ofNat 64 zA → S'.regs 2 = BitVec.ofNat 64 yA →
      S'.regs 3 = BitVec.ofNat 64 mA → S'.regs 4 = 0#64 →
      S'.regs 7 = BitVec.ofNat 64 yp → S'.regs 8 = BitVec.ofNat 64 yl → S'.regs 9 = BitVec.ofNat 64 yc →
      S'.regs 14 = BitVec.ofNat 64 zp → S'.regs 15 = BitVec.ofNat 64 zl → S'.regs 16 = BitVec.ofNat 64 zc →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = BitVec.ofNat 64 (t - 328) → S'.regs 30 = BitVec.ofNat 64 ret → S'.mem = M' →
      MemFrame M M' [(t - 328, t - 8), (t + 8, t + 48)] → M'.regions = M.regions →
      M'.readLE (t - 328) 8 = r29.toNat → M'.readLE (t - 320) 8 = ret →
      M'.readLE (t + 8) 8 = zA → M'.readLE (t + 16) 8 = zA → M'.readLE (t + 32) 8 = mA →
      M'.readLE (t + 40) 1 = 0 → M'.readLE (t - 168) 8 = yl → M'.readLE (t - 104) 8 = yp →
      Reaches ((LibExp.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret0) S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have hzp : zp < 2 ^ 64 := hz8 ▸ Memory.readLE_lt _ _ _
  have hzl : zl < 2 ^ 64 := hz16 ▸ Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := hz24 ▸ Memory.readLE_lt _ _ _
  have hyp : yp < 2 ^ 64 := hy8 ▸ Memory.readLE_lt _ _ _
  have hyl : yl < 2 ^ 64 := hy16 ▸ Memory.readLE_lt _ _ _
  have hyc : yc < 2 ^ 64 := hy24 ▸ Memory.readLE_lt _ _ _
  have es0 : BitVec.ofNat 64 t - 192#64 = BitVec.ofNat 64 (t - 192) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es1 : BitVec.ofNat 64 t - 320#64 = BitVec.ofNat 64 (t - 320) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 320) - 8#64 = BitVec.ofNat 64 (t - 328) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hm0 : BitVec.ofNat 64 mA ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hzm' : BitVec.ofNat 64 zA ≠ BitVec.ofNat 64 mA := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hr29 : r29.toNat < 2 ^ 64 := r29.isLt
  subst hz8 hz16 hz24 hy8 hy16 hy24
  janus_run [es0, es1, es2, hm0, hzm'] until [pA]
  refine KA _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    dsimp only
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (t - 328, t - 8)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (t + 8, t + 48)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals first | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done) | skip
  all_goals first | omega | skip

end FvModexp.Arm64.IExp
