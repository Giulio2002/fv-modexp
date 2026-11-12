import FvModexp.Proofs.Arm64.Int.LibMod
import FvModexp.Proofs.Common.BitLemmas

/-!
# `(*Int).Mod` (arm64), segment A1: entry → the join after the alias test (int.go:325-330; fn+0x0 .. fn+0x190)

`z.Mod(x = z, y)` as `Run` calls it (X0 = X1 = z, X2 = y): stack check (falls through), frame 176 (`MOVD.W R30,
-176(RSP)`, FP at `SP - 184`), the spill of `z` (`SP + 8`), `z == y` (refuted), the nil check of `y` (`MOVB (R2), R27`),
`alias(z.abs, y.abs)`: `cap z = 0`, `cap y = 0` or different last capacity words → the join `pJ` with X4 = y (`y0 = y`).
The aliased case (`y0 = new(Int).Set(y)`, fn+0x5c) is refuted by `hali`, morestack by the guard. No other stores.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IMod

/-- `(*Int).Mod`'s entry -/
abbrev fnM : Nat := 0x1b0f20
/-- `(*Int).QuoRem`'s entry -/
abbrev fnQ : Nat := 0x1b0d70
/-- `nat.div`'s entry -/
abbrev fnD : Nat := 0x1b9200
/-- the join after the alias test (fn+0x190: `MOVD R4, 88(RSP)`) -/
abbrev pJ : Nat := 0x1b10b0
/-- the return point of the `QuoRem` call in `Mod` (fn+0x1ac) -/
abbrev raQ : Nat := 0x1b10cc
/-- the return point of the `nat.div` call in `QuoRem` (fn+0x5c) -/
abbrev raD : Nat := 0x1b0dcc

/-- the address of the last capacity word of a nat `(p, _, c)` as the machine computes it -/
@[reducible] def lastA (p c : Nat) : Nat := (p + 8 * (c - 1)) % 2 ^ 64

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runA1 (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibMod.program.link impl) ret0)
    (Q : Outcome → Prop)
    (t g ret zA yA zp zc yp yc : Nat) (r29 : BitVec 64) (M : Memory)
    (hal : t % 16 = 0) (ht1 : 336 ≤ t) (ht2 : t + 32 ≤ 2 ^ 48)
    (hacc : M.accessible (t - 184) 200 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + 320 < t)
    (hret48 : ret < 2 ^ 48)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : M.accessible zA 32 false = true) (hzS : zA + 32 ≤ t - 184 ∨ t + 16 ≤ zA)
    (hyA : yA + 32 ≤ 2 ^ 48) (hya : M.accessible yA 32 false = true) (hyS : yA + 32 ≤ t - 184 ∨ t + 16 ≤ yA)
    (hzy : zA ≠ yA)
    (hz8 : M.readLE (zA + 8) 8 = zp) (hz24 : M.readLE (zA + 24) 8 = zc)
    (hy8 : M.readLE (yA + 8) 8 = yp) (hy24 : M.readLE (yA + 24) 8 = yc)
    (hali : zc = 0 ∨ yc = 0 ∨ lastA zp zc ≠ lastA yp yc)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 fnM) (hsp : S.sp = BitVec.ofNat 64 t)
    (h0 : S.regs 0 = BitVec.ofNat 64 zA) (h1 : S.regs 1 = BitVec.ofNat 64 zA) (h2 : S.regs 2 = BitVec.ofNat 64 yA)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29)
    (h30 : S.regs 30 = BitVec.ofNat 64 ret) (hmem : S.mem = M)
    (KA : ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 pJ → S'.sp = BitVec.ofNat 64 (t - 176) →
      S'.regs 0 = BitVec.ofNat 64 zA → S'.regs 1 = BitVec.ofNat 64 zA → S'.regs 2 = BitVec.ofNat 64 yA →
      S'.regs 4 = BitVec.ofNat 64 yA →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = BitVec.ofNat 64 (t - 184) → S'.regs 30 = BitVec.ofNat 64 ret → S'.mem = M' →
      MemFrame M M' [(t - 184, t - 168), (t + 8, t + 16)] → M'.regions = M.regions →
      M'.readLE (t - 184) 8 = r29.toNat → M'.readLE (t - 176) 8 = ret → M'.readLE (t + 8) 8 = zA →
      Reaches ((LibMod.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibMod.program.link impl).withExit ret0) S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have hzp : zp < 2 ^ 64 := hz8 ▸ Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := hz24 ▸ Memory.readLE_lt _ _ _
  have hyp : yp < 2 ^ 64 := hy8 ▸ Memory.readLE_lt _ _ _
  have hyc : yc < 2 ^ 64 := hy24 ▸ Memory.readLE_lt _ _ _
  have es0 : BitVec.ofNat 64 t - 48#64 = BitVec.ofNat 64 (t - 48) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es1 : BitVec.ofNat 64 t - 176#64 = BitVec.ofNat 64 (t - 176) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 176) - 8#64 = BitVec.ofNat 64 (t - 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hzy' : BitVec.ofNat 64 zA ≠ BitVec.ofNat 64 yA := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hr29 : r29.toNat < 2 ^ 64 := r29.isLt
  subst hz8 hz24 hy8 hy24
  janus_run [es0, es1, es2, hzy'] until [pJ, 0x1b0f7c]
  all_goals first
    | (exfalso; (try simp only [lastA] at *); omega)
    | skip
  all_goals
    refine KA _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
    case mf =>
      dsimp only
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (t - 184, t - 168)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (t + 8, t + 16)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals first | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done) | skip
    all_goals first | omega | skip

end FvModexp.Arm64.IMod
