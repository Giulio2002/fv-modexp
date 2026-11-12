import FvModexp.Proofs.Arm64.Int.ModA

/-!
# `(*Int).Mod` (arm64), segment A2: the join → `nat.div`'s entry (int.go:330-331 → int.go:299-300)

From `pJ` (X0 = X1 = z, X2 = y, X4 = y0 = y): `y0` spilled at `SP' + 88`, `var q Int` zeroed at `SP' + 104 .. + 136`,
`CALL q.QuoRem(z, y, z)` (X0 = `SP' + 104`, X3 = z, X30 = `raQ`). `QuoRem` (frame 128, FP at `SP'' - 8`): stack check
(falls through), the spills of `q, x, y, r` (`SP'' + 136 .. + 160`), `q.abs` (= 0, just zeroed), `r.abs = x.abs = z.abs`,
`y.abs`, and `CALL q.abs.div(nil, r.abs, x.abs, y.abs)` (X30 = `raD`). Stops at `nat.div`'s entry.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IMod

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runA2 (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibMod.program.link impl) ret0)
    (Q : Outcome → Prop)
    (t g zA yA zp zl zc yp yl yc : Nat) (M : Memory)
    (hal : t % 16 = 0) (ht1 : 336 ≤ t) (ht2 : t + 32 ≤ 2 ^ 48)
    (hacc : M.accessible (t - 312) 272 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + 320 < t)
    (hgS : g + 24 ≤ t - 312 ∨ t + 16 ≤ g + 16)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : M.accessible zA 32 false = true) (hzS : zA + 32 ≤ t - 312 ∨ t + 16 ≤ zA)
    (hyA : yA + 32 ≤ 2 ^ 48) (hya : M.accessible yA 32 false = true) (hyS : yA + 32 ≤ t - 312 ∨ t + 16 ≤ yA)
    (hz8 : M.readLE (zA + 8) 8 = zp) (hz16 : M.readLE (zA + 16) 8 = zl) (hz24 : M.readLE (zA + 24) 8 = zc)
    (hy8 : M.readLE (yA + 8) 8 = yp) (hy16 : M.readLE (yA + 16) 8 = yl) (hy24 : M.readLE (yA + 24) 8 = yc)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 pJ) (hsp : S.sp = BitVec.ofNat 64 (t - 176))
    (h0 : S.regs 0 = BitVec.ofNat 64 zA) (h1 : S.regs 1 = BitVec.ofNat 64 zA) (h2 : S.regs 2 = BitVec.ofNat 64 yA)
    (h4 : S.regs 4 = BitVec.ofNat 64 yA) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (h29 : S.regs 29 = BitVec.ofNat 64 (t - 184)) (hmem : S.mem = M)
    (KA : ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 fnD → S'.sp = BitVec.ofNat 64 (t - 304) →
      S'.regs 0 = 0#64 → S'.regs 1 = 0#64 → S'.regs 2 = 0#64 → S'.regs 3 = 0#64 →
      S'.regs 4 = BitVec.ofNat 64 zp → S'.regs 5 = BitVec.ofNat 64 zl → S'.regs 6 = BitVec.ofNat 64 zc →
      S'.regs 7 = BitVec.ofNat 64 zp → S'.regs 8 = BitVec.ofNat 64 zl → S'.regs 9 = BitVec.ofNat 64 zc →
      S'.regs 10 = BitVec.ofNat 64 yp → S'.regs 11 = BitVec.ofNat 64 yl → S'.regs 12 = BitVec.ofNat 64 yc →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = BitVec.ofNat 64 (t - 312) → S'.regs 30 = BitVec.ofNat 64 raD → S'.mem = M' →
      MemFrame M M' [(t - 312, t - 296), (t - 168, t - 136), (t - 88, t - 40)] → M'.regions = M.regions →
      M'.readLE (t - 312) 8 = t - 184 → M'.readLE (t - 304) 8 = raQ →
      M'.readLE (t - 168) 8 = t - 72 → M'.readLE (t - 160) 8 = zA → M'.readLE (t - 152) 8 = yA →
      M'.readLE (t - 144) 8 = zA → M'.readLE (t - 64) 8 = 0 →
      Reaches ((LibMod.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibMod.program.link impl).withExit ret0) S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have hzp : zp < 2 ^ 64 := hz8 ▸ Memory.readLE_lt _ _ _
  have hzl : zl < 2 ^ 64 := hz16 ▸ Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := hz24 ▸ Memory.readLE_lt _ _ _
  have hyp : yp < 2 ^ 64 := hy8 ▸ Memory.readLE_lt _ _ _
  have hyl : yl < 2 ^ 64 := hy16 ▸ Memory.readLE_lt _ _ _
  have hyc : yc < 2 ^ 64 := hy24 ▸ Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (t - 176) - 128#64 = BitVec.ofNat 64 (t - 304) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 304) - 8#64 = BitVec.ofNat 64 (t - 312) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 (t - 176) + 104#64 = BitVec.ofNat 64 (t - 72) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  subst hz8 hz16 hz24 hy8 hy16 hy24
  janus_run [es1, es2, es3] until [fnD]
  refine KA _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    dsimp only
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (t - 312, t - 296)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (t - 168, t - 136)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (t - 88, t - 40)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals first | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done) | skip
  all_goals first | omega | skip

end FvModexp.Arm64.IMod
