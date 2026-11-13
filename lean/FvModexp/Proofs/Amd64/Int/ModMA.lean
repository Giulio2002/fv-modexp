import FvModexp.Proofs.Amd64.Int.QRDefs

set_option autoImplicit false

/-!
# `(*Int).Mod` (amd64), segments A (entry → `QuoRem`'s entry) and B (`QuoRem`'s return → `RET`) (int.go:325-339)

`z.Mod(z, y)` (`RSP = t`, `RAX = RBX = z`, `RCX = y`): stack check (falls through), `PUSH RBP`, frame `0x98`
(`RSP = t - 160`), the spill of `z` (`t + 8`); `z ≠ y` and the alias test (int.go:327, `alias(z, y)`: last words of the
two arrays) false, so `y` itself is the divisor (`[t - 88] = y`); `var q Int` zeroed at `t - 72` (`q.neg` byte,
`q.abs` = 0, 0, 0 via `X15 = 0`); `CALL QuoRem` with `RAX = &q`, `RBX = z`, `RCX = y`, `RDI = z` (return `raM`,
`RSP = t - 168`). Segment B: `z.neg` is `0`, so `Mod` returns `z` (the `Sub`/`Add` correction is dead).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IMod

/-- `(*Int).Mod`'s entry -/
@[reducible] def fnM : Nat := 0x5e2d60

/-- the return address of `Mod`'s `QuoRem` call -/
@[reducible] def raM : Nat := 0x5e2f77

theorem fnM_eq : segAddr Extracted.program (RunIface.P ++ "(*Int).Mod") = fnM := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **segment A**: `Mod`'s entry → `QuoRem`'s entry, on the non-alias path -/
theorem runMA (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibMod.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop)
    (t g bp zA yA zp zc yp yc : Nat) (M : Janus.Arm64.Memory) (hbp : bp < 2 ^ 64)
    (ht1 : 176 ≤ t) (ht2 : t + 16 ≤ 2 ^ 48)
    (hacc : M.accessible (t - 168) 184 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + 32 < t)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : M.accessible zA 32 false = true)
    (hyA : yA + 32 ≤ 2 ^ 48) (hya : M.accessible yA 32 false = true) (hzy : zA ≠ yA)
    (hzS : zA + 32 ≤ t - 168 ∨ t + 16 ≤ zA) (hyS : yA + 32 ≤ t - 168 ∨ t + 16 ≤ yA)
    (hz8 : M.readLE (zA + 8) 8 = zp) (hz24 : M.readLE (zA + 24) 8 = zc)
    (hy8 : M.readLE (yA + 8) 8 = yp) (hy24 : M.readLE (yA + 24) 8 = yc)
    (hali : zc = 0 ∨ yc = 0 ∨ (zp + 8 * zc) % 2 ^ 64 ≠ (yp + 8 * yc) % 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 fnM) (hsp : S.regs 4 = BitVec.ofNat 64 t)
    (h0 : S.regs 0 = BitVec.ofNat 64 zA) (h3 : S.regs 3 = BitVec.ofNat 64 zA) (h1 : S.regs 1 = BitVec.ofNat 64 yA)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (h5 : S.regs 5 = BitVec.ofNat 64 bp) (hx15 : S.xmm 15 = 0)
    (hmem : S.mem = M)
    (KA : ∀ (S' : State) (M' : Janus.Arm64.Memory),
      S'.rip = BitVec.ofNat 64 fnQ → S'.regs 4 = BitVec.ofNat 64 (t - 168) →
      S'.regs 0 = BitVec.ofNat 64 (t - 72) → S'.regs 3 = BitVec.ofNat 64 zA → S'.regs 1 = BitVec.ofNat 64 yA →
      S'.regs 7 = BitVec.ofNat 64 zA →
      S'.regs 14 = S.regs 14 → S'.regs 5 = BitVec.ofNat 64 (t - 8) → S'.fsBase = S.fsBase → S'.df = S.df →
      S'.xmm 15 = S.xmm 15 → S'.mem = M' →
      MemFrame M M' [(t - 168, t - 160), (t - 88, t - 40), (t - 8, t), (t + 8, t + 16)] → M'.regions = M.regions →
      M'.readLE (t - 168) 8 = raM →
      M'.readLE (t - 72 + 8) 8 = 0 → M'.readLE (t - 72 + 16) 8 = 0 → M'.readLE (t - 72 + 24) 8 = 0 →
      M'.readLE (t - 8) 8 = bp → M'.readLE (t + 8) 8 = zA →
      Reaches ((LibMod.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibMod.program.link impl).withExit ret0) S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hzp : zp < 2 ^ 64 := hz8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := hz24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyp : yp < 2 ^ 64 := hy8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyc : yc < 2 ^ 64 := hy24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 t - 8#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) - 152#64 = BitVec.ofNat 64 (t - 160) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 (t - 160) - 8#64 = BitVec.ofNat 64 (t - 168) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es4 : BitVec.ofNat 64 (t - 160) + 88#64 = BitVec.ofNat 64 (t - 72) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  subst hz8 hz24 hy8 hy24 hmem
  janus64_run [es1, es2, es3, es4, hx15] until [fnQ]
  all_goals
    refine KA _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl (by
      dsimp only
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (t - 168, t - 160)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (t - 88, t - 40)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (t - 8, t)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (t + 8, t + 16)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus64_simp; done) | skip
  all_goals first | omega | (dsimp only; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **segment B**: `QuoRem`'s return (`raM`, `RSP = t - 160`) → `RET`: `z.neg = 0` (`cmpb (z), 0`), so no correction -/
theorem runMB (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibMod.program.link impl) ret0)
    (F : State → Prop) (t bp zA : Nat)
    (ht1 : 176 ≤ t) (ht2 : t + 16 ≤ 2 ^ 48)
    (hzA : zA + 1 ≤ 2 ^ 48)
    (S : State) (hacc : S.mem.accessible (t - 8) 24 false = true) (hza : S.mem.accessible zA 1 false = true)
    (hpc : S.rip = BitVec.ofNat 64 raM) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 160))
    (s8 : S.mem.readLE (t + 8) 8 = zA) (sbp : S.mem.readLE (t - 8) 8 = bp) (sra : S.mem.readLE t 8 = ret0)
    (hng : S.mem.readLE zA 1 = 0)
    (KB : ∀ (s4 : State), s4.mem = S.mem → s4.regs 4 = BitVec.ofNat 64 (t + 8) → s4.regs 0 = BitVec.ofNat 64 zA →
      s4.regs 5 = BitVec.ofNat 64 bp → s4.regs 14 = S.regs 14 → s4.fsBase = S.fsBase → s4.df = S.df →
      s4.xmm 15 = S.xmm 15 → F s4) :
    Reaches ((LibMod.program.link impl).withExit ret0) S (IsReturn F) := by
  have es1 : BitVec.ofNat 64 (t - 160) + 152#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) + 8#64 = BitVec.ofNat 64 t := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 t + 8#64 = BitVec.ofNat 64 (t + 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have s8' : S.mem.readLE (t - 160 + 168) 8 = zA := by rw [show t - 160 + 168 = t + 8 by omega]; exact s8
  have hzl : zA < 2 ^ 64 := by omega
  have hbp : bp < 2 ^ 64 := sbp ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hacc8 : S.mem.accessible (t - 160 + 168) 8 false = true := by
    rw [show t - 160 + 168 = t + 8 by omega]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  janus64_run [es1, es2, es3, s8', sbp, sra, hng, hacc8]
  all_goals first
    | exact KB _ rfl (by simp only [setRegF_apply]; rfl) (by simp only [setRegF_apply]; rfl)
        (by simp only [setRegF_apply]; rfl) (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]) rfl rfl rfl
    | skip

end FvModexp.Amd64.IMod
