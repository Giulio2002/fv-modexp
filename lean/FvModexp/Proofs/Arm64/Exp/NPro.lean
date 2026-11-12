import FvModexp.Proofs.Arm64.Exp.LibN
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.expNN` (arm64): prologue and alias test (fn+0x0 .. `J1` = fn+0x8c)

Stack check (falls through), frame 256 (`STP (R29, R30), -8(R20)` at `SP - 264`, `SP - 256`), the spills of `z`, `x`,
`y`, `m` (`SP + 8`, `+ 40`, `+ 64`, `+ 88`), the zeroing of the defer slots (`240`, byte `127`, result `176..200`), then
`alias(z, x) || alias(z, y)` (nat.go:228: `cap > 0` on both and the same last element of the capacity) → `z = nil`.
Continuation form, one continuation per outcome.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

/-- the last-element address `p + 8 (c - 1)` (mod `2^64`) of a nat of capacity `c`, as the code computes it -/
@[reducible] def lastA (p c : Nat) : Nat := (p + 8 * (c - 1)) % 2 ^ 64

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem pro (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0)
    (Q : Outcome → Prop) (sp g ret zp zc xp xc yp yc : Nat) (r29 : BitVec 64) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48)
    (hacc : M.accessible (sp + 1048) 360 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 1184)
    (hret48 : ret < 2 ^ 48) (hzp : zp < 2 ^ 64) (hzc : zc < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxc : xc < 2 ^ 64)
    (hyp : yp < 2 ^ 64) (hyc : yc < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1786544) (hsp : S.sp = BitVec.ofNat 64 (sp + 1312))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h6 : S.regs 6 = BitVec.ofNat 64 xc)
    (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h9 : S.regs 9 = BitVec.ofNat 64 yc)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29)
    (h30 : S.regs 30 = BitVec.ofNat 64 ret) (hmem : S.mem = M)
    (Kk : (zc = 0 ∨ ((xc = 0 ∨ lastA xp xc ≠ lastA zp zc) ∧ (yc = 0 ∨ lastA yp yc ≠ lastA zp zc))) →
      ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 1786684 → S'.sp = BitVec.ofNat 64 (sp + 1056) →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 3 →
      S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 →
      S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 → S'.regs 11 = S.regs 11 →
      S'.regs 12 = S.regs 12 → S'.regs 13 = S.regs 13 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.mem = M' → MemFrame M M' [(sp + 1048, sp + 1304), (sp + 1320, sp + 1408)] → M'.regions = M.regions →
      M'.readLE (sp + 1048) 8 = r29.toNat → M'.readLE (sp + 1056) 8 = ret →
      M'.readLE (sp + 1296) 8 = 0 → M'.readLE (sp + 1183) 1 = 0 →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q)
    (K0 : zc ≠ 0 → ((xc ≠ 0 ∧ lastA xp xc = lastA zp zc) ∨ (yc ≠ 0 ∧ lastA yp yc = lastA zp zc)) →
      ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 1786684 → S'.sp = BitVec.ofNat 64 (sp + 1056) →
      S'.regs 0 = 0#64 → S'.regs 1 = 0#64 → S'.regs 2 = 0#64 → S'.regs 3 = S.regs 3 →
      S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 →
      S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 → S'.regs 10 = S.regs 10 → S'.regs 11 = S.regs 11 →
      S'.regs 12 = S.regs 12 → S'.regs 13 = S.regs 13 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.mem = M' → MemFrame M M' [(sp + 1048, sp + 1304), (sp + 1320, sp + 1408)] → M'.regions = M.regions →
      M'.readLE (sp + 1048) 8 = r29.toNat → M'.readLE (sp + 1056) 8 = ret →
      M'.readLE (sp + 1296) 8 = 0 → M'.readLE (sp + 1183) 1 = 0 →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (sp + 1312) - 256#64 = BitVec.ofNat 64 (sp + 1056) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es0 : BitVec.ofNat 64 (sp + 1312) - 128#64 = BitVec.ofNat 64 (sp + 1184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (sp + 1056) - 8#64 = BitVec.ofNat 64 (sp + 1048) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hr29 : r29.toNat < 2 ^ 64 := r29.isLt
  janus_run [es0, es1, es2] until [1786684]
  all_goals first
    | (refine Kk (by (try simp only [lastA] at *); omega) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?r1 ?r2
          ?r3 ?r4
       case mf =>
         dsimp only
         repeat (first
           | refine MemFrame.writeLE ?_ _ (r := (sp + 1048, sp + 1304)) (by simp) (by simp only; omega) (by simp only; omega)
           | refine MemFrame.writeLE ?_ _ (r := (sp + 1320, sp + 1408)) (by simp) (by simp only; omega) (by simp only; omega))
         exact MemFrame.refl _ _
       all_goals first | (janus_simp; done) | skip
       all_goals first | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
         BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done) | skip
       all_goals first | omega | skip)
    | (refine K0 (by (try simp only [lastA] at *); omega) (by (try simp only [lastA] at *); omega) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?r1 ?r2 ?r3 ?r4
       case mf =>
         dsimp only
         repeat (first
           | refine MemFrame.writeLE ?_ _ (r := (sp + 1048, sp + 1304)) (by simp) (by simp only; omega) (by simp only; omega)
           | refine MemFrame.writeLE ?_ _ (r := (sp + 1320, sp + 1408)) (by simp) (by simp only; omega) (by simp only; omega))
         exact MemFrame.refl _ _
       all_goals first | (janus_simp; done) | skip
       all_goals first | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
         BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done) | skip
       all_goals first | omega | skip)

end FvModexp.Arm64.ExpN
