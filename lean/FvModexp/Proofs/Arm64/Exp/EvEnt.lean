import FvModexp.Proofs.Arm64.Exp.EvTz
import FvModexp.Proofs.Arm64.Exp.EvPre
import FvModexp.Proofs.Arm64.Nat.StackNatDefs
import FvModexp.Proofs.Common.BitLemmas
import FvModexp.Proofs.Common.TruncMath

set_option autoImplicit false

/-!
# `nat.expNNEven` (arm64): the entry segments (agent infra)

* `entA`: `fnE` → the `tz` loop head `tzH` (guard, frame `sp = SP - 336`, `STP (R29, R30)`, `320 := 0`, argument
  spills `344..440` (not `368`/`432`), defer flag / result slots zeroed, `CBZ ml` not taken, `R1 := 0`);
* `entB`: `enS` (`R1 = n`) → the entry of `(*stack).nat` (`stk.nat(n/64 + 1)`, return `nat1R`): `368 := st`,
  `432 := ml`, `184 := n`, `224 := ml - n/64`, the defer record `296 = deferwrap1`, `304 = st`, `312 = len₀`,
  `320 = sp + 296`, flag `127 := 1`;
* `entS` = `entA` ∘ `tzLoop` ∘ `entB` (memory abstract: `M` the entry memory).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpEven

/-- the frame writes of the function (`[sp - 8, sp + 448)` without the caller's FP/LR) -/
@[reducible] def FW (sp : Nat) : List (Nat × Nat) := [(sp - 8, sp + 328), (sp + 344, sp + 448)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`fnE` → `tzH`** -/
theorem entA {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop)
    (sp g zp zl zc st xp xl xc yp yl yc mp ml mc ret : Nat) (r29 : BitVec 64) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 448 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 8) 456 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 128)
    (hml : 0 < ml) (hml' : ml < 2 ^ 64) (hret48 : ret < 2 ^ 48)
    (hzp : zp < 2 ^ 64) (hzl : zl < 2 ^ 64) (hzc : zc < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxl : xl < 2 ^ 64)
    (hxc : xc < 2 ^ 64) (hyp : yp < 2 ^ 64) (hyl : yl < 2 ^ 64) (hyc : yc < 2 ^ 64) (hmp : mp < 2 ^ 64)
    (hmc : mc < 2 ^ 64) (hst : st < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 fnE) (hsp : S.sp = BitVec.ofNat 64 (sp + 336))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 yp) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc) (h10 : S.regs 10 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 ml) (h12 : S.regs 12 = BitVec.ofNat 64 mc)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29)
    (h30 : S.regs 30 = BitVec.ofNat 64 ret) (hmem : S.mem = M)
    (KT : ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 tzH → S'.sp = BitVec.ofNat 64 sp → S'.regs 1 = 0#64 →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 10 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 ml →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' (FW sp) → M'.regions = M.regions →
      M'.readLE (sp - 8) 8 = r29.toNat → M'.readLE sp 8 = ret →
      M'.readLE (sp + 344) 8 = zp → M'.readLE (sp + 360) 8 = zc → M'.readLE (sp + 376) 8 = xp →
      M'.readLE (sp + 384) 8 = xl → M'.readLE (sp + 392) 8 = xc → M'.readLE (sp + 400) 8 = yp →
      M'.readLE (sp + 408) 8 = yl → M'.readLE (sp + 416) 8 = yc → M'.readLE (sp + 424) 8 = mp →
      M'.readLE (sp + 440) 8 = mc →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at KT
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (sp + 336) - 336#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs8 : sp - 8 + 8 = sp := by omega
  have es2 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hm0 : BitVec.ofNat 64 ml ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus_run [es1, es2, hm0] until [tzH]
  refine KT _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp + 328)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 344, sp + 448)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals simp (disch := omega) only [hs8, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip

/-- `entB`'s writes -/
@[reducible] def FB (sp : Nat) : List (Nat × Nat) := [(sp + 127, sp + 328), (sp + 368, sp + 376), (sp + 432, sp + 440)]

theorem a1_bv {n : Nat} (hn : n < 2 ^ 20) :
    (BitVec.ofNat 64 n + 64#64).rotateRight 6 &&& 18446744073709551615#64 &&& 288230376151711743#64 =
      BitVec.ofNat 64 (a1 n) := by
  rw [TruncMath.rot6]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, a1]
  omega

theorem a2_nat {n ml : Nat} (hn : n < 2 ^ 20) (hnm : n / 64 ≤ ml) (hml : ml < 2 ^ 20) :
    (18446744073709551616 -
          ((BitVec.ofNat 64 n +
                  ((if (BitVec.ofNat 64 n).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&&
                        18446744073709551614#64 |||
                      (BitVec.ofNat 64 n).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>>
                    58).sshiftRight 6).toNat + ml) % 18446744073709551616 = a2 ml n := by
  have h63 : (BitVec.ofNat 64 n).toNat < 2 ^ 63 := by rw [BitVec.toNat_ofNat]; omega
  rw [asr63_small _ h63, show (0#64 : BitVec 64) >>> 58 = 0#64 from rfl, BitVec.add_zero,
    sshiftRight_small _ h63, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [a2]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`enS` → `(*stack).nat`'s entry** (`R0 = st`, `R1 = n/64 + 1`, `R30 = nat1R`) -/
theorem entB {impl : List Segment} (ret0 : BitVec 64) (Q : State → Prop)
    (sp g st ml n len0 : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 448 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 456 true = true)
    (hst1 : M.accessible st 24 false = true) (hst2 : st + 24 ≤ 2 ^ 48) (hstw : st + 24 ≤ sp - 8 ∨ sp + 448 ≤ st)
    (hl0 : M.readLE (st + 8) 8 = len0) (hn : n < 2 ^ 20) (hml : ml < 2 ^ 20) (hnm : n / 64 < ml)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 enS) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h1 : S.regs 1 = BitVec.ofNat 64 n) (h3 : S.regs 3 = BitVec.ofNat 64 st) (h11 : S.regs 11 = BitVec.ofNat 64 ml)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = BitVec.ofNat 64 (sp - 8)) (hmem : S.mem = M)
    (KN : ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn) → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 1 = BitVec.ofNat 64 (a1 n) → S'.regs 30 = BitVec.ofNat 64 nat1R →
      S'.regs 18 = S.regs 18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = BitVec.ofNat 64 (sp - 8) →
      S'.mem = M' → MemFrame M M' (FB sp) → M'.regions = M.regions →
      M'.readLE (sp + 368) 8 = st → M'.readLE (sp + 432) 8 = ml → M'.readLE (sp + 184) 8 = n →
      M'.readLE (sp + 224) 8 = a2 ml n → M'.readLE (sp + 296) 8 = dwE → M'.readLE (sp + 304) 8 = st →
      M'.readLE (sp + 312) 8 = len0 → M'.readLE (sp + 320) 8 = sp + 296 →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  generalize e18 : S.regs 18 = x18 at KN
  have hl0' : M.readLE (st + 8) 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  janus_run [hl0] until [1784176]
  refine KN _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 127, sp + 328)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 368, sp + 376)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 432, sp + 440)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; exact a1_bv hn
  · exact a2_nat hn (by omega) hml

end FvModexp.Arm64.ExpEven
