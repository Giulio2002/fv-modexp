import FvModexp.Proofs.Arm64.Nat.DivLargeCall

/-!
# `divLarge` (arm64): `shift = 0` (natdiv.go:609-610), from `joinU` to `copy(v, vIn)`'s `memmove`

`CLZ` of `vIn[n-1]` (slot `SP - 168`) → `SP - 120`; `CBNZ` (not taken); `min(len v, len vIn) = n`; `CMP vIn, v; BEQ`
(not taken: `v` is the scratch at `t`, apart from `vIn`); `memmove(t, vIn, 8n)` (`fn + 0x194`), return `fn + 0x198`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem cpA (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibDivL.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (hgrd : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8)
    (hclz : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0) (Q : State → Prop)
    (k : ∀ (m : Memory) (T : State), T.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x198) →
      T.sp = s.sp - 304#64 → T.regs 28 = s.regs 28 → T.regs 29 = s.sp - 312#64 → T.regs 18 = s.regs 18 → T.mem = m → m.regions = s.mem.regions →
      MemFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m (R.rt ++ [(s.sp.toNat - 304 - 4096, s.sp.toNat - 304 - 8),
        (s.sp.toNat - 304 + 8, s.sp.toNat - 304 + 8 + 8 * 3)] ++ [(t, t + 8 * vl)]) →
      LiveFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m Lk [(t, t + 8 * vl)] →
      R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m) →
      Mem.Copied (S.mem.writeLE (s.sp.toNat - 120) 8 0) m t vp (8 * vl) →
      ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hil9 := hl.il9
  have hM := hS.mem
  have m1 := hM.vtop; have m2 := hM.s12; have m3 := hM.s11
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hr0 := hS.r0; have hr1 := hS.r1; have hr2 := hS.r2
  have hvt := Memory.readLE_lt s.mem (vp + 8 * (vl - 1)) 8
  have hc0 : clzNat 64 (BitVec.ofNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8)).toNat = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvt]; exact hclz
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hSacc : ∀ a n v, S.mem.accessible a n v = s.mem.accessible a n v := fun a n v => hM.fr.accessible a n v
  have hwacc : S.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hSacc]; exact hw
  have htv : t ≠ vp := by have := hl.tv; omega
  have ht48 := hl.t48; have hv48 := hl.v48
  have hl3 := lsl3_ofNat vl (by omega)
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hga := hE.pre.ce.2.2.2.2.1
  unfold Apart at hga
  have hU := hS.ua
  have e304 : (s.sp - 304#64).toNat = s.sp.toNat - 304 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hsv := hE.pre.sv
  have hvil := hl.vil
  have hvh : Held R Lk t (8 * vl) := hS.ext2.held hl.theld
  janus_run [m1, m2, m3, hc0, hl3] until [cA "runtime.memmove"]
  refine ReachesRet.call_regions (hmv Lk bk) rfl (mv_pre (dst := t) (src := vp) (n := 8 * vl) hE hS.ext2 _ rfl ?q28 ?qg ?qa
    ?l1 ?l2 ?qi ?q0 ?q1 ?q2 (hsv.2.1 _ _ _ (by omega)) (by omega) ?dacc hvh (by have := hl.tw; omega) (by omega)
    ?sacc (by have := hl.vw; omega)) ?qk
  case q28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  case qg => rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hgrd
  case qa => intro a n w; simp only [Memory.accessible_writeLE]; exact hSacc a n w
  case l1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
  case l2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
  case qi => exact inv_store_out hM.inv (hout.of_sub (by omega) (by omega))
  case q0 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hr0, BitVec.toNat_ofNat]; omega
  case q1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]; omega
  case q2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]; omega
  case dacc => simp only [Memory.accessible_writeLE]; rw [hSacc]; exact hE.scr.acc
  case sacc => simp only [Memory.accessible_writeLE]; rw [hSacc]; exact hE.pre.vo.2.1
  case qk =>
    intro T hT ⟨junk, f, v, m, ex, ep, hs, hMF, hLF, hinv, hcp⟩ hrg
    subst hs
    simp only [calleeStack, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hr0, BitVec.toNat_ofNat, e304, h28] at hMF hLF hcp hinv
    rw [Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show vp < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 8 * vl < 2 ^ 64 by omega)] at hcp
    rw [Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * vl < 2 ^ 64 by omega)] at hMF hLF
    exact k m _ (by rw [hT]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl) rfl
      (by simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28, true_or, or_true, if_true])
      (by simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29, true_or, or_true, if_true])
      (by simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18, true_or, or_true, if_true]) rfl
      (by simp only [retStateX, Memory.regions_writeLE] at hrg ⊢; rw [hrg]; exact hS.reg) hMF hLF hinv hcp

end FvModexp.Arm64.DivLarge
