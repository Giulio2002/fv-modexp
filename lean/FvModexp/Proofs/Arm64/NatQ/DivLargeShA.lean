import FvModexp.Proofs.Arm64.NatQ.DivLargeShB

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivLargeShA.lean, TIGHT COSTS, asm s38)
# `divLarge` (arm64): `shift ≠ 0` (natdiv.go:614): from `joinU` to `lshVU(v, vIn, shift)` (`fn + 0x230`) → `shB`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivLarge
open FvModexp.Arm64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- at `lshVU.abi0`'s entry (first call) -/
theorem shA2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (sh : Nat) (hsh : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = sh) (hsh0 : sh ≠ 0)
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program lshVUfn)) (hsp : X.sp = s.sp - 304#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 312#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x234))
    (hA1 : MemFrame S.mem X.mem [(s.sp.toNat - 296, s.sp.toNat - 232), (s.sp.toNat - 120, s.sp.toNat - 112)])
    (hA1sh : X.mem.readLE (s.sp.toNat - 120) 8 = sh)
    (hz : X.mem.readLE (s.sp.toNat - 296) 8 = t) (hn : X.mem.readLE (s.sp.toNat - 288) 8 = vl)
    (hx : X.mem.readLE (s.sp.toNat - 272) 8 = vp) (hs : X.mem.readLE (s.sp.toNat - 248) 8 = sh)
    (hXreg : X.mem.regions = s.mem.regions) (Q : State → Prop)
    (k : ∀ S', AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh S' →
      ReachesRet (LibDivL.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) X Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have htv := hl.tv
  have hspn : X.sp.toNat = s.sp.toNat - 304 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hXacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hA1.accessible, hS.mem.fr.accessible]
  have hshb := (AsmDiv.clz_norm64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) (by
      rcases hE.pre.vn with h | h
      · have := hl.v2; omega
      · exact h) (Memory.readLE_lt _ _ _)).1
  rw [hsh] at hshb
  have hgt := (wsL_parts (g_wsL hE)).1
  have hpre := (lsh_pre (bk := bk) (Lk := Lk) hE X hspn h28 (z := t) (x := vp) (n := vl) (sh := sh)
    (by rw [hspn, show s.sp.toNat - 304 + 8 = s.sp.toNat - 296 by omega]; exact hz)
    (by rw [hspn, show s.sp.toNat - 304 + 16 = s.sp.toNat - 288 by omega]; exact hn)
    (by rw [hspn, show s.sp.toNat - 304 + 32 = s.sp.toNat - 272 by omega]; exact hx)
    (by rw [hspn, show s.sp.toNat - 304 + 56 = s.sp.toNat - 248 by omega]; exact hs)
    (by rw [h30]; decide) (by rw [h30]; decide) hXacc
    (by rw [hXacc]; exact hE.scr.acc) (by rw [hXacc]; exact hE.pre.vo.2.1) (by omega) hshb
    (Or.inr (by unfold Apart; omega)) (Or.inr (by unfold Apart; omega)) hl.tw hl.vw
    (hS.ext2.held hl.theld) (by unfold Apart; omega)
    (RtInv.inv_frame' hA1 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
      rcases hr with rfl | rfl <;> left <;> exact hout.of_sub (by simp only; omega) (by simp only; omega))
      hS.mem.inv)).1
  refine ReachesRet.call_regions (lshvu impl hap R bk Lk) hpc hpre ?_
  intro T hT ⟨junk, f, v, fpsr, m3, hs4, hq, hinv3, _⟩ hrg
  subst hs4
  unfold LshVUSum.Q at hq
  rw [hspn, show s.sp.toNat - 304 + 8 = s.sp.toNat - 296 by omega, show s.sp.toNat - 304 + 16 = s.sp.toNat - 288 by omega,
    show s.sp.toNat - 304 + 32 = s.sp.toNat - 272 by omega, show s.sp.toNat - 304 + 56 = s.sp.toNat - 248 by omega,
    show s.sp.toNat - 304 + 64 = s.sp.toNat - 240 by omega, show s.sp.toNat - 304 + 72 = s.sp.toNat - 232 by omega,
    hz, hn, hx, hs] at hq
  obtain ⟨q1, -, q3⟩ := hq
  rw [h28] at hinv3
  exact shB impl hap R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C hE S hS sh hsh hsh0 X.mem m3
    hA1 hA1sh q3 q1 hinv3 _ (by rw [hT, h30]) (by simp only [retState0]; exact hsp)
    (by simp only [retState0, regs0_apply]; simp only [Nat.reduceEqDiff, or_false, false_or, if_true, h28])
    (by simp only [retState0, regs0_apply]; simp only [Nat.reduceEqDiff, or_false, false_or, if_true, h29])
    (by simp only [retState0, regs0_apply]; simp only [Nat.reduceEqDiff, or_false, false_or, if_true, h18]) rfl
    (by simp only [retState0] at hrg; rw [hrg]; exact hXreg) Q k

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the shift path from `joinU` -/
theorem shA (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (sh : Nat) (hsh : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = sh) (hsh0 : sh ≠ 0)
    (Q : State → Prop)
    (k : ∀ S', AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh S' →
      ReachesRet (LibDivL.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2; have hil9 := hl.il9; have hvil := hl.vil
  have hM := hS.mem
  have m1 := hM.vtop; have m2 := hM.s12; have m3 := hM.s11; have m4 := hM.s13
  have hpc := hS.pc; have hsp := hS.sp; have h28 := hS.r28; have h29 := hS.r29; have h18 := hS.r18
  have hr0 := hS.r0; have hr1 := hS.r1; have hr2 := hS.r2
  have hvt := Memory.readLE_lt s.mem (vp + 8 * (vl - 1)) 8
  have hshb := (AsmDiv.clz_norm64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) (by
      rcases hE.pre.vn with h | h
      · omega
      · exact h) hvt).1
  rw [hsh] at hshb
  have hc0 : clzNat 64 (BitVec.ofNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8)).toNat = sh := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvt]; exact hsh
  have hne : (BitVec.ofNat 64 sh = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : S.mem.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hM.fr.accessible]; exact hw
  have ht48 := hl.t48; have hv48 := hl.v48; have hvc := hE.pre.vo.1
  janus_run [m1, m2, m3, m4, hc0, hne] until [segAddr Extracted.program lshVUfn]
  rw [hsh]
  refine shA2 impl hap R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C hE S hS sh hsh hsh0 _ rfl rfl
    ?g28 ?g29 ?g18 rfl (by janus_frame) ?gsh ?gz ?gn ?gx ?gs ?greg Q k
  case greg => simp only [Memory.regions_writeLE]; exact hS.reg
  case g28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  case g29 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
  case g18 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
  all_goals
    simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Memory.readLE_writeLE_of_disjoint, Nat.reducePow]
    omega

end FvModexp.Arm64.Q.DivLarge
