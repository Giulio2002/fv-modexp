import FvModexp.Proofs.Arm64.Nat.DivLargeShC
import FvModexp.Proofs.Arm64.Nat.DivLargeShP

/-!
# `divLarge` (arm64): shift path after `lshVU(v, vIn, shift)` (`fn + 0x234`): bounds, ABI0 arguments,
`lshVU(u[:il], uIn, shift)` (`fn + 0x264`; in place when `P = uIn`) → `shC`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- at `lshVU.abi0`'s entry (second call) -/
theorem shB2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (sh : Nat) (hsh : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = sh) (hsh0 : sh ≠ 0)
    (A1 m3 : Memory)
    (hA1 : MemFrame S.mem A1 [(s.sp.toNat - 296, s.sp.toNat - 232), (s.sp.toNat - 120, s.sp.toNat - 112)])
    (hA1sh : A1.readLE (s.sp.toNat - 120) 8 = sh)
    (hQ1f : MemFrame A1 m3 [(t, t + 8 * vl), (s.sp.toNat - 240, s.sp.toNat - 232)])
    (hQ1v : natVal m3 t vl = natVal A1 vp vl * 2 ^ sh % 2 ^ (64 * vl))
    (hinv3 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m3))
    (X : State) (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program lshVUfn)) (hsp : X.sp = s.sp - 304#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 312#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x268))
    (hA2 : MemFrame m3 X.mem [(s.sp.toNat - 296, s.sp.toNat - 232)])
    (hz : X.mem.readLE (s.sp.toNat - 296) 8 = P) (hn : X.mem.readLE (s.sp.toNat - 288) 8 = il)
    (hx : X.mem.readLE (s.sp.toNat - 272) 8 = ip) (hs : X.mem.readLE (s.sp.toNat - 248) 8 = sh)
    (hXreg : X.mem.regions = s.mem.regions) (Q : State → Prop)
    (k : ∀ S', AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh S' →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) X Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9
  have hU := hS.ua
  have hcap := hU.cap; have hp48 := hU.p48; have hpw := hU.pw; have hpg := hU.pg
  unfold Apart at hpg
  have hspn : X.sp.toNat = s.sp.toNat - 304 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hF3 : MemFrame S.mem X.mem [(s.sp.toNat - 296, s.sp.toNat - 232), (s.sp.toNat - 120, s.sp.toNat - 112),
      (t, t + 8 * vl), (P, P + 8 * il)] := by
    refine (mfTrans (mfTrans hA1 hQ1f) hA2).mono fun a n ho => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  have hXacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hF3.accessible, hS.mem.fr.accessible]
  have hiw := hl.iw
  have hpi : ip ≤ P ∨ Apart P (8 * il) ip (8 * il) := by
    rcases hU.pi with h | h
    · left; omega
    · right; unfold Apart at h ⊢; omega
  have hpi' : P ≤ ip ∨ Apart P (8 * il) ip (8 * il) := by
    rcases hU.pi with h | h
    · left; omega
    · right; unfold Apart at h ⊢; omega
  have hshb := (AsmDiv.clz_norm64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) (by
      rcases hE.pre.vn with h | h
      · have := hl.v2; omega
      · exact h) (Memory.readLE_lt _ _ _)).1
  rw [hsh] at hshb
  have hpre := (lsh_pre (bk := bk) (Lk := Lk) hE X hspn h28 (z := P) (x := ip) (n := il) (sh := sh)
    (by rw [hspn, show s.sp.toNat - 304 + 8 = s.sp.toNat - 296 by omega]; exact hz)
    (by rw [hspn, show s.sp.toNat - 304 + 16 = s.sp.toNat - 288 by omega]; exact hn)
    (by rw [hspn, show s.sp.toNat - 304 + 32 = s.sp.toNat - 272 by omega]; exact hx)
    (by rw [hspn, show s.sp.toNat - 304 + 56 = s.sp.toNat - 248 by omega]; exact hs)
    (by rw [h30]; decide) (by rw [h30]; decide) hXacc
    (by rw [hXacc]; exact Memory.accessible_mono _ (by rw [← hS.mem.fr.accessible]; exact hU.pacc) (by omega) (by omega))
    (by rw [hXacc]; exact hE.pre.io.2.1) (by omega) hshb hpi hpi' (by omega) (by omega)
    (hU.pheld.sub (by omega) (by omega)) (by unfold Apart; omega)
    (RtInv.inv_frame' hA2 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; left
      exact (hE.pre.ce.2.2.2.1 : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt).of_sub (by simp only; omega)
        (by simp only; omega)) hinv3)).1
  refine ReachesRet.call_regions (lshvu impl hap R bk Lk) hpc hpre ?_
  intro T hT ⟨junk, f, v, fpsr, m4, hs4, hq, hinv4, _⟩ hrg
  subst hs4
  unfold LshVUSum.Q at hq
  rw [hspn, show s.sp.toNat - 304 + 8 = s.sp.toNat - 296 by omega, show s.sp.toNat - 304 + 16 = s.sp.toNat - 288 by omega,
    show s.sp.toNat - 304 + 32 = s.sp.toNat - 272 by omega, show s.sp.toNat - 304 + 56 = s.sp.toNat - 248 by omega,
    show s.sp.toNat - 304 + 64 = s.sp.toNat - 240 by omega, show s.sp.toNat - 304 + 72 = s.sp.toNat - 232 by omega,
    hz, hn, hx, hs] at hq
  obtain ⟨q1, q2, q3⟩ := hq
  rw [h28] at hinv4
  exact shC impl R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C hE S hS sh hsh A1 m3 X.mem m4 hA1
    hA1sh hQ1f hQ1v hA2 q3 q1 q2 hinv4 _ (by rw [hT, h30]) (by simp only [retState0]; exact hsp)
    (by simp only [retState0, regs0_apply]; simp only [Nat.reduceEqDiff, or_false, false_or, if_true, h28])
    (by simp only [retState0, regs0_apply]; simp only [Nat.reduceEqDiff, or_false, false_or, if_true, h29])
    (by simp only [retState0, regs0_apply]; simp only [Nat.reduceEqDiff, or_false, false_or, if_true, h18]) rfl
    (by simp only [retState0] at hrg; rw [hrg]; exact hXreg) Q k

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after the first `lshVU` (`fn + 0x234`) → the second call's entry → `shB2` -/
theorem shB (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (sh : Nat) (hsh : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = sh) (hsh0 : sh ≠ 0)
    (A1 m3 : Memory)
    (hA1 : MemFrame S.mem A1 [(s.sp.toNat - 296, s.sp.toNat - 232), (s.sp.toNat - 120, s.sp.toNat - 112)])
    (hA1sh : A1.readLE (s.sp.toNat - 120) 8 = sh)
    (hQ1f : MemFrame A1 m3 [(t, t + 8 * vl), (s.sp.toNat - 240, s.sp.toNat - 232)])
    (hQ1v : natVal m3 t vl = natVal A1 vp vl * 2 ^ sh % 2 ^ (64 * vl))
    (hinv3 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m3))
    (T : State) (hpc : T.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x234)) (hsp : T.sp = s.sp - 304#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 312#64) (h18 : T.regs 18 = s.regs 18) (hm : T.mem = m3)
    (hreg3 : m3.regions = s.mem.regions) (Q : State → Prop)
    (k : ∀ S', AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C sh S' →
      ReachesRet (LibDiv.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) T Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9
  have hU := hS.ua
  have hcap := hU.cap; have hpw := hU.pw; have hc40 := hU.c40
  have hF : MemFrame S.mem m3 [(s.sp.toNat - 296, s.sp.toNat - 232), (s.sp.toNat - 120, s.sp.toNat - 112),
      (t, t + 8 * vl), (P, P + 8 * il)] := by
    refine (mfTrans hA1 hQ1f).mono fun a n ho => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  obtain ⟨-, -, -, r4, -, r6, -, r8, r9, r10, -, -⟩ := sh_rd hE hS hF
  have r11 : m3.readLE (s.sp.toNat - 120) 8 = sh := by
    rw [hQ1f.readLE _ _ (by have := hl.tw; simp only [outside_cons, outside_nil, and_true]; omega)]; exact hA1sh
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : m3.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by
    rw [hF.accessible, hS.mem.fr.accessible]; exact hw
  have hp48 := hU.p48; have hi48 := hl.i48
  have hshb := (AsmDiv.clz_norm64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) (by
      rcases hE.pre.vn with h | h
      · have := hl.v2; omega
      · exact h) (Memory.readLE_lt _ _ _)).1
  rw [hsh] at hshb
  janus_run [hm, r4, r6, r8, r9, r10, r11] until [segAddr Extracted.program lshVUfn]
  refine shB2 impl hap R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C hE S hS sh hsh hsh0 A1 m3 hA1
    hA1sh hQ1f hQ1v hinv3 _ rfl rfl ?g28 ?g29 ?g18 rfl (by janus_frame) ?gz ?gn ?gx ?gs ?greg Q k
  case greg => simp only [Memory.regions_writeLE]; first | exact hreg3 | (rw [hm]; exact hreg3)
  case g28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  case g29 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29]
  case g18 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]
  all_goals
    simp (disch := omega) only [FvModexp.Expmc.readLE_writeLE_same, Memory.readLE_writeLE_of_disjoint, Nat.reducePow]
    omega

end FvModexp.Arm64.DivLarge
