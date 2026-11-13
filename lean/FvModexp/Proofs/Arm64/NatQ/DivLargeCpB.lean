import FvModexp.Proofs.Arm64.NatQ.DivLargeCpE

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivLargeCpB.lean, TIGHT COSTS, asm s38)
# `divLarge` (arm64): copy path after `copy(v, vIn)` (`fn + 0x198`): `copy(u[:len uIn], uIn)` (natdiv.go:611; the
`memmove` is skipped when `u`'s array is `uIn`'s) → `fn + 0x204` (`cpE`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Q.DivLarge
open FvModexp.Arm64.DivLarge
variable {H : Nat}

/-- the frame slots after the first `memmove` -/
theorem cp_rd1 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il ic vp vl vc : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S) {m : Memory}
    (hMF : MemFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m (R.rt ++ csW s ++ [(t, t + 8 * vl)])) :
    m.readLE (s.sp.toNat - 96) 8 = t ∧ m.readLE (s.sp.toNat - 160) 8 = vl ∧ m.readLE (s.sp.toNat - 152) 8 = vl ∧
      m.readLE (s.sp.toNat - 176) 8 = C ∧ m.readLE (s.sp.toNat - 192) 8 = il + 1 ∧
      m.readLE (s.sp.toNat - 104) 8 = P ∧ m.readLE (s.sp.toNat - 120) 8 = 0 ∧
      m.readLE (s.sp.toNat + 96) 8 = vl ∧ m.readLE (s.sp.toNat + 72) 8 = il ∧ m.readLE (s.sp.toNat + 64) 8 = ip := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have htw := hl.tw
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  have hM := hS.mem
  have rd : ∀ a, s.sp.toNat - 200 ≤ a → a + 8 ≤ s.sp.toNat + 112 →
      m.readLE a 8 = (S.mem.writeLE (s.sp.toNat - 120) 8 0).readLE a 8 := fun a h1 h2 =>
    hMF.readLE _ _ (by
      simp only [csW, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have wd : ∀ a, (a + 8 ≤ s.sp.toNat - 120 ∨ s.sp.toNat - 112 ≤ a) →
      (S.mem.writeLE (s.sp.toNat - 120) 8 0).readLE a 8 = S.mem.readLE a 8 := fun a h =>
    Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rd _ (by omega) (by omega), wd _ (by omega)]; exact hM.vt
  · rw [rd _ (by omega) (by omega), wd _ (by omega)]; exact hM.vn1
  · rw [rd _ (by omega) (by omega), wd _ (by omega)]; exact hM.vn2
  · rw [rd _ (by omega) (by omega), wd _ (by omega)]; exact hS.sC
  · rw [rd _ (by omega) (by omega), wd _ (by omega)]; exact hS.sL
  · rw [rd _ (by omega) (by omega), wd _ (by omega)]; exact hS.sP
  · rw [rd _ (by omega) (by omega), Memory.readLE_writeLE_self]
  · rw [rd _ (by omega) (by omega), wd _ (by omega)]; exact hM.s12
  · rw [rd _ (by omega) (by omega), wd _ (by omega)]; exact hM.s9
  · rw [rd _ (by omega) (by omega), wd _ (by omega)]; exact hM.s8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `copy(u[:len uIn], uIn)`'s `memmove` (`fn + 0x1e0`): reloads → `fn + 0x204` -/
theorem cpC (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (hclz : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0)
    (m3 m4 : Memory)
    (hMF1 : MemFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m3 (R.rt ++ csW s ++ [(t, t + 8 * vl)]))
    (hLF1 : LiveFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m3 Lk [(t, t + 8 * vl)])
    (hcp1 : Mem.Copied (S.mem.writeLE (s.sp.toNat - 120) 8 0) m3 t vp (8 * vl))
    (hMF2 : MemFrame m3 m4 (R.rt ++ csW s ++ [(P, P + 8 * il)]))
    (hLF2 : LiveFrame m3 m4 Lk [(P, P + 8 * il)])
    (hinv4 : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m4))
    (hval : natVal m4 P il = natVal s.mem ip il)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x1e0)) (hsp : T.sp = s.sp - 304#64)
    (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 312#64) (h18 : T.regs 18 = s.regs 18) (hm : T.mem = m4)
    (hreg4 : m4.regions = s.mem.regions) (Q : State → Prop)
    (k : ∀ S', AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C 0 S' →
      ReachesRet (LibDivL.program.link impl) (s.regs 30) S' Q) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hU := hS.ua
  have hpw := hU.pw; have hcap := hU.cap
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, -⟩ := cp_rd1 hE hS hMF1
  have rd : ∀ a, s.sp.toNat - 200 ≤ a → a + 8 ≤ s.sp.toNat + 112 → m4.readLE a 8 = m3.readLE a 8 := fun a h1 h2 =>
    hMF2.readLE _ _ (by
      simp only [csW, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩)
  have q1 := (rd _ (by omega) (by omega)).trans r1; have q2 := (rd _ (by omega) (by omega)).trans r2
  have q3 := (rd _ (by omega) (by omega)).trans r3; have q4 := (rd _ (by omega) (by omega)).trans r4
  have q5 := (rd _ (by omega) (by omega)).trans r5; have q6 := (rd _ (by omega) (by omega)).trans r6
  have q7 := (rd _ (by omega) (by omega)).trans r7; have q8 := (rd _ (by omega) (by omega)).trans r8
  have q9 := (rd _ (by omega) (by omega)).trans r9
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hwacc : m4.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by
    rw [hMF2.accessible, hMF1.accessible, Memory.accessible_writeLE, hS.mem.fr.accessible]; exact hw
  janus_run [hm, q1, q2, q3, q4, q5, q6, q7, q8, q9] until [segAddr Extracted.program fn + 0x204]
  refine cpE impl R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C hE S hS hclz m3 m4 hMF1 hLF1 hcp1
    hMF2 hLF2 hinv4 hval _ rfl rfl ?g28 ?g29 ?g18 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hreg4 Q k
  all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28, h29, h18]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `copy(v, vIn)` (`fn + 0x198`): `copy(u[:len uIn], uIn)` (skipped when `P = uIn`) → `fn + 0x204` -/
theorem cpB (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibDivL.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il ic vp vl vc : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C : Nat)
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtU R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C S)
    (hclz : clzNat 64 (s.mem.readLE (vp + 8 * (vl - 1)) 8) = 0) (Q : State → Prop)
    (k : ∀ S', AtA R b L zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C 0 S' →
      ReachesRet (LibDivL.program.link impl) (s.regs 30) S' Q)
    (m : Memory) (T : State) (hpc : T.pc = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x198))
    (hsp : T.sp = s.sp - 304#64) (h28 : T.regs 28 = s.regs 28) (h29 : T.regs 29 = s.sp - 312#64)
    (h18 : T.regs 18 = s.regs 18) (hm : T.mem = m) (hreg : m.regions = s.mem.regions)
    (hMF1 : MemFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m (R.rt ++ csW s ++ [(t, t + 8 * vl)]))
    (hLF1 : LiveFrame (S.mem.writeLE (s.sp.toNat - 120) 8 0) m Lk [(t, t + 8 * vl)])
    (hinv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk m))
    (hcp1 : Mem.Copied (S.mem.writeLE (s.sp.toNat - 120) 8 0) m t vp (8 * vl)) :
    ReachesRet (LibDivL.program.link impl) (s.regs 30) T Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hvil := hl.vil; have hil9 := hl.il9
  have hU := hS.ua
  have hpw := hU.pw; have hcap := hU.cap; have hp48 := hU.p48
  have hout : Outside (s.sp.toNat - 41264) (41264 + 112) R.rt := hE.pre.ce.2.2.2.1
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := cp_rd1 hE hS hMF1
  obtain ⟨hal, hb', ha, hw⟩ := hE.pre.ce.2.1
  have hMacc : ∀ a n w, m.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hMF1.accessible, Memory.accessible_writeLE, hS.mem.fr.accessible]
  have hwacc : m.accessible (s.sp.toNat - 41264) (41264 + 112) true = true := by rw [hMacc]; exact hw
  -- `uIn` unchanged so far
  have hiw := hl.iw; have hti := hl.ti
  have hI : natVal m ip il = natVal s.mem ip il := by
    unfold natVal
    have hih : Held R Lk ip (8 * il) := hS.ext2.held (hE.ext.held hE.pre.io.2.2.2.1)
    have e1 : m.readLE ip (8 * il) = (S.mem.writeLE (s.sp.toNat - 120) 8 0).readLE ip (8 * il) := by
      rcases hih with hi | ho
      · exact hLF1.readLE _ _ hi (by simp only [outside_cons, outside_nil, and_true]; omega)
      · exact hMF1.readLE _ _ (by
          simp only [csW, outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨ho, by omega, by omega⟩, by omega⟩)
    rw [e1, Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hS.is _ _ (Nat.le_refl _) (Nat.le_refl _)
  have hLs := lsep_of hE hS.ext2
  by_cases hPi : P = ip
  · subst hPi
    janus_run [hm, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10] until [segAddr Extracted.program fn + 0x204]
    refine cpE impl R b L c zp zc st up uc P il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C hE S hS hclz m m hMF1 hLF1 hcp1
      ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩ ⟨fun _ _ _ _ => rfl⟩ hinv hI _ rfl rfl ?g28 ?g29 ?g18 rfl rfl rfl rfl rfl rfl
      rfl rfl rfl ?gm hreg Q k
    case gm => first | rfl | exact hm
    all_goals simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28, h29, h18]
  · have hPi' : P ≠ ip := hPi
    have hPi'' : ip ≠ P := fun h => hPi h.symm
    have hi48 := hl.i48
    have hpi := hU.pi
    have hap : Apart P (8 * C) ip (8 * il) := hpi.resolve_left hPi
    unfold Apart at hap
    have hl3 := lsl3_ofNat il (by omega)
    have hsv := hE.pre.sv
    have hgrd : m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
      have hga := hE.pre.ce.2.2.2.2.1; have hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt := hE.pre.ce.2.2.2.2.2.1
      have hgt := (wsL_parts (g_wsL hE)).1
      unfold Apart at hga
      rw [hMF1.readLE _ _ (by
          simp only [csW, outside_append, outside_cons, outside_nil, and_true]
          exact ⟨⟨hgr, by omega, by omega⟩, by omega⟩),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact Mem.grd hE hS.mem
    janus_run [hm, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, hl3] until [cA "runtime.memmove"]
    have e304 : (s.sp - 304#64).toNat = s.sp.toNat - 304 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    refine ReachesRet.call_regions (hmv Lk bk) rfl (mv_pre (dst := P) (src := ip) (n := 8 * il) hE hS.ext2 _ rfl ?q28 hgrd
      hMacc ?l1 ?l2 hinv ?q0 ?q1 ?q2 (hsv.2.1 _ _ _ (by omega)) (by omega) ?dacc (hU.pheld.sub (by omega) (by omega))
      (by omega) (by have := hl.i48; omega) ?sacc (by omega)) ?qk
    case q28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
    case l1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    case l2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    case q0 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]; omega
    case q1 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]; omega
    case q2 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat]; omega
    case dacc => rw [hMacc]; exact Memory.accessible_mono _ (by rw [← hS.mem.fr.accessible]; exact hU.pacc) (by omega) (by omega)
    case sacc => rw [hMacc]; exact hE.pre.io.2.1
    case qk =>
      intro T2 hT ⟨junk, f, v, m4, ex, ep, hs, hMF, hLF, hinv4, hcp⟩ hrg
      subst hs
      simp only [calleeStack, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.toNat_ofNat, e304, h28] at hMF hLF hcp hinv4
      rw [Nat.mod_eq_of_lt (show P < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show ip < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show 8 * il < 2 ^ 64 by omega)] at hcp
      rw [Nat.mod_eq_of_lt (show P < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * il < 2 ^ 64 by omega)] at hMF hLF
      have hval : natVal m4 P il = natVal s.mem ip il := by
        unfold natVal; rw [FvModexp.Asm.readLE_of_copied hcp]; exact hI
      exact cpC impl R b L c zp zc st up uc ip il ic vp vl vc s t w1 c1 L1 b1 Lk bk P C hE S hS hclz m m4 hMF1 hLF1 hcp1
        hMF hLF hinv4 hval _ (by rw [hT]; simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; rfl) rfl
        (by simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28, true_or, or_true, if_true])
        (by simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h29, true_or, or_true, if_true])
        (by simp only [retStateX, callRegs_apply, setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18, true_or, or_true, if_true])
        rfl (by simp only [retStateX, Memory.regions_writeLE] at hrg; rw [hrg]; exact hreg) Q k

end FvModexp.Arm64.Q.DivLarge
