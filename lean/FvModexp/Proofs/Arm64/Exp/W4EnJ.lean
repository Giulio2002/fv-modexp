import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4EnDefs

/-!
# window-4 entry (arm64): the join of `slices.Grow` (`enJ`, fn+0x178) → `xnE` (fn+0x1a4)

The header update of the inline `stk.reserve(23n)` (nat.go:336-337): `len, cap` stores, the write-barrier flag test,
(flag on) `gcWriteBarrier2` with its buffer stores `(new ptr, old ptr)`, the pointer store, `len := len + nr`.
Adapted from agent divmc's `(*stack).nat` `joinW`/`tail` (Arm64/Nat/StackNatWb/Tail).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4En

/-- the pointer store `MOVD R13, (R3)` (both write-barrier branches) -/
abbrev enS : Nat := 1798916

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem enJn (impl : List Segment) (R : RtInv)
    (hwb : WbLiveContract (LibW.program.link impl) wbE 4096 R 2)
    (ret0 : Nat) (hret : RetAddr (LibW.program.link impl) ret0) (Q : Outcome → Prop)
    (b1 : Nat) (L1 : List (Nat × Nat)) (g sp st w1 len0 c1 n : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 4304 ≤ sp) (hsp2 : sp + 1040 ≤ 2 ^ 48)
    (hwacc : M.accessible (sp - 4096) (4096 + 8) true = true)
    (hwrt : LiveSep [(sp - 4096, sp - 8)] R.rt) (hwL : LiveSep L1 [(sp - 4096, sp - 8)])
    (hsta : M.accessible st 24 true = true) (hst48 : st + 24 ≤ 2 ^ 48)
    (hsth : InRanges st 24 L1 ∨ Outside st 24 R.rt) (hstw : st + 24 ≤ sp - 4096 ∨ sp - 8 ≤ st)
    (hwbf : M.accessible StackNat.wbA 4 false = true) (hwbA : Apart st 24 StackNat.wbA 4)
    (hok : R.ok wbE [2]) (hinv : R.inv b1 L1 g (view R.rt L1 M)) (hg : g < 2 ^ 64)
    (hc : len0 + StackNat.rnd (23 * n) ≤ c1) (hc40 : c1 < 2 ^ 40) (hw64 : w1 < 2 ^ 64) (hl16 : len0 ≤ 2 ^ 16)
    (hn : n ≤ 128)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 enJ) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h13 : S.regs 13 = BitVec.ofNat 64 w1)
    (h14 : S.regs 14 = BitVec.ofNat 64 len0) (h15 : S.regs 15 = BitVec.ofNat 64 c1)
    (h9 : S.regs 9 = BitVec.ofNat 64 (len0 + StackNat.rnd (23 * n))) (h28 : S.regs 28 = BitVec.ofNat 64 g)
    (hmem : S.mem = M)
    (K : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 xnE → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 →
      S'.regs 8 = S.regs 8 → S'.regs 10 = S.regs 10 → S'.regs 11 = S.regs 11 → S'.regs 18 = S.regs 18 →
      S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' (R.rt ++ [(st, st + 24), (sp - 4096, sp - 8)]) → LiveFrame M M' L1 [(st, st + 24)] →
      M'.regions = M.regions → R.inv b1 L1 g (view R.rt L1 M') →
      M'.readLE st 8 = w1 → M'.readLE (st + 8) 8 = len0 + StackNat.rnd (23 * n) → M'.readLE (st + 16) 8 = c1 →
      Reaches ((LibW.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret0) S Q := by
  have hrn : StackNat.rnd (23 * n) ≤ 23 * n + 3 := by simp only [StackNat.rnd]; omega
  have hacc16 : M.accessible (st + 8) 16 true = true := Memory.accessible_mono _ hsta (by omega) (by omega)
  have hacc8 : M.accessible st 8 true = true := Memory.accessible_mono _ hsta (by omega) (by omega)
  have hwbv : StackNat.wbA = 7616064 := rfl
  rw [hwbv] at hwbA hwbf
  unfold Apart at hwbA
  have hF1 : MemFrame M ((M.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1) [(st, st + 24)] := by janus_frame
  have hinv1 : R.inv b1 L1 g (view R.rt L1 ((M.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1)) :=
    RtInv.inv_frame' hF1 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [show st + 24 - st = 24 by omega]; exact hsth.symm) hinv
  have es1 : BitVec.ofNat 64 sp - 0#64 = BitVec.ofNat 64 sp := BitVec.sub_zero _
  generalize e4 : S.regs 4 = x4 at K
  generalize e5 : S.regs 5 = x5 at K
  generalize e6 : S.regs 6 = x6 at K
  generalize e8 : S.regs 8 = x8 at K
  generalize e10 : S.regs 10 = x10 at K
  generalize e11 : S.regs 11 = x11 at K
  generalize e18 : S.regs 18 = x18 at K
  generalize e29 : S.regs 29 = x29 at K
  have hw1 : (BitVec.ofNat 64 w1).toNat = w1 := by rw [BitVec.toNat_ofNat]; omega
  janus_run [hacc16, hacc8, hwbf] until [wbE, enS]
  · -- the barrier is off
    janus_run [hacc16, hacc8] until [xnE]
    refine K _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?lf ?rg ?inv ?q1 ?q2 ?q3
    case mf => janus_frame
    case lf =>
      have h : MemFrame M (((M.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1).writeLE st 8 w1 |>.writeLE (st + 8) 8
        (len0 + StackNat.rnd (23 * n))) [(st, st + 24)] := by janus_frame
      exact ⟨fun a k _ ho => h.readLE a k ho⟩
    case inv =>
      refine RtInv.inv_frame' (ws := [(st, st + 24)]) (by janus_frame) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [show st + 24 - st = 24 by omega]; exact hsth.symm) hinv
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow, Memory.regions_writeLE]
    all_goals omega
  · -- the barrier is on
    have hacc4 : ((M.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1).accessible (sp - 4096) (4096 + 8) true = true := by
      simp only [Memory.accessible_writeLE]; exact Memory.accessible_mono _ hwacc (by omega) (by omega)
    refine Reaches.call_regions ((hwb L1 b1).withExit hret) ?_ ⟨⟨?_, ?_, ?_, ?_, by omega, ?_, ?_⟩, hok, ?_, ?_, ?_⟩ ?_
    · rfl
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
    · dsimp only; rw [BitVec.toNat_ofNat]; omega
    · dsimp only; rw [BitVec.toNat_ofNat]; omega
    · dsimp only; rw [BitVec.toNat_ofNat]; omega
    · dsimp only; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hacc4
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg]; exact hinv1
    · dsimp only; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hwL
    · dsimp only; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hwrt
    intro S2 hpc2 ⟨buf, junk, f2, v2, m', ex2, ep2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩ hrg2
    subst hs2
    dsimp only at hfr2 hlf2 hapW hinvS hsl hapL hrg2
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hfr2 hapW
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28] at hinvS
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg] at hinvS
    obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := hsl
    have hbufR : InRanges buf.toNat 16 R.rt := by simpa using hsl1
    have hacc16b : m'.accessible buf.toNat 16 true = true := by simpa using hsl3
    have hb8a : m'.accessible buf.toNat 8 true = true := Memory.accessible_mono _ hacc16b (Nat.le_refl _) (by omega)
    have hb8b : m'.accessible (buf.toNat + 8) 8 true = true := Memory.accessible_mono _ hacc16b (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    have hstb : st + 24 ≤ buf.toNat ∨ buf.toNat + 16 ≤ st := by
      rcases hsth with hL | hO
      · have := hapL.apart_of_inRanges hL; omega
      · have := hbufR.apart hO; unfold Apart at this; omega
    have hkeep : ∀ a k, st ≤ a → a + k ≤ st + 24 →
        m'.readLE a k = ((M.writeLE (st + 8) 8 len0).writeLE (st + 16) 8 c1).readLE a k := by
      intro a k h1 h2
      rcases hsth with hL | hO
      · exact hlf2.readLE a k (hL.sub h1 h2) trivial
      · refine hfr2.readLE a k ?_
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hO.of_sub h1 h2, by omega⟩
    have hacc8' : m'.accessible st 8 true = true := by rw [hfr2.accessible]; simp only [Memory.accessible_writeLE]; exact hacc8
    have hacc8'' : m'.accessible (st + 8) 8 true = true := by
      rw [hfr2.accessible]; simp only [Memory.accessible_writeLE]; exact Memory.accessible_mono _ hacc16 (by omega) (by omega)
    have hk0 := hkeep st 8 (Nat.le_refl _) (by omega)
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)] at hk0
    have hk16 := hkeep (st + 16) 8 (by omega) (by omega)
    rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)] at hk16
    janus_run [hb8a, hb8b, hbuf64, hk0, hacc8', hacc8''] until [xnE]
    have hbs : MemFrame m' (((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st 8)).writeLE st 8 w1
        |>.writeLE (st + 8) 8 (len0 + StackNat.rnd (23 * n))) [(buf.toNat, buf.toNat + 16), (st, st + 24)] := by
      refine MemFrame.writeLE ?_ _ (r := (st, st + 24)) (by simp) (by simp only; omega) (by simp only; omega)
      refine MemFrame.writeLE ?_ _ (r := (st, st + 24)) (by simp) (by simp only; omega) (by simp only; omega)
      refine MemFrame.writeLE ?_ _ (r := (buf.toNat, buf.toNat + 16)) (by simp) (by simp only; omega) (by simp only; omega)
      refine MemFrame.writeLE ?_ _ (r := (buf.toNat, buf.toNat + 16)) (by simp) (by simp only; omega) (by simp only; omega)
      exact MemFrame.refl _ _
    apply K
    all_goals first | (janus_simp; done) | skip
    · rfl
    all_goals dsimp only
    · -- mf
      refine MemFrame.trans (rs'' := R.rt ++ [(st, st + 24), (sp - 4096, sp - 8)])
        (MemFrame.trans (rs'' := R.rt ++ [(st, st + 24), (sp - 4096, sp - 8)]) hF1 hfr2 fun a k ho => ?_)
        hbs fun a k ho => ?_
      · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        exact ⟨ho.2.1, ho.1, ho.2.2⟩
      · refine ⟨ho, ?_⟩
        simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        have := hbufR.apart ho.1; unfold Apart at this; exact ⟨by omega, ho.2.1⟩
    · -- lf
      refine ⟨fun a k hin hout => ?_⟩
      have := hapL.apart_of_inRanges hin
      rw [hbs.readLE a k ?_, hlf2.readLE a k hin trivial, hF1.readLE a k hout]
      simp only [outside_cons, outside_nil, and_true] at hout ⊢; exact ⟨by omega, hout⟩
    · simp only [Memory.regions_writeLE] at hrg2 ⊢; exact hrg2
    · -- inv
      have hv1 : view R.rt L1 ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st 8)) =
          ((view R.rt L1 m').writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st 8) := by
        rw [view_writeLE_vis (hbufR.sub (by omega) (by omega)) (Outside.of_sub hapL.outside (by omega) (by omega)),
          view_writeLE_vis (hbufR.sub (Nat.le_refl _) (by omega)) (Outside.of_sub hapL.outside (Nat.le_refl _) (by omega))]
      have hv : R.inv b1 L1 g (view R.rt L1 ((m'.writeLE buf.toNat 8 w1).writeLE (buf.toNat + 8) 8 (M.readLE st 8))) := by
        rw [hv1]; exact hinvS _ (by janus_frame)
      refine RtInv.inv_frame' (ws := [(st, st + 24)]) (by janus_frame) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [show st + 24 - st = 24 by omega]; exact hsth.symm) hv
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow]
    all_goals first | omega | (rw [hkeep _ _ (by omega) (by omega)]; simp (disch := omega) only
      [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]; omega) | skip

end FvModexp.Arm64.W4En
