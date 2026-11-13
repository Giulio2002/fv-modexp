import FvModexp.Proofs.Arm64.Exp.P2PreF
import FvModexp.Proofs.Arm64.Exp.P2PreMv

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (arm64): after the fill loop → `powers[0] = powers[0].set(natOne)` (nat.go:881;
inline `z.make(1)` reusing `powers[0]`, `memmove(z, natOne, 8)`), header store, write barrier (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp

/-- an opaque wrapper (keeps big hypotheses away from `janus_run`'s context splitting) -/
structure Hide (P : Prop) : Prop where
  h : P

/-- the join after `powers[0]`'s header store and write barrier (`0x1b55dc`, the pointer store `powers[0].ptr = buf`) -/
def X1J (impl : List Segment) (R : RtInv) (kc : Nat) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State) : Prop :=
  ∀ (S : State) (bp : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    S.pc = BitVec.ofNat 64 1791452 → S.sp = BitVec.ofNat 64 (s.sp.toNat - 208) → S.regs 28 = s.regs 28 →
    S.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216) → S.regs 18 = s.regs 18 →
    S.regs 3 = BitVec.ofNat 64 pw → S.regs 4 = BitVec.ofNat 64 (W lm) → S.regs 5 = BitVec.ofNat 64 pl →
    S.regs 7 = BitVec.ofNat 64 (2 * W lm) → S.regs 8 = BitVec.ofNat 64 1 → S.regs 9 = BitVec.ofNat 64 bp →
    Ctx R kc L st pw pl lm s bp S.mem L1 b1 → (∀ j, 1 ≤ j → j < pl → PwT S.mem pw bp lm j) →
    S.mem.readLE bp 8 = 1 → b ≤ b1 →
    Goal impl R kc sqC mlC b L st pw pl lm x xl s S

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat} {mlC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}


set_option maxRecDepth 20000 in
/-- `natOne` at a memory with the context: its header / word reads, readable, held, apart from `buf` -/
theorem one_ctx (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 op : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1)
    (hone : NatOne R L s.mem op (winA s (K kc) A ++ LW s pw pl st)) (hsop : StkApart s.mem st op 8) :
    M.readLE natOneA 8 = op ∧ M.readLE (natOneA + 8) 8 = 1 ∧ M.readLE op 8 = 1 ∧
      M.accessible natOneA 24 false = true ∧ M.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧
      Held R L1 op 8 ∧ Outside op 8 (winA s (K kc) A ++ LW s pw pl st) ∧ Apart bp (8 * NB pl lm) op 8 := by
  obtain ⟨o0, o1, -, o3, oa, ort, ow, oacc, o48, oh, oow⟩ := hone
  have hO : ∀ a n, Outside a n R.rt → Outside a n (winA s (K kc) A ++ LW s pw pl st) → M.readLE a n = s.mem.readLE a n :=
    fun a n h1 h2 => hc.fr.readLE a n (by simp only [AW, outside_append] at h2 ⊢; exact ⟨⟨h1, h2.1⟩, h2.2⟩)
  have hop : M.readLE op 8 = s.mem.readLE op 8 := by
    rcases oh with hL | hR
    · refine hc.lf.readLE op 8 hL ?_
      simp only [LW, outside_append] at oow ⊢
      exact oow.2
    · exact hO op 8 hR oow
  have hnb : 0 < NB pl lm := by
    simp only [NB]; exact Nat.mul_pos (by omega) (by have := (w_facts hpre).1; omega)
  refine ⟨?_, ?_, hop.trans o3, by rw [hc.fr.accessible]; exact oa, by rw [hc.fr.accessible]; exact oacc, o48,
    hc.le.held oh, oow, ?_⟩
  · rw [hO natOneA 8 (ort.of_sub (by omega) (by omega)) (ow.of_sub (by omega) (by omega))]; exact o0
  · rw [hO (natOneA + 8) 8 (ort.of_sub (by omega) (by omega)) (ow.of_sub (by omega) (by omega))]; exact o1
  · rcases hc.scr.loc with ⟨h0, h1, h2⟩ | ⟨hin, hap⟩
    · have := (hsop (by omega)).2 (by omega)
      unfold Apart at this ⊢; omega
    · rcases oh with hpL | hpO
      · have := hap.apart_of_inRanges hpL; unfold Apart at this ⊢; omega
      · have := hin.apart hpO; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem exitF (hmv : MemmoveLive (LibW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (kX : X1J impl R kc sqC mlC b L st pw pl lm x xl s) :
    FillJ impl R kc sqC mlC b L st pw pl lm x xl s pl := by
  intro S bp L1 b1 hpc hsp h28 h29 h18 h0 h1 h2 h3 h4 h5 hc hd _ hb
  have hsl := s.sp.isLt
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨hal, hb', ha, hw⟩ := hpre.1.2.1
  simp only [K, A] at hb' ha hw
  have hwS : S.mem.accessible (s.sp.toNat - (208 + kc)) (208 + kc + 80) true = true := by
    rw [hc.fr.accessible]; exact hw
  have hpw48 := hf.pw48
  have hpwa : S.mem.accessible pw (24 * pl) true = true := by rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hpww
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  obtain ⟨t0, t1, t2⟩ := hd 0 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_mul] at t0 t1 t2
  have hsv := hpre.2.1
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 8] := fun d src => hsv.2.1 d src 8 (by decide)
  obtain ⟨op, hone, hsop⟩ := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨n0, n8, n1, nacc, oacc, o48, oheld, oout, obuf⟩ := one_ctx hpre hc hone hsop
  have hinv := hc.inv
  obtain ⟨-, -, e2, e3, e4, -, e6, -, -, -, -, -⟩ := hc.sl
  have f224 : S.mem.readLE (s.sp.toNat - 208 + 224) 8 = pw := by
    rw [show s.sp.toNat - 208 + 224 = s.sp.toNat + 16 by omega]; exact e3
  have f232 : S.mem.readLE (s.sp.toNat - 208 + 232) 8 = pl := by
    rw [show s.sp.toNat - 208 + 232 = s.sp.toNat + 24 by omega]; exact e4
  have f144 : S.mem.readLE (s.sp.toNat - 208 + 144) 8 = W lm := by
    rw [show s.sp.toNat - 208 + 144 = s.sp.toNat - 64 by omega]; exact e6
  have hpl0 : pl ≠ 0 := by omega
  have hspN : S.sp.toNat = s.sp.toNat - 208 := by
    rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hnb0 : 0 < NB pl lm := by simp only [NB]; exact Nat.mul_pos (by omega) (by omega)
  have hne : op ≠ bp := by intro e; rw [e] at obuf; unfold Apart at obuf; have := hc.scr; omega
  have hc3 := ctx_own (ctx_own (ctx_own hc hf (2 * W lm) (a := s.sp.toNat - 208 + 104) (k := 8)
    ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩) hf 1 (a := s.sp.toNat - 208 + 96) (k := 8)
    ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩) hf bp (a := s.sp.toNat - 208 + 168) (k := 8)
    ⟨by omega, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
  have hopH : Hide (op + 8 ≤ s.sp.toNat - (208 + kc) ∨ s.sp.toNat + 80 ≤ op ∨
      (s.sp.toNat - 8 ≤ op ∧ op + 8 ≤ s.sp.toNat + 8)) := by
    clear hpww
    simp only [winA, LW, K, A, outside_append, outside_cons, outside_nil, and_true] at oout
    exact ⟨by omega⟩
  have hsw : op + 8 ≤ s.sp.toNat - 208 - 4096 ∨ s.sp.toNat - 208 + 32 ≤ op := by
    have := hopH.h; clear hpww; omega
  have hwok := wok_buf (zp := bp) (zn := 8 * NB pl lm) hc.scr (Nat.le_refl _) (Nat.le_refl _)
  -- disjunctions are kept hidden (each `omega` would split on them)
  have hboH : Hide (bp + 8 * NB pl lm ≤ s.sp.toNat - (208 + kc) ∨ s.sp.toNat + 80 ≤ bp) := by
    have := wok_win hwok hf.w (by simp only; omega); simp only [K, A] at this; exact ⟨by omega⟩
  have hbpwH : Hide (pw + 24 * pl ≤ bp ∨ bp + 8 * NB pl lm ≤ pw) := by
    have := wok_pw hwok hf.pwrt (hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by omega) (a := pw) (n := 24 * pl)
      (Nat.le_refl _) (Nat.le_refl _) (by simp only; omega)
    exact ⟨by simp only at this; omega⟩
  have hpwwH : Hide (pw + 24 * pl ≤ s.sp.toNat - (208 + kc) ∨ s.sp.toNat + 80 ≤ pw) := ⟨hpww⟩
  clear hpww
  have hnA : natOneA = 7356432 := rfl
  rw [hnA] at n0 n8 nacc
  have hmv' : MemmoveLive (LibW.program.link impl) mvE 4096 R := by rw [← mvE_eq]; exact hmv
  unfold Goal
  janus_run [n0, n8, t0, t2, f224, f232, f144] until [mvE]
  refine mvCall hmv' hpre hkc hc3 rfl rfl (by janus_simp) rfl (ra := 1791400) (by janus_simp) (by decide) (by decide)
    (d := bp) (src := op) (by janus_simp) (by janus_simp) (by janus_simp) (Nat.le_refl _) (by omega)
    (by simp only [Memory.accessible_writeLE]; exact oacc) o48 hsw
    fun junk f v m ex ep hcm hrd hcp => ?_
  have hrdF : ∀ a, s.sp.toNat - 176 ≤ a → a + 8 ≤ s.sp.toNat + 80 → m.readLE a 8 =
      (((S.mem.writeLE (s.sp.toNat - 208 + 104) 8 (2 * W lm)).writeLE (s.sp.toNat - 208 + 96) 8 1).writeLE
        (s.sp.toNat - 208 + 168) 8 bp).readLE a 8 := fun a h1 h2 =>
    hrd a 8 (by omega) (Or.inr (Or.inr ⟨h1, h2⟩)) (by have := hboH.h; omega)
  have g224 : m.readLE (s.sp.toNat - 208 + 224) 8 = pw := by
    rw [hrdF _ (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact f224
  have g232 : m.readLE (s.sp.toNat - 208 + 232) 8 = pl := by
    rw [hrdF _ (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact f232
  have g144 : m.readLE (s.sp.toNat - 208 + 144) 8 = W lm := by
    rw [hrdF _ (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact f144
  have g104 : m.readLE (s.sp.toNat - 208 + 104) 8 = 2 * W lm := by
    rw [hrdF _ (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  have g96 : m.readLE (s.sp.toNat - 208 + 96) 8 = 1 := by
    rw [hrdF _ (by omega) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
  have g168 : m.readLE (s.sp.toNat - 208 + 168) 8 = bp := by
    rw [hrdF _ (by omega) (by omega), Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  have hone' : m.readLE bp 8 = 1 := by
    have := hopH.h
    rw [hcp, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact n1
  have hdm : ∀ j, 1 ≤ j → j < pl → PwT m pw bp lm j := fun j h1 h2 => by
    obtain ⟨e0, e1, e2⟩ := hd j h2
    have := hbpwH.h; have := hpwwH.h
    have hr : ∀ a, pw + 24 * j ≤ a → a + 8 ≤ pw + 24 * j + 24 → m.readLE a 8 = S.mem.readLE a 8 := fun a h1 h2 => by
      rw [hrd a 8 (by omega) (Or.inl ⟨by omega, by omega⟩) (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact ⟨(hr _ (by omega) (by omega)).trans e0, (hr _ (by omega) (by omega)).trans e1,
      (hr _ (by omega) (by omega)).trans e2⟩
  have hgl := globals_ctx hpre hcm (S' := S) hspN (stk := 4096) (above := 8) (by omega) (by omega)
  have hwbf : m.accessible RunIface.wbA 4 false = true := hgl.2.2.2.2.2.2.2.2.2.2.1
  have hwbv : RunIface.wbA = 7616064 := rfl
  rw [hwbv] at hwbf
  have hpwm : m.accessible pw (24 * pl) true = true := by rw [hcm.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hwm : m.accessible (s.sp.toNat - (208 + kc)) (208 + kc + 80) true = true := by rw [hcm.fr.accessible]; exact hw
  -- after the header store `(1, 2w)`
  have hc5 := ctx_own (ctx_own hcm hf 1 (a := pw + 8) (k := 8) ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩) hf
    (2 * W lm) (a := pw + 8 + 8) (k := 8) ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
  have hr5 : ∀ a n, (a + n ≤ pw + 8 ∨ pw + 24 ≤ a) →
      ((m.writeLE (pw + 8) 8 1).writeLE (pw + 8 + 8) 8 (2 * W lm)).readLE a n = m.readLE a n := fun a n h => by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hd5 : ∀ j, 1 ≤ j → j < pl → PwT ((m.writeLE (pw + 8) 8 1).writeLE (pw + 8 + 8) 8 (2 * W lm)) pw bp lm j :=
    fun j h1 h2 => by
      obtain ⟨e0, e1, e2⟩ := hdm j h1 h2
      exact ⟨(hr5 _ _ (by omega)).trans e0, (hr5 _ _ (by omega)).trans e1, (hr5 _ _ (by omega)).trans e2⟩
  have ho5 : ((m.writeLE (pw + 8) 8 1).writeLE (pw + 8 + 8) 8 (2 * W lm)).readLE bp 8 = 1 :=
    (hr5 _ _ (by have := hbpwH.h; omega)).trans hone'
  have hpreB : Hide (Pre R kc sqC mlC b L st pw pl ws lm x xl s) := ⟨hpre⟩
  clear hpre hrd hrdF hdm hd hone hsop oout hcp hgl hc hc3 hcm hr5 obuf oheld
  have hpww := hpwwH.h
  janus_run [g224, g232, g144, g104, g96, g168, hwbf, hpwm, hwm] until [wbE, 1791452]
  · -- the barrier is off
    refine kX _ bp L1 b1 rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hc5 hd5 ho5 hb
    all_goals janus_simp
  · -- the barrier is on
    refine wbCall hwb hpreB.h hkc hc5 rfl rfl (by janus_simp) rfl (ra := 1791448) (by janus_simp) (by decide) (by decide)
      fun buf junk f v m' ex ep hb48 hbal hbacc hctx hrdW => ?_
    have hb8a : m'.accessible buf.toNat 8 true = true := Memory.accessible_mono _ hbacc (Nat.le_refl _) (by omega)
    have hb8b : m'.accessible (buf.toNat + 8) 8 true = true := Memory.accessible_mono _ hbacc (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    janus_run [hb8a, hb8b, hbuf64] until [1791452]
    have hr := hrdW bp (m.readLE pw 8)
    have hdW : ∀ j, 1 ≤ j → j < pl → PwT (W2 m' buf.toNat bp (m.readLE pw 8)) pw bp lm j := fun j h1 h2 => by
      obtain ⟨e0, e1, e2⟩ := hd5 j h1 h2
      exact ⟨(hr _ 8 (by omega) (Or.inl ⟨by omega, by omega⟩)).trans e0,
        (hr _ 8 (by omega) (Or.inl ⟨by omega, by omega⟩)).trans e1,
        (hr _ 8 (by omega) (Or.inl ⟨by omega, by omega⟩)).trans e2⟩
    refine kX _ bp L1 b1 rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hctx _ _) hdW
      ((hr _ 8 (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans ho5) hb
    all_goals janus_simp
end

end FvModexp.Arm64.P2Pre
