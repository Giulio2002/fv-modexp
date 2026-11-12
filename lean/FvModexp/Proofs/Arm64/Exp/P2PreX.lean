import FvModexp.Proofs.Arm64.Exp.P2PreF
import FvModexp.Proofs.Arm64.Exp.P2PreMv

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

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
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
theorem exitF (hmv : MemmoveLive (LibExp.program.link impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (LibExp.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) :
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
  simp only [winA, LW, K, A, outside_append, outside_cons, outside_nil, and_true] at oout
  have hnA : natOneA = 7356432 := rfl
  rw [hnA] at n0 n8 nacc
  have hmv' : MemmoveLive (LibExp.program.link impl) mvE 4096 R := by rw [← mvE_eq]; exact hmv
  unfold Goal
  janus_run [n0, n8, t0, t2, f224, f232, f144] until [mvE]
  refine mvCall hmv' hpre hkc hc3 rfl rfl (by janus_simp) rfl (ra := 1791400) (by janus_simp) (by decide) (by decide)
    (d := bp) (src := op) (by janus_simp) (by janus_simp) (by janus_simp) (Nat.le_refl _) (by omega)
    (by simp only [Memory.accessible_writeLE]; exact oacc) o48 (by omega)
    fun junk f v m ex ep hcm hrd hcp => ?_
  trace_state
  sorry
end

end FvModexp.Arm64.P2Pre
