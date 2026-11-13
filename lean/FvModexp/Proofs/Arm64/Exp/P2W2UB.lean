import FvModexp.Proofs.Arm64.Exp.P2W2LI
import FvModexp.Proofs.Arm64.Exp.P2W2Al

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): U-class buffers (`UB`) — the entry `z`, a fresh allocation, transport
(agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- a fresh range is apart from every held range -/
theorem fresh_held_apart {R : RtInv} {L1 : List (Nat × Nat)} {p n t k : Nat} (hin : InRanges p n R.rt)
    (hap : ApartAll p n L1) (hh : Held R L1 t k) : Apart p n t k := by
  rcases hh with hL | hO
  · have := hap.apart_of_inRanges hL; unfold Apart; omega
  · exact (hin.apart hO).symm

/-- a held range apart from the entry free part is apart from an entry-relative scratch nat -/
theorem held_scr_apart {R : RtInv} {L L1 : List (Nat × Nat)} {m0 M : Memory} {st a n t k : Nat}
    (hh : Held R L a n) (hf : Apart a n (free m0 st).1 (free m0 st).2) (hs : Scr R L L1 m0 M st t k) :
    Apart a n t (8 * k) := by
  rcases hs.loc with ⟨-, l1, l2⟩ | ⟨hin, hap⟩
  · simp only [free, Apart] at hf ⊢; omega
  · exact (fresh_held_apart hin hap hh).symm

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- the entry `z` (`0 < cap z`) is a U-class buffer -/
theorem ub_z (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ)
    {zzp bp X : Nat} (htz : TZ R L s.mem M L1 st sp zzp bp lm X) :
    UB R L K g sp st zp zc M L1 zzp bp lm zp zc := by
  have hzc40 : zc < 2 ^ 40 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hzc40, fun hzc => ?_, Or.inl ⟨rfl, rfl⟩, fun hzc => ?_, fun _ _ => Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨⟨hzO1, -, -, -⟩, hzacc, hz48, hz8, -⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hzc
    exact ⟨hz8, h.le.held hzO1, by rw [h.fr.accessible]; exact hzacc, hz48⟩
  · obtain ⟨⟨hzO1, hzO2, hzO3, hzO4⟩, -, -, -, hzg, -, -, hzA⟩ :=
      hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hzc
    exact ⟨hzO2, hzO3, hzA, hzg.symm, free_apart h hzO1 hzO4, held_scr_apart hzO1 hzO4 htz.zscr,
      held_scr_apart hzO1 hzO4 htz.bscr⟩

set_option maxRecDepth 20000 in
/-- a fresh allocation `[p, p + r)` (cap `c`, `8 c ≤ r`) is a U-class buffer -/
theorem ub_fresh (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hl : 0 < ℓ) {m : Memory} {p r n : Nat}
    (hA : AllocR R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ m p r n) {zzp bp X : Nat}
    (htz : TZ R L s.mem M L1 st sp zzp bp lm X) {c : Nat} (hc0 : 0 < c) (hc : 8 * c ≤ r) (hc40 : c < 2 ^ 40) :
    UB R L K g sp st zp zc m (L1 ++ [(p, p + r)]) zzp bp lm p c := by
  have hin : InRanges p (8 * c) R.rt := hA.rin.sub (Nat.le_refl _) (by omega)
  have hap : ApartAll p (8 * c) L1 := ApartAll.sub' hA.rap (Nat.le_refl _) (by omega)
  have hce := h.cenv hP
  obtain ⟨-, -, -, -, -, -, -, -, -, hgrt, -⟩ := hce
  have hgA : OE R L sp K st s.mem RunIface.gA 32 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 560) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsok := h.sok
  have hlen := h.len
  have e0 : stW m st = stW M st := hA.rdH _ _ (hsok.2.1.sub (Nat.le_refl _) (by omega)) (by unfold Apart at hstw ⊢; omega)
  have e1 : stLen m st = stLen M st := hA.rdH _ _ (hsok.2.1.sub (by omega) (by omega)) (by unfold Apart at hstw ⊢; omega)
  have e2 : stCap m st = stCap M st := hA.rdH _ _ (hsok.2.1.sub (by omega) (by omega)) (by unfold Apart at hstw ⊢; omega)
  have hcap : 0 < stCap M st := by have := hsok.2.2.2.2.2.1; omega
  have harr := fresh_held_apart hin hap (hsok.2.2.2.2.1 hcap).2.1
  have hlc := hsok.2.2.2.2.2.1
  refine ⟨hc40, fun _ => ⟨hA.al, Or.inl ⟨(p, p + r), by simp, by simp only; omega, by simp only; omega⟩,
    Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by omega), by have := hA.b48; omega⟩,
    Or.inr ⟨hc0, hin, fun q hq => hap q (h.le.mem_old hq)⟩, fun _ => ⟨(hin.apart hP.win_rt).symm,
    fresh_held_apart hin hap hsok.2.1, fresh_held_apart hin hap (h.le.held hgA.1), (hin.apart hgrt).symm, ?_,
    fresh_held_apart hin hap htz.zscr.held, fresh_held_apart hin hap htz.bscr.held⟩,
    fun _ _ => Or.inr (by simp only [e0, e2]; exact harr)⟩
  simp only [free, e0, e1, e2]
  unfold Apart at harr ⊢; omega

/-- `UB` through a step that keeps the stack header and accessibility, with a larger live set -/
theorem UB.keep {L2 : List (Nat × Nat)} {M' : Memory} {zzp bp p c : Nat}
    (hu : UB R L K g sp st zp zc M L1 zzp bp lm p c) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w)
    (hx : LiveExt R L1 L2) (e0 : stW M' st = stW M st) (e1 : stLen M' st = stLen M st)
    (e2 : stCap M' st = stCap M st) : UB R L K g sp st zp zc M' L2 zzp bp lm p c := by
  refine ⟨hu.c40, fun hc => ?_, hu.org, fun hc => ?_, fun hc => by rw [e0, e2]; exact hu.rs hc⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hu.live hc
    exact ⟨a1, hx.held a2, by rw [hacc]; exact a3, a4⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hu.ap hc
    exact ⟨a1, a2, a3, a4, by simp only [free, e0, e1, e2]; exact a5, a6, a7⟩

end

end FvModexp.Arm64.P2W2
