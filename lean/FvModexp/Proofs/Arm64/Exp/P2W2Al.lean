import FvModexp.Proofs.Arm64.Exp.P2W2WC

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): `WC` through a live allocation (`makeslice` / `newobject`) (agent infra)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- a range of the window strictly below the saved FP is outside `WN` -/
theorem cs_out {a k : Nat} {cs : List (Nat × Nat)} (hcs : ∀ q ∈ cs, sp - K ≤ q.1 ∧ q.2 ≤ sp + 456)
    (ho : Outside a k (WN sp K)) : Outside a k cs := by
  simp only [WN, outside_cons, outside_nil, and_true] at ho
  refine outside_of_forall fun q hq => ?_
  have := hcs q hq; omega

/-- the stack header through a step that writes only the runtime's ranges and `cs` (in the window) and keeps `L1` -/
theorem hdr_keep (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {m : Memory} {cs : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ cs))
    (hcs : ∀ q ∈ cs, sp - K ≤ q.1 ∧ q.2 ≤ sp + 456) (hLF : LiveFrame M m L1 []) {a k : Nat} (h1 : st ≤ a)
    (h2 : a + k ≤ st + 24) : m.readLE a k = M.readLE a k := by
  have hstw : Apart st 24 (sp - K) (K + 560) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  rcases h.sok.2.1 with hL | hO
  · exact hLF.readLE a k (hL.sub h1 h2) trivial
  · refine hMF.readLE a k ?_
    rw [outside_append]
    refine ⟨hO.of_sub h1 h2, outside_of_forall fun q hq => ?_⟩
    have := hcs q hq; omega

/-- **`WC` through a live allocation** of `[p, p + r)` -/
theorem WC.alloc (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {m : Memory} {cs : List (Nat × Nat)} (hMF : MemFrame M m (R.rt ++ cs))
    (hcs : ∀ q ∈ cs, sp - K ≤ q.1 ∧ q.2 ≤ sp + 456) (hLF : LiveFrame M m L1 []) (hrg : m.regions = M.regions)
    {p r : Nat} (hin : InRanges p r R.rt) (hap : ApartAll p r L1)
    (hinv : R.inv (b1 - r) (L1 ++ [(p, p + r)]) g (view R.rt (L1 ++ [(p, p + r)]) m)) :
    WC R L K g sp st zp zc s.mem m (L1 ++ [(p, p + r)]) (b1 - r) ℓ := by
  have e0 : stW m st = stW M st := hdr_keep hP h hMF hcs hLF (Nat.le_refl _) (by omega)
  have e1 : stLen m st = stLen M st := hdr_keep hP h hMF hcs hLF (by omega) (by omega)
  have e2 : stCap m st = stCap M st := hdr_keep hP h hMF hcs hLF (by omega) (by omega)
  have hx : LiveExt R L1 (L1 ++ [(p, p + r)]) :=
    LiveExt.single (by rw [show p + r - p = r by omega]; exact hin) (by rw [show p + r - p = r by omega]; exact hap)
  refine h.call hMF hLF hrg (fun a k _ o2 _ _ => cs_out hcs o2) (fun _ _ _ _ => trivial) hx hinv
    (stkOK_hdr h.sok hMF e0 e1 e2 hx) (e1.trans h.len) (Nat.le_refl _) (Or.inl ⟨e0, e2⟩)
    (fun hn => absurd ⟨e0, e2⟩ hn)

end

end FvModexp.Arm64.P2W2
