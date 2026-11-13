import FvModexp.Proofs.Arm64.Nat.DivBasic
import FvModexp.Proofs.Arm64.Nat.DivDefs

set_option autoImplicit false

/-!
# `nat.div` (arm64): the postcondition when the stack is untouched (`len v = 1`, `u < v` paths; pure)

The final memory differs from the entry one only in `R.rt`, the window and the (non-empty) arrays of `z` and `z2`;
the stack header and array are then unchanged (`StackBack`'s "kept" case).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (outside_of_inRanges held_apart_fresh)

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem post_kept {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul v vl : Nat} {s : State}
    (hpre : Pre R b dc L zp zl zc st z2 z2l z2c u ul v vl s) (s' : State) {q ql qc r rl rc : Nat}
    {L' : List (Nat × Nat)} {b' : Nat}
    (h0 : s'.regs 0 = BitVec.ofNat 64 q) (h1 : s'.regs 1 = BitVec.ofNat 64 ql) (h2 : s'.regs 2 = BitVec.ofNat 64 qc)
    (h3 : s'.regs 3 = BitVec.ofNat 64 r) (h4 : s'.regs 4 = BitVec.ofNat 64 rl) (h5 : s'.regs 5 = BitVec.ofNat 64 rc)
    (hq : ExpHyp.NatOF R L L' s'.mem zp zc 1 q ql qc (natVal s.mem u ul / natVal s.mem v vl))
    (hr : ExpHyp.NatOF R L L' s'.mem z2 z2c 1 r rl rc (natVal s.mem u ul % natVal s.mem v vl))
    (hext : LiveExt R L L') (hb : b - cost dc (stLen s.mem st) ul vl ≤ b')
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem))
    (hMF : MemFrame s.mem s'.mem (R.rt ++ winA s 41504 112 ++ ar zp zc ++ ar z2 z2c))
    (hLF : LiveFrame s.mem s'.mem L (ar zp zc ++ ar z2 z2c)) :
    PostL R b dc L zp zc st z2 z2c u ul v vl s s' := by
  have hp := hpre.f
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hc40⟩ := hp.sok
  have hsw := hp.sw
  simp only [win, outside_cons, outside_nil, and_true] at hsw
  have hz := hp.pw zp zc (by simp)
  have hz2 := hp.pw z2 z2c (by simp)
  -- the stack header is unchanged
  have hhd : ∀ a n, st ≤ a → a + n ≤ st + 24 → s'.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have ho : Outside a n (ar zp zc ++ ar z2 z2c) := by
      rw [outside_append]
      refine ⟨outside_ar fun hc => ?_, outside_ar fun hc => ?_⟩
      · have := (hz hc).2.2.1; unfold Apart at this; omega
      · have := (hz2 hc).2.2.1; unfold Apart at this; omega
    rcases hsth with hin | hout
    · exact hLF.readLE a n (hin.sub h1 h2) ho
    · refine hMF.readLE a n ?_
      simp only [outside_append] at ho ⊢
      refine ⟨⟨⟨hout.of_sub h1 h2, ?_⟩, ho.1⟩, ho.2⟩
      simp only [winA, outside_cons, outside_nil, and_true]; omega
  have ew : stW s'.mem st = stW s.mem st := hhd st 8 (Nat.le_refl _) (by omega)
  have el : stLen s'.mem st = stLen s.mem st := hhd (st + 8) 8 (by omega) (by omega)
  have ec : stCap s'.mem st = stCap s.mem st := hhd (st + 16) 8 (by omega) (by omega)
  refine ⟨q, ql, qc, r, rl, rc, h0, h1, h2, h3, h4, h5, L', b', hq, hr, ⟨hext, hb, hinv⟩, ⟨⟨?sok, el, Or.inl ⟨ew, ec⟩⟩, fun hn => absurd ⟨ew, ec⟩ hn⟩,
    ?fresh, ?mf, ?lf⟩
  case sok =>
    refine ⟨hst8, hext.held hsth, by rw [hMF.accessible]; exact hstacc, hst48, ?_, by rw [el, ec]; exact hlc,
      by rw [ec]; exact hc40⟩
    rw [ew, ec]
    intro hc0
    obtain ⟨a1, a2, a3, a4⟩ := hnl hc0
    exact ⟨a1, hext.held a2, by rw [hMF.accessible]; exact a3, a4⟩
  case fresh =>
    intro hne hrc hcap
    rcases hr.2.2.2.2.2 with ⟨e1, e2⟩ | ⟨-, hrin, hrap⟩
    · exact absurd ⟨e1, e2⟩ hne
    · rw [ec] at hcap; rw [ew, ec]
      exact held_apart_fresh (hnl hcap).2.1 hrap hrin
  case mf =>
    refine hMF.mono fun a n ho => ?_
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨⟨⟨ho.1.1.1, ho.1.1.2⟩, outside_ar_of (by simp only [outside_cons, outside_nil, and_true]; exact ho.1.2.1)⟩,
      outside_ar_of (by simp only [outside_cons, outside_nil, and_true]; exact ho.1.2.2)⟩
  case lf =>
    refine ⟨fun a n hin ho => hLF.readLE a n hin ?_⟩
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    exact ⟨outside_ar_of (by simp only [outside_cons, outside_nil, and_true]; exact ho.1.1),
      outside_ar_of (by simp only [outside_cons, outside_nil, and_true]; exact ho.1.2)⟩

end FvModexp.Arm64.NatDiv
