import FvModexp.Proofs.Amd64.Exp.W2Posts2

set_option autoImplicit false

/-!
# window-2 prologue (amd64): transport lemmas `rrJ → p01` through `OnePost` and `SnPost` (agent expmc s50)

Twins of the arm64 `W2OneRet` helpers (`one_rd`, `sn_rd`, `hdr_one`, `rd2`, `slot2`, `buf_apart`, `buf_facts`,
`one_facts`). The window-2 frame is `[sp - 4296, sp + 0x2a8)` (`Env`); `rrJ → snE` writes `ow sp`, the stack-nat call
writes its window `[sp - 4200, sp + 16)`, the stack header and the free part of the array.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf OneIn)

theorem apart_held' {R : RtInv} {L : List (Nat × Nat)} {p k a n : Nat} (hin : InRanges p k R.rt)
    (hap : ApartAll p k L) (hh : InRanges a n L ∨ Outside a n R.rt) : Apart a n p k := by
  have := apart_held hin hap hh; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
theorem one_rd {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g fs sp n onep a k : Nat} {M0 M1 : Memory}
    (hO : OnePost R L L1 b b1 g fs sp n M0 M1 onep) (hh : InRanges a k L ∨ Outside a k R.rt)
    (hw : Apart a k (sp - 4296) (4296 + 0x2a8)) : M1.readLE a k = M0.readLE a k := by
  have hF := hO.2.2.2.1
  have hL := hO.2.2.2.2.1
  unfold Apart at hw
  rcases hh with h | h
  · exact hL.readLE a k h trivial
  · exact hF.readLE a k (by
      simp only [ow, outside_append, outside_cons, outside_nil, and_true]
      exact ⟨h, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩)

set_option maxRecDepth 20000 in
theorem sn_rd {R : RtInv} {L1 L2 : List (Nat × Nat)} {b1 b2 g sp st k a j : Nat} {M1 M2 : Memory}
    (hS : SnPost R b1 L1 L2 b2 g sp st k M1 M2) (hok : stLen M1 st ≤ stCap M1 st)
    (hh : InRanges a j L1 ∨ Outside a j R.rt)
    (hw : Apart a j (sp - 4296) (4296 + 0x2a8)) (hst : Apart a j st 24)
    (hfr : Apart a j (stFree M1 st).1 (stFree M1 st).2) (hsp : 4296 ≤ sp) :
    M2.readLE a j = M1.readLE a j := by
  obtain ⟨-, -, -, -, -, -, -, hF, hL, -⟩ := hS
  unfold Apart at hw hst hfr
  simp only at hfr
  have h2 : Outside a j (stkWs M1 st) := by
    simp only [stkWs, outside_cons, outside_nil, and_true]; omega
  exact FvModexp.Expmc.held_readLE hh hF hL (by simp only [outside_cons, outside_nil, and_true]; omega) h2

set_option maxRecDepth 20000 in
/-- the table buffer is apart from every held object that is apart from the old free part -/
theorem buf_apart {R : RtInv} {L1 L2 : List (Nat × Nat)} {b1 b2 g sp st k a j : Nat} {M1 M2 : Memory}
    (hS : SnPost R b1 L1 L2 b2 g sp st k M1 M2) (hok : stLen M1 st ≤ stCap M1 st)
    (hh : InRanges a j L1 ∨ Outside a j R.rt)
    (hfr : stLen M1 st + StackNat.rnd k ≤ stCap M1 st → Apart a j (stFree M1 st).1 (stFree M1 st).2) :
    Apart a j (stW M2 st + 8 * stLen M1 st) (8 * k) := by
  obtain ⟨-, -, -, hsok, hlen, hkept, hfresh, -⟩ := hS
  have hr : k ≤ StackNat.rnd k := by simp only [StackNat.rnd]; omega
  by_cases hc : stLen M1 st + StackNat.rnd k ≤ stCap M1 st
  · obtain ⟨e1, e2⟩ := hkept hc
    have hfr' := hfr hc
    rw [e1]; unfold Apart at hfr' ⊢; simp only at hfr'; omega
  · obtain ⟨hin, hap⟩ := hfresh (by omega)
    have := apart_held' hin hap hh
    have hlc := hsok.2.2.2.2.2.1
    unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
/-- the table buffer's own facts at `p01` -/
theorem buf_facts {R : RtInv} {L1 L2 : List (Nat × Nat)} {b1 b2 g fs sp st n : Nat} {M1 M2 : Memory}
    (hS : SnPost R b1 L1 L2 b2 g sp st (5 * n) M1 M2) (hok : stLen M1 st ≤ stCap M1 st)
    (harr : 0 < stCap M1 st → Apart (stW M1 st) (8 * stCap M1 st) (sp - 4296) (4296 + 0x2a8) ∧
      Apart (stW M1 st) (8 * stCap M1 st) (g + 16) 8 ∧ Apart (stW M1 st) (8 * stCap M1 st) (fs - 8) 8)
    (hrt : Outside (sp - 4296) (4296 + 0x2a8) R.rt) (hgrt : Outside (g + 16) 8 R.rt) (hfrt : Outside (fs - 8) 8 R.rt)
    (hn : 0 < n) :
    M2.accessible (stW M2 st + 8 * stLen M1 st) (8 * (5 * n)) true = true ∧
    stW M2 st + 8 * stLen M1 st + 8 * (5 * n) ≤ 2 ^ 48 ∧
    (InRanges (stW M2 st + 8 * stLen M1 st) (8 * (5 * n)) L2 ∨
      Outside (stW M2 st + 8 * stLen M1 st) (8 * (5 * n)) R.rt) ∧
    Apart (stW M2 st + 8 * stLen M1 st) (8 * (5 * n)) (sp - 4296) (4296 + 0x2a8) ∧
    Apart (g + 16) 8 (stW M2 st + 8 * stLen M1 st) (8 * (5 * n)) ∧
    Apart (fs - 8) 8 (stW M2 st + 8 * stLen M1 st) (8 * (5 * n)) := by
  obtain ⟨bp, hbp⟩ : ∃ bp, bp = stW M2 st + 8 * stLen M1 st := ⟨_, rfl⟩
  rw [← hbp]
  obtain ⟨-, -, -, hsok, hlen, hkept, hfresh, -⟩ := hS
  obtain ⟨-, -, -, -, hlive, hlc2, -⟩ := hsok
  have hr : 5 * n ≤ StackNat.rnd (5 * n) := by simp only [StackNat.rnd]; omega
  have hcap : 0 < stCap M2 st := by omega
  obtain ⟨l8, lh, lacc, l48⟩ := hlive hcap
  have hsub1 : stW M2 st ≤ bp := by omega
  have hsub2 : bp + 8 * (5 * n) ≤ stW M2 st + 8 * stCap M2 st := by omega
  refine ⟨Arm64.Memory.accessible_sub M2 lacc (Or.inr rfl) hsub1 hsub2, by omega,
    lh.imp (fun h => h.sub hsub1 hsub2) (fun h => h.of_sub hsub1 hsub2), ?_, ?_, ?_⟩
  all_goals by_cases hc : stLen M1 st + StackNat.rnd (5 * n) ≤ stCap M1 st
  · obtain ⟨e1, e2⟩ := hkept hc
    obtain ⟨a1, -⟩ := harr (by omega)
    unfold Apart at a1 ⊢; rw [hbp, e1] at hsub1 hsub2 ⊢; rw [e2] at hsub2; omega
  · obtain ⟨hin, -⟩ := hfresh (by omega)
    have := out_inR hrt hin; unfold Apart; omega
  · obtain ⟨e1, e2⟩ := hkept hc
    obtain ⟨-, a2, -⟩ := harr (by omega)
    unfold Apart at a2 ⊢; rw [hbp, e1] at hsub1 hsub2 ⊢; rw [e2] at hsub2; omega
  · obtain ⟨hin, -⟩ := hfresh (by omega)
    have := out_inR hgrt hin; unfold Apart; omega
  · obtain ⟨e1, e2⟩ := hkept hc
    obtain ⟨-, -, a3⟩ := harr (by omega)
    unfold Apart at a3 ⊢; rw [hbp, e1] at hsub1 hsub2 ⊢; rw [e2] at hsub2; omega
  · obtain ⟨hin, -⟩ := hfresh (by omega)
    have := out_inR hfrt hin; unfold Apart; omega

set_option maxRecDepth 20000 in
theorem hdr_one {R : RtInv} {L L1 : List (Nat × Nat)} {b b1 g fs sp n onep st : Nat} {M0 M1 : Memory}
    (hO : OnePost R L L1 b b1 g fs sp n M0 M1 onep) (hh : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hw : Apart st 24 (sp - 4296) (4296 + 0x2a8)) :
    stW M1 st = stW M0 st ∧ stLen M1 st = stLen M0 st ∧ stCap M1 st = stCap M0 st := by
  have h3 : ∀ j, j + 8 ≤ 24 → M1.readLE (st + j) 8 = M0.readLE (st + j) 8 := fun j hj =>
    one_rd hO (hh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
      (by unfold Apart at hw ⊢; omega)
  exact ⟨by simpa using h3 0 (by omega), h3 8 (by omega), h3 16 (by omega)⟩

set_option maxRecDepth 20000 in
/-- a held object apart from the window, the stack header and the free part keeps its bytes `rrJ → p01` -/
theorem rd2 {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b b1 b2 g fs sp n onep st a k : Nat} {M0 M1 M2 : Memory}
    (hO : OnePost R L L1 b b1 g fs sp n M0 M1 onep) (hS : SnPost R b1 L1 L2 b2 g sp st (5 * n) M1 M2)
    (hsth : InRanges st 24 L ∨ Outside st 24 R.rt) (hstw : Apart st 24 (sp - 4296) (4296 + 0x2a8))
    (hlc : stLen M0 st ≤ stCap M0 st) (hsp : 4296 ≤ sp)
    (hh : InRanges a k L ∨ Outside a k R.rt) (hw : Apart a k (sp - 4296) (4296 + 0x2a8)) (hs : Apart a k st 24)
    (hfr : Apart a k (stFree M0 st).1 (stFree M0 st).2) : M2.readLE a k = M0.readLE a k := by
  obtain ⟨e1, e2, e3⟩ := hdr_one hO hsth hstw
  have hx := hO.2.1
  rw [sn_rd hS (by rw [e2, e3]; exact hlc) (hh.imp hx.inRanges_old id) hw hs (by simp only [e1, e2, e3]; exact hfr) hsp,
    one_rd hO hh hw]

set_option maxRecDepth 20000 in
/-- a frame slot of window-2 outside `ow` and the stack-nat window keeps its word `rrJ → p01` -/
theorem slot2 {R : RtInv} {L L1 L2 : List (Nat × Nat)} {b b1 b2 g fs sp n onep st K : Nat} {M0 M1 M2 : Memory}
    (hO : OnePost R L L1 b b1 g fs sp n M0 M1 onep) (hS : SnPost R b1 L1 L2 b2 g sp st (5 * n) M1 M2)
    (hsth : InRanges st 24 L ∨ Outside st 24 R.rt) (hstw : Apart st 24 (sp - 4296) (4296 + 0x2a8))
    (hfw : Apart (stFree M0 st).1 (stFree M0 st).2 (sp - 4296) (4296 + 0x2a8)) (hlc : stLen M0 st ≤ stCap M0 st)
    (hrt : Outside (sp - 4296) (4296 + 0x2a8) R.rt) (hsp : 4296 ≤ sp)
    (hK : Outside (sp + K) 8 (ow sp)) (hK1 : 0x18 ≤ K) (hK2 : K + 8 ≤ 0x2a8) :
    M2.readLE (sp + K) 8 = M0.readLE (sp + K) 8 := by
  obtain ⟨e1, e2, e3⟩ := hdr_one hO hsth hstw
  have hro : Outside (sp + K) 8 R.rt := hrt.of_sub (by omega) (by omega)
  have hF1 := hO.2.2.2.1
  have hF2 := hS.2.2.2.2.2.2.2.1
  unfold Apart at hstw hfw
  simp only at hfw
  rw [hF2.readLE _ _ ?_, hF1.readLE _ _ ?_]
  · simp only [outside_append]; exact ⟨hro, hK⟩
  · simp only [stkWs, e1, e2, e3, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hro, by omega⟩, by omega, by omega⟩

end FvModexp.Amd64.W2Pro
