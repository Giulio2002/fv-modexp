import FvModexp.Proofs.Arm64.Exp.NNilC
import FvModexp.Proofs.Arm64.Exp.NNilG
import FvModexp.Proofs.Arm64.Exp.NNilJ

/-!
# `nat.expNN` (arm64), `stk == nil`: from the `Get` return to the downstream chain

`Mg` = the memory at the `Get` call (after the spills of `stkNil`), `m` = the memory at `Get`'s return.
* `k2T`: `Get` returned a pooled stack: `getT` (record, reloads, join) → `contR` | `contD` (`newStk_T`).
* `k2N`: `Get` returned nil: `getN` → `noCallN` (`newobject`) → `joinN` → `contR` | `contD` (`newStk_N`).
`chain`: the frame of `s.mem → …` (`R.rt` and the window, live set kept) composed with one more step.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

theorem chain {R : RtInv} {L : List (Nat × Nat)} {sp K : Nat} {A B C : Memory} {ws : List (Nat × Nat)}
    (h1 : MemFrame A B (R.rt ++ wN sp K) ∧ LiveFrame A B L [])
    (h2 : MemFrame B C (R.rt ++ ws)) (h2l : LiveFrame B C L [])
    (hsub : ∀ a k, Outside a k (wN sp K) → Outside a k ws) :
    MemFrame A C (R.rt ++ wN sp K) ∧ LiveFrame A C L [] :=
  ⟨h1.1.trans h2 fun a k ho => by
      simp only [outside_append] at ho ⊢; exact ⟨⟨ho.1, ho.2⟩, ho.1, hsub _ _ ho.2⟩,
    h1.2.trans h2l fun _ _ h => h⟩

/-- a window-only step -/
theorem chainW {R : RtInv} {L : List (Nat × Nat)} {sp K : Nat} {A B C : Memory} {ws : List (Nat × Nat)}
    (h1 : MemFrame A B (R.rt ++ wN sp K) ∧ LiveFrame A B L []) (h2 : MemFrame B C ws)
    (hLs : LiveSep L [(sp - K, sp + 1432)]) (hws : ∀ r ∈ ws, sp - K ≤ r.1 ∧ r.2 ≤ sp + 1432)
    (hsub : ∀ a k, Outside a k (wN sp K) → Outside a k ws) :
    MemFrame A C (R.rt ++ wN sp K) ∧ LiveFrame A C L [] :=
  chain h1 (h2.widen R.rt) (LiveFrame.of_win h2 fun r hr => by
    have := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at this
    exact outside_of_forall fun w hw => by have := hws w hw; omega) hsub

/-- the callee window of the `Get`/`newobject` calls lies in the window -/
theorem sub_cw {sp K : Nat} (hK : 4304 ≤ K) (hKs : K ≤ sp) :
    ∀ a k, Outside a k (wN sp K) → Outside a k [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)] :=
  fun a k ho => by simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega

theorem sub_slots {sp K : Nat} (hKs : K ≤ sp) :
    ∀ a k, Outside a k (wN sp K) → Outside a k [(sp + 1182, sp + 1184), (sp + 1272, sp + 1288), (sp + 1296, sp + 1304)] :=
  fun a k ho => by simp only [wN, outside_cons, outside_nil, and_true] at ho ⊢; omega

theorem slots_rt {R : RtInv} {sp K : Nat} (hKs : K ≤ sp) (hwout : Outside (sp - K) (K + 1432) R.rt) :
    ∀ r ∈ [(sp + 1182, sp + 1184), (sp + 1272, sp + 1288), (sp + 1296, sp + 1304)], Outside r.1 (r.2 - r.1) R.rt := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hwout.of_sub (by simp only; omega) (by simp only; omega)

theorem slots_win {sp K : Nat} (hKs : K ≤ sp) :
    ∀ r ∈ [(sp + 1182, sp + 1184), (sp + 1272, sp + 1288), (sp + 1296, sp + 1304)], sp - K ≤ r.1 ∧ r.2 ≤ sp + 1432 := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨by simp only; omega, by simp only; omega⟩

/-- reads of the frame slots above the callee window survive a call frame `R.rt ++ cw` -/
theorem rd_cw {R : RtInv} {sp K : Nat} {A B : Memory} (hK : 4304 ≤ K) (hKs : K ≤ sp)
    (hwout : Outside (sp - K) (K + 1432) R.rt)
    (h : MemFrame A B (R.rt ++ [(sp + 1056 - 4096, sp + 1048), (sp + 1064, sp + 1072)])) (a k : Nat)
    (ha : (sp + 1048 ≤ a ∧ a + k ≤ sp + 1064) ∨ (sp + 1072 ≤ a ∧ a + k ≤ sp + 1432)) : B.readLE a k = A.readLE a k := by
  refine h.readLE a k ?_
  rw [outside_append]
  refine ⟨hwout.of_sub (by omega) (by omega), ?_⟩
  simp only [outside_cons, outside_nil, and_true]; omega

/-- reads in the window outside the record slots survive the record's stores -/
theorem rd_sl {sp : Nat} {A B : Memory}
    (h : MemFrame A B [(sp + 1182, sp + 1184), (sp + 1272, sp + 1288), (sp + 1296, sp + 1304)]) (a k : Nat)
    (ha : a + k ≤ sp + 1182 ∨ (sp + 1184 ≤ a ∧ a + k ≤ sp + 1272) ∨ (sp + 1304 ≤ a)) : B.readLE a k = A.readLE a k :=
  h.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)

end FvModexp.Arm64.ExpN
