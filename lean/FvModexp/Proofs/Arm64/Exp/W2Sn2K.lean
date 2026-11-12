import FvModexp.Proofs.Arm64.Exp.W2Ctx

/-!
# window-2 prologue (arm64): transfer lemmas for the `RR` section's own spills and `stk.nat` calls

* `keeps_own`: the frame's own stores inside `[sp+8, sp+752)` (off the kept slots) keep the context;
* `slot_sn`, `held_sn`: frame slots and held objects through a `stk.nat` call;
* `below_sn`: a scratch nat of the stack (below the current length, or apart from the array) stays so, and is apart
  from the new stack nat;
* `norm_of_pow`: `2^(128 n)` stored in `2n+1` limbs is normalised.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf FinEnv)

theorem outside_ws_of_win {a k lo hi : Nat} (h : a + k ≤ lo ∨ hi ≤ a) :
    ∀ {ws : List (Nat × Nat)}, (∀ r ∈ ws, lo ≤ r.1 ∧ r.2 ≤ hi) → Outside a k ws
  | [], _ => trivial
  | (l1, h1) :: ws, hin => by
    have := hin (l1, h1) (List.mem_cons_self ..)
    simp only at this
    exact ⟨by omega, outside_ws_of_win h (fun r hr => hin r (List.mem_cons_of_mem _ hr))⟩

theorem stkOK_frame {R : RtInv} {L : List (Nat × Nat)} {st : Nat} {M M' : Memory} (h : StkOK M R L st)
    (e0 : M'.readLE st 8 = M.readLE st 8) (e1 : M'.readLE (st + 8) 8 = M.readLE (st + 8) 8)
    (e2 : M'.readLE (st + 16) 8 = M.readLE (st + 16) 8) (hacc : ∀ a k w, M'.accessible a k w = M.accessible a k w) :
    StkOK M' R L st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [StkOK, stW, stLen, stCap, NatLive] at h5 h6 h7 ⊢
  rw [e0, e1, e2, hacc, hacc]
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the frame's own stores keep the context -/
theorem keeps_own {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)}
    {M M' : Memory} (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 ex M)
    {ws : List (Nat × Nat)} (hF : MemFrame M M' ws) (hreg : M'.regions = M.regions)
    (hin : ∀ r ∈ ws, sp + 8 ≤ r.1 ∧ r.2 ≤ sp + 752)
    (hsl : ∀ j, (128 ≤ j ∧ j + 8 ≤ 136 ∨ 224 ≤ j ∧ j + 8 ≤ 232 ∨ 320 ≤ j ∧ j + 8 ≤ 336 ∨ 536 ≤ j ∧ j + 8 ≤ 752) →
      Outside (sp + j) 8 ws) :
    Keeps R L L g sp K st l0 ex M M' := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce0
  have hin' : ∀ r ∈ ws, sp - K ≤ r.1 ∧ r.2 ≤ sp + 752 := fun r hr => by have := hin r hr; omega
  have ow : ∀ a k, Apart a k (sp - K) (K + 752) → Outside a k ws := fun a k h =>
    outside_ws_of_win (by unfold Apart at h; omega) hin'
  have hst : Apart st 24 (sp - K) (K + 752) := hstw
  have e0 := hF.readLE st 8 (ow _ _ (hst.mono (by omega) (Nat.le_refl _)))
  have e1 := hF.readLE (st + 8) 8 (ow _ _ (hst.sub (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)))
  have e2 := hF.readLE (st + 16) 8 (ow _ _ (hst.sub (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)))
  have hsok' := stkOK_frame hsok e0 e1 e2 (fun a k w => hF.accessible a k w)
  refine keeps_of hce hK (LiveExt.refl R L) (FvModexp.Expmc.frame_widen_rt hF)
    (FvModexp.Expmc.liveFrame_of_frame (ws := ([] : List (Nat × Nat))) hF (fun a k hin2 _ => ?_)) hreg ?_ ?_ (fun a k ho => ⟨ow _ _ ho.2.1, trivial⟩)
    hsl (outside_ws_of_win (lo := sp + 8) (hi := sp + 752) (by omega) hin)
    (outside_ws_of_win (lo := sp + 8) (hi := sp + 752) (by omega) hin) hsok'
    (by simp only [stLen]; rw [e1]; exact Nat.le_refl _) (Or.inl ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
    (fun h => by simp only [stCap] at h ⊢; rw [e2]; exact h)
  · obtain ⟨r, hr, h1, h2⟩ := hin2
    have := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at this
    exact outside_ws_of_win (lo := sp - K) (hi := sp + 752) (by omega) hin'
  · intro r hr hlt
    have := hin r hr
    exact M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)
  · exact outside_ws_of_win (by unfold Apart at hga; omega) hin'

set_option maxRecDepth 20000 in
/-- a frame slot above `stk.nat`'s spill area survives the call -/
theorem slot_sn {R : RtInv} {L L' : List (Nat × Nat)} {b b' g sp st k : Nat} {M M' : Memory}
    (hS : SnPost R b L L' b' g sp st k M M') (hrt : Outside (sp - 4304) (4304 + 752) R.rt) (h4 : 4304 ≤ sp)
    (hstw : Apart st 24 (sp - 4304) (4304 + 752))
    (huw : Apart (stFree M st).1 (stFree M st).2 (sp - 4304) (4304 + 752))
    (j : Nat) (h1 : 24 ≤ j) (h2 : j + 8 ≤ 752) : M'.readLE (sp + j) 8 = M.readLE (sp + j) 8 := by
  obtain ⟨-, -, -, -, -, -, -, hF, -, -⟩ := hS
  refine hF.readLE _ _ ?_
  simp only [outside_append]
  refine ⟨⟨hrt.of_sub (by omega) (by omega), ?_⟩, ?_⟩
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [stFree, Apart] at hstw huw
    simp only [stkWs, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
/-- a held object apart from the frame, the header and the free part survives a `stk.nat` call -/
theorem held_sn {R : RtInv} {L L' : List (Nat × Nat)} {b b' g sp st k a c : Nat} {M M' : Memory}
    (hS : SnPost R b L L' b' g sp st k M M') (hh : Held R L a c) (hw : Apart a c (sp - 4304) (4304 + 752))
    (hs : Apart a c st 24) (hf : Apart a c (stFree M st).1 (stFree M st).2) : M'.readLE a c = M.readLE a c := by
  obtain ⟨-, -, -, -, -, -, -, hF, hL, -⟩ := hS
  simp only [stFree, Apart] at hw hs hf
  exact FvModexp.Expmc.held_readLE hh hF hL (by simp only [outside_cons, outside_nil, and_true]; omega)
    (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
/-- a scratch nat below the stack's length (or apart from its array) stays so through `stk.nat(k)`, and is apart from
the new nat -/
theorem below_sn {R : RtInv} {L L' : List (Nat × Nat)} {b b' g sp st k l0 p c : Nat} {M M' : Memory}
    (hS : SnPost R b L L' b' g sp st k M M') (hh : Held R L p c)
    (hB : (stW M st + 8 * l0 ≤ p ∧ p + c ≤ stW M st + 8 * stLen M st) ∨ Apart p c (stW M st) (8 * stCap M st)) :
    ((stW M' st + 8 * l0 ≤ p ∧ p + c ≤ stW M' st + 8 * stLen M' st) ∨ Apart p c (stW M' st) (8 * stCap M' st)) ∧
    Apart p c (stW M' st + 8 * stLen M st) (8 * k) := by
  obtain ⟨-, -, -, hsok', hlen', hkept, hfresh, -, -, -⟩ := hS
  have hlc' := hsok'.2.2.2.2.2.1
  have hr : k ≤ StackNat.rnd k := by simp only [StackNat.rnd]; omega
  by_cases hc : stLen M st + StackNat.rnd k ≤ stCap M st
  · obtain ⟨e1, e2⟩ := hkept hc
    simp only [stW, stLen, stCap] at e1 e2 hlen' hB hc hlc' ⊢
    rw [e1, e2]
    rcases hB with h | h
    · exact ⟨Or.inl ⟨h.1, by omega⟩, by unfold Apart; omega⟩
    · exact ⟨Or.inr h, by unfold Apart at h ⊢; omega⟩
  · obtain ⟨hin, hap⟩ := hfresh (by omega)
    have := apart_held' hin hap hh
    simp only [stW, stLen, stCap] at this hlen' hlc' ⊢
    exact ⟨Or.inr (by unfold Apart at this ⊢; omega), by unfold Apart at this ⊢; omega⟩

/-- `2^(128 n)` in `2n+1` limbs is normalised -/
theorem norm_of_pow {M : Memory} {p n : Nat} (h : M.readLE p (8 * (2 * n + 1)) = 2 ^ (128 * n)) :
    NatNorm M p (2 * n + 1) := by
  right
  intro h0
  rw [show 2 * n + 1 - 1 = 2 * n by omega] at h0
  have e := M.readLE_add p (8 * (2 * n)) 8
  rw [show 8 * (2 * n) + 8 = 8 * (2 * n + 1) by omega, h, h0, Nat.mul_zero, Nat.add_zero] at e
  have hl := M.readLE_lt p (8 * (2 * n))
  have e2 : (256 : Nat) ^ (8 * (2 * n)) = 2 ^ (128 * n) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * (2 * n)) = 128 * n by omega]
  rw [e2, ← e] at hl
  exact Nat.lt_irrefl _ hl

end FvModexp.Arm64.W2Pro
