import FvModexp.Proofs.Amd64.Exp.W2Ctx

set_option autoImplicit false

/-!
# window-2 (amd64): transfer lemmas for the `RR` section's `stk.nat` calls (agent expmc s53; twin of `Arm64.W2SnK` /
the second half of `Arm64.W2Sn2K`)

* `keeps_sn`: a `stk.nat(k)` call (`SnPost`, callee window `[sp - 4200, sp + 16)`) keeps the context;
* `slot_sn`, `held_sn`: frame slots and held objects through the call;
* `below_sn`: a scratch nat below the stack's length (or apart from its array) stays so and is apart from the new nat;
* `norm_of_pow`: `2^(128 n)` stored in `2n+1` limbs is normalised.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf FinEnv)

/-- the `ArrIn` half of a `stk.nat` call's post -/
theorem sn_arrIn {R : RtInv} {L L' : List (Nat × Nat)} {b b' g sp st k : Nat} {M M' : Memory} (hk : 0 < k)
    (hS : SnPost R b L L' b' g sp st k M M') : ArrIn L' st M M' := by
  obtain ⟨-, -, -, hsok', hlen', hkept, -, -, -, -, hmS⟩ := hS
  intro hne
  by_cases hc : stLen M st + StackNat.rnd k ≤ stCap M st
  · exact absurd (hkept hc) hne
  · have hr : 0 < StackNat.rnd k := by simp only [StackNat.rnd]; omega
    have := hsok'.2.2.2.2.2.1
    refine ⟨hmS (by omega), ?_⟩
    simp only [stLen, stCap] at hlen' this ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- a `stk.nat(k)` call keeps the context -/
theorem keeps_sn {R : RtInv} {L L' : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r b b' k : Nat} {ex : List (Nat × Nat)}
    {M M' : Memory} (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) (hk : 0 < k)
    (hS : SnPost R b L L' b' g sp st k M M') : Keeps R L L' g fs sp K st l0 ex M M' := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, hcap, -, hug, huf, huw, hsu, hstg, hstf, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  have hai := sn_arrIn hk hS
  obtain ⟨hxS, -, -, hsok2, hlen2, hkept, hfresh, hFS, hLS, hrgS, -⟩ := hS
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, hga, -, -, -, -, -, -, -, -, -, f6⟩ := hce0
  have hsok0 := hsok
  obtain ⟨-, -, hstacc, -, hlive, hlc, -⟩ := hsok0
  obtain ⟨-, -, laacc, -⟩ := hlive hcap
  have hr : 0 < StackNat.rnd k := by simp only [StackNat.rnd]; omega
  simp only [AW, Apart, stUp] at hstw huw hug huf hsu hga hstg hstf f6
  refine keeps_of hce hxS (by simpa only [List.append_assoc] using hFS) hLS hrgS ?_ ?_ ?_ ?_ ?_ hsok2
    (by simp only [stLen] at hlen2 ⊢; omega) ?_ ?_ hai
  · clear hstw huw hug huf hsu hga hstg hstf f6
    intro q hq hlt
    simp only [stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · simpa using hstacc
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
  · clear hstw huw hsu hstf f6 huf
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hsu hga hstg hug
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug huf hsu hga hstg hstf f6
    intro a k' ho
    obtain ⟨-, o2, o3, o4, -⟩ := ho
    simp only [AW, Apart, stUp] at o2 o3 o4
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
    omega
  · clear hug huf hsu hga hstg hstf f6
    intro j hj
    simp only [KeptJ] at hj
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug huf hsu hga hstg hstf f6
    by_cases hc : stLen M st + StackNat.rnd k ≤ stCap M st
    · exact Or.inl (hkept hc)
    · exact Or.inr (hfresh (by omega))
  · clear hstw huw hug huf hsu hga hstg hstf f6
    intro _
    by_cases hc : stLen M st + StackNat.rnd k ≤ stCap M st
    · rw [(hkept hc).2]; exact hcap
    · have := hsok2.2.2.2.2.2.1; simp only [stLen, stCap] at hlen2 this ⊢; omega

set_option maxRecDepth 20000 in
/-- a frame slot above `stk.nat`'s window (`[sp - 4200, sp + 16)`) survives the call -/
theorem slot_sn {R : RtInv} {L L' : List (Nat × Nat)} {b b' g sp K st k : Nat} {M M' : Memory}
    (hS : SnPost R b L L' b' g sp st k M M') (hrt : Outside (sp - 8 - K) (K + 688) R.rt) (hK : 4192 ≤ K)
    (hsp : K + 8 ≤ sp) (hstw : AW sp K st 24) (huw : AW sp K (stFree M st).1 (stFree M st).2)
    (j : Nat) (h1 : 16 ≤ j) (h2 : j + 8 ≤ 0x2a8) : M'.readLE (sp + j) 8 = M.readLE (sp + j) 8 := by
  obtain ⟨-, -, -, -, -, -, -, hF, -, -⟩ := hS
  refine hF.readLE _ _ ?_
  simp only [outside_append]
  refine ⟨⟨hrt.of_sub (by omega) (by omega), ?_⟩, ?_⟩
  · simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [AW, stFree, Apart] at hstw huw
    simp only [stkWs, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
/-- a held object apart from the callee window, the header and the free part survives a `stk.nat` call -/
theorem held_sn {R : RtInv} {L L' : List (Nat × Nat)} {b b' g sp K st k a c : Nat} {M M' : Memory}
    (hS : SnPost R b L L' b' g sp st k M M') (hh : Held R L a c) (hK : 4192 ≤ K) (hw : AW sp K a c)
    (hs : Apart a c st 24) (hf : Apart a c (stFree M st).1 (stFree M st).2) : M'.readLE a c = M.readLE a c := by
  obtain ⟨-, -, -, -, -, -, -, hF, hL, -⟩ := hS
  simp only [AW, stFree, Apart] at hw hs hf
  exact FvModexp.Expmc.held_readLE hh hF hL (by simp only [outside_cons, outside_nil, and_true]; omega)
    (by simp only [stkWs, outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
/-- a scratch nat below the stack's length (or apart from its array) stays so through `stk.nat(k)`, and is apart
from the new nat -/
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
  have e := Janus.Arm64.Memory.readLE_add M p (8 * (2 * n)) 8
  rw [show 8 * (2 * n) + 8 = 8 * (2 * n + 1) by omega, h, h0, Nat.mul_zero, Nat.add_zero] at e
  have hl := Janus.Arm64.Memory.readLE_lt M p (8 * (2 * n))
  have e2 : (256 : Nat) ^ (8 * (2 * n)) = 2 ^ (128 * n) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (8 * (2 * n)) = 128 * n by omega]
  rw [e2, ← e] at hl
  exact Nat.lt_irrefl _ hl

end FvModexp.Amd64.W2Pro
