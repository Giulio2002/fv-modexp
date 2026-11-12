import FvModexp.Proofs.Arm64.Exp.W2DivK
import FvModexp.Proofs.Arm64.Exp.W2Lsh
import FvModexp.Proofs.Arm64.Exp.W2Sn2K

/-!
# window-2 prologue (arm64): transfer lemmas around `zz := nil.lsh(RR, 128 n)`

* `keeps_own2`: own stores in the frame plus one word of the scratch `RR` (an extra range of the context);
* `keeps_lsh`: the `lsh` call keeps the context;
* `zz_of_lsh`: the fresh result `zz = 2^(128 n)` has `2n+1` limbs and satisfies `ZZ`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf FinEnv)

theorem stkOK_ext {R : RtInv} {L L' : List (Nat × Nat)} {st : Nat} {M : Memory} (hx : LiveExt R L L')
    (h : StkOK M R L st) : StkOK M R L' st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, hx.held h2, h3, h4, fun hc => ?_, h6, h7⟩
  obtain ⟨a, b, c, d⟩ := h5 hc
  exact ⟨a, hx.held b, c, d⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- own stores in the frame and one word `[p, p+8)` of an extra range keep the context -/
theorem keeps_own2 {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)}
    {M M' : Memory} (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 ex M)
    {ws : List (Nat × Nat)} {p : Nat} (hF : MemFrame M M' (ws ++ [(p, p + 8)])) (hreg : M'.regions = M.regions)
    (hin : ∀ r ∈ ws, sp + 8 ≤ r.1 ∧ r.2 ≤ sp + 752)
    (hsl : ∀ j, (128 ≤ j ∧ j + 8 ≤ 136 ∨ 224 ≤ j ∧ j + 8 ≤ 232 ∨ 320 ≤ j ∧ j + 8 ≤ 336 ∨ 536 ≤ j ∧ j + 8 ≤ 752) →
      Outside (sp + j) 8 ws)
    (hp : ∀ a k, Obj R L sp K st l0 ex M a k → Apart a k p 8) (hpw : AW sp K p 8) (hpg : Apart p 8 (g + 16) 8)
    (hps : Apart p 8 st 24) (hpa : M.accessible p 8 true = true) :
    Keeps R L L g sp K st l0 ex M M' ∧ stW M' st = stW M st ∧ stLen M' st = stLen M st ∧ stCap M' st = stCap M st := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce0
  have hin' : ∀ r ∈ ws, sp - K ≤ r.1 ∧ r.2 ≤ sp + 752 := fun r hr => by have := hin r hr; omega
  simp only [AW, Apart] at hpw hpg hps hstw hga
  have ow : ∀ a k, a + k ≤ sp - K ∨ sp + 752 ≤ a → a + k ≤ p ∨ p + 8 ≤ a → Outside a k (ws ++ [(p, p + 8)]) :=
    fun a k h1 h2 => by
      rw [outside_append]
      exact ⟨outside_ws_of_win h1 hin', by simp only [outside_cons, outside_nil, and_true]; exact h2⟩
  have e0 := hF.readLE st 8 (ow _ _ (by omega) (by omega))
  have e1 := hF.readLE (st + 8) 8 (ow _ _ (by omega) (by omega))
  have e2 := hF.readLE (st + 16) 8 (ow _ _ (by omega) (by omega))
  have hsok' := stkOK_frame hsok e0 e1 e2 (fun a k w => hF.accessible a k w)
  refine ⟨?_, e0, e1, e2⟩
  refine keeps_of hce hK (LiveExt.refl R L) (FvModexp.Expmc.frame_widen_rt hF)
    (FvModexp.Expmc.liveFrame_of_frame (ws := [(p, p + 8)]) hF (fun a k hin2 hout => ?_)) hreg ?_
    (ow _ _ (by omega) (by omega)) (fun a k ho => ?_) (fun j hj => ?_)
    (by rw [outside_append]; exact ⟨outside_ws_of_win (lo := sp + 8) (hi := sp + 752) (by omega) hin,
      by simp only [outside_cons, outside_nil, and_true]; omega⟩)
    (by rw [outside_append]; exact ⟨outside_ws_of_win (lo := sp + 8) (hi := sp + 752) (by omega) hin,
      by simp only [outside_cons, outside_nil, and_true]; omega⟩) hsok'
    (by simp only [stLen]; rw [e1]; exact Nat.le_refl _) (Or.inl ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
    (fun h => by simp only [stCap] at h ⊢; rw [e2]; exact h)
  · obtain ⟨r, hr, h1, h2⟩ := hin2
    have := hLs r hr
    simp only [outside_cons, outside_nil, and_true] at this hout
    exact ow _ _ (by omega) hout
  · intro r hr hlt
    rcases List.mem_append.1 hr with hr | hr
    · have := hin r hr
      exact M.accessible_sub hacc (Or.inr rfl) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr; simpa using hpa
  · have h1 := ho.2.1; have h2 := hp a k ho
    simp only [AW, Apart] at h1 h2
    exact ⟨ow _ _ (by omega) (by omega), by simp only [outside_cons, outside_nil, and_true]; omega⟩
  · rw [outside_append]
    exact ⟨hsl j hj, by simp only [outside_cons, outside_nil, and_true]; omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the `lsh` call keeps the context -/
theorem keeps_lsh {R : RtInv} {L L' : List (Nat × Nat)}
    {g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret b b' stkL rrp p l c : Nat} {r29 : BitVec 64}
    {ex : List (Nat × Nat)} {M M' : Memory}
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 ex M) (hKL : stkL ≤ K)
    (hD : LsPost R b L L' b' g sp stkL rrp n M M' p l c) :
    Keeps R L L' g sp K st l0 ex M M' ∧ stW M' st = stW M st ∧ stLen M' st = stLen M st ∧ stCap M' st = stCap M st := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, hsth, hstw, hsok, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  obtain ⟨-, -, hx, -, -, hF, hL, hrg⟩ := hD
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce0
  have hF' : MemFrame M M' (R.rt ++ ([(sp - stkL, sp - 8), (sp + 8, sp + 64)] ++ [(0, 0 + 8 * 0)])) := by
    simpa only [List.append_assoc] using hF
  simp only [AW, Apart] at hstw hga
  have rd : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    FvModexp.Expmc.held_readLE (hsth.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
      hF hL (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  have e0 := rd 0 (by omega)
  rw [Nat.add_zero] at e0
  have e1 := rd 8 (by omega)
  have e2 := rd 16 (by omega)
  have hsok' := stkOK_ext hx (stkOK_frame hsok e0 e1 e2 (fun a k w => hF.accessible a k w))
  refine ⟨?_, e0, e1, e2⟩
  refine keeps_of hce hK hx hF' hL hrg ?_ ?_ (fun a k ho => ?_) (fun j hj => ?_) ?_ ?_ hsok'
    (by simp only [stLen]; rw [e1]; exact Nat.le_refl _) (Or.inl ⟨by simp only [stW]; rw [e0], by simp only [stCap]; rw [e2]⟩)
    (fun h => by simp only [stCap] at h ⊢; rw [e2]; exact h)
  · intro r hr hlt
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · simp at hlt
  · simp only [List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · have h1 := ho.2.1
    simp only [AW, Apart] at h1
    exact ⟨by simp only [List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega,
      by simp only [outside_cons, outside_nil, and_true]; omega⟩
  · simp only [List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · simp only [List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · simp only [List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the fresh `zz = 2^(128 n)` (`2n+1` limbs) after `lsh` -/
theorem zz_of_lsh {R : RtInv} {L L' : List (Nat × Nat)}
    {g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret b b' stkL rrp p l c : Nat} {r29 : BitVec 64}
    {M M' : Memory}
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 [(rrp, 8 * (2 * n))] M)
    (hrH : Held R L rrp (8 * (2 * n))) (hv1 : M.readLE rrp 8 = 1)
    (e0 : stW M' st = stW M st) (e2 : stCap M' st = stCap M st)
    (hD : LsPost R b L L' b' g sp stkL rrp n M M' p l c) :
    l = 2 * n + 1 ∧ ZZ R L' g sp n mp xp yp ylen zp zc st l0 p c M' ∧ AW sp K p (8 * c) ∧ 2 * n + 1 ≤ c ∧
    M'.readLE p (8 * (2 * n + 1)) = 2 ^ (128 * n) ∧ Apart p (8 * c) rrp (8 * (2 * n)) ∧ c < 2 ^ 40 := by
  obtain ⟨-, hce, hK, -, hn, -, -, -, hm, -, -, -, hx, -, -, hy, -, -, -, -, -, -,
    -, hz, -, hsth, -, hsok, -, hl0, hcap, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  obtain ⟨⟨hv, hN, hlc, hc40, hlive, -, hfr⟩, hneed, -, -, -, -, -, -⟩ := hD
  have hce0 := hce
  obtain ⟨-, -, -, -, -, -, -, hrt, -, hgrt, -, -, -⟩ := hce0
  have hc : 2 * n + 2 ≤ c := by have := hneed (by omega); omega
  obtain ⟨hin, hap⟩ := hfr (by omega) (by omega)
  obtain ⟨p8, pH, pacc, p48⟩ := hlive (by omega)
  have hval : M'.readLE p (8 * l) = 2 ^ (128 * n) := by
    simp only [natVal] at hv; rw [hv, show 8 * 1 = 8 from rfl, hv1, Nat.one_mul]
  have hl1 : l ≤ 2 * n + 1 :=
    norm_len_le hN (by rw [hval]; exact Nat.pow_lt_pow_right (by decide) (by omega))
  have hl2 : 2 * n + 1 ≤ l := by
    refine Nat.not_lt.1 fun hlt => ?_
    have := M'.readLE_lt p (8 * l)
    rw [hval, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 8 * (8 * l) ≤ 128 * n by omega)
    omega
  have hl : l = 2 * n + 1 := by omega
  have ap : ∀ a k, Held R L a k → Apart a k p (8 * c) := fun a k h => apart_held' hin hap h
  have hw := out_inR hrt hin
  have hg := out_inR hgrt hin
  obtain ⟨-, aH, -, -⟩ := hsok.2.2.2.2.1 hcap
  have hsA := ap _ _ aH
  have hmA := ap _ _ hm.2.2.1
  have hxA := ap _ _ hx.2.2.1
  have hyA := ap _ _ hy.2.2.1
  have hstA := ap _ _ hsth
  have hrA := ap _ _ hrH
  refine ⟨hl, ⟨⟨by omega, hc40, pacc, p48, pH, by unfold Apart; omega, by unfold Apart; omega⟩, p8, hmA.symm, hyA.symm,
    hxA.symm, by unfold Apart; omega, hstA.symm, ?_, fun h2 => ap _ _ (hz h2).1.2.2.2.2.1⟩, by simp only [AW, Apart]; omega,
    by omega, by rw [← hl]; exact hval, hrA.symm, hc40⟩
  simp only [stUp]; rw [e0, e2]
  unfold Apart at hsA ⊢
  have := hsok.2.2.2.2.2.1
  omega

end FvModexp.Arm64.W2Pro
