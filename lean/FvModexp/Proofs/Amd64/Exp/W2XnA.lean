import FvModexp.Proofs.Amd64.Exp.W2XnD
import FvModexp.Proofs.Amd64.Exp.W2LshK

set_option autoImplicit false

/-!
# window-2 prologue (amd64): path A of the `x` normalisation — context pieces (agent expmc s56; twin of
`Arm64.W2XnA`, first half)

`_, x = stk.nat(len x - n + 1).div(stk, stk.nat(n), x, m)` (nat.go:1377-1379):
* `CtxX.addEx`/`CtxX.dropEx`: the scratch quotient `q` is an extra range of the context while the division runs;
* `keeps_divX`: the division (`DvPostG`, `u = x`, quotient `q` = the extra range, remainder buffer `z2` in the stack
  above the context's level) keeps the context;
* `rem_xin`: the remainder (the old `z2` buffer or a fresh object) satisfies `XIn` at the stack level after the division.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf FinEnv)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem CtxX.addEx {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {e : Nat × Nat}
    {M : Memory} (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M)
    (he : stW M st + 8 * l0 ≤ e.1 ∧ e.1 + e.2 ≤ stW M st + 8 * stCap M st) :
    CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r (e :: ex) M := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hmO, h11, h12, h13, hxO, h15, h16, hyO, h18, h19, h20, h21, h22,
    h23, hz, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, hgO, h41, h42,
    h43, h44, hcO, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, obj_addEx hmO he, h11, h12, h13, obj_addEx hxO he, h15, h16,
    obj_addEx hyO he, h18, h19, h20, h21, h22, h23,
    fun h2n => ⟨(hz h2n).1, (hz h2n).2.1, obj_addEx (hz h2n).2.2.1 he, (hz h2n).2.2.2.1, (hz h2n).2.2.2.2⟩,
    h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, obj_addEx hgO he, h41, h42,
    h43, h44, obj_addEx hcO he, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩

theorem obj_drop {R : RtInv} {L : List (Nat × Nat)} {sp K st l0 a k : Nat} {ex : List (Nat × Nat)} {e : Nat × Nat}
    {M : Memory} (h : Obj R L sp K st l0 (e :: ex) M a k) : Obj R L sp K st l0 ex M a k :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun e' he' => h.2.2.2.2 e' (List.mem_cons_of_mem _ he')⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem CtxX.dropEx {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {e : Nat × Nat}
    {M : Memory} (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r (e :: ex) M) :
    CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hmO, h11, h12, h13, hxO, h15, h16, hyO, h18, h19, h20, h21, h22,
    h23, hz, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, hgO, h41, h42,
    h43, h44, hcO, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, obj_drop hmO, h11, h12, h13, obj_drop hxO, h15, h16,
    obj_drop hyO, h18, h19, h20, h21, h22, h23,
    fun h2n => ⟨(hz h2n).1, (hz h2n).2.1, obj_drop (hz h2n).2.2.1, (hz h2n).2.2.2.1, (hz h2n).2.2.2.2⟩,
    h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, obj_drop hgO, h41, h42,
    h43, h44, obj_drop hcO, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the division `q.div(stk, z2, x, m)` keeps the context (`q` its extra range, `z2` in the stack above `l0`) -/
theorem keeps_divX {R : RtInv} {L L' : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r b b' costD stkD qp qc z2p up ul rr rl rc : Nat}
    {M M' : Memory}
    (hC : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r [(qp, 8 * qc)] M)
    (hKD : stkD ≤ K)
    (hzin : stW M st + 8 * l0 ≤ z2p ∧ z2p + 8 * n ≤ stW M st + 8 * stLen M st)
    (hqa : M.accessible qp (8 * qc) true = true) (hqW : AW sp K qp (8 * qc)) (hqG : Apart qp (8 * qc) (g + 16) 8)
    (hqF : Apart qp (8 * qc) (fs - 8) 8)
    (hD : DvPostG R b costD L L' b' g sp stkD st qp qc z2p n up ul mp n M M' rr rl rc) :
    KeepsX R L L' g fs sp K st l0 [(qp, 8 * qc)] M M' := by
  obtain ⟨-, hce, hK, -, hn, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, hcap, -, hug, huf, huw, hsu, hstg, hstf, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  obtain ⟨-, hxD, -, -, ⟨⟨hsok', hlen', hst'⟩, hai⟩, -, hF, hL, hrg⟩ := hD
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro', f1, f2, f3, f4, f5, f6⟩ := hce0
  have hsok0 := hsok
  obtain ⟨hst8, hsth', hstacc, hst48, hlive, hlc, hcap40⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  clear hLs hd hro'
  simp only [AW, Apart, stUp] at hstw huw hug huf hsu hga hstg hstf hqW hqG hqF f6
  refine keeps_ofX hce hxD (by simpa only [List.append_assoc] using hF) hL hrg ?_ ?_ ?_ ?_ ?_ hsok'
    (by omega) hst' ?_ hai
  · clear hstw huw hug huf hsu hga hstg hstf hqW hqG hqF f6
    intro r' hr' hlt
    simp only [stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · simp only at hlt ⊢; exact M.accessible_sub hqa (Or.inr rfl) (by omega) (by omega)
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
    · simpa using hstacc
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
  · clear hstw huw hsu hqW huf hstf hqF f6
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hsu hqW hug hstg hqG hga
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug huf hsu hga hstg hstf hqW hqG hqF f6
    intro a k' ho
    obtain ⟨-, o2, o3, o4, o5⟩ := ho
    have o6 := o5 _ (List.mem_singleton_self _)
    clear o5
    simp only [AW, Apart, stUp] at o2 o3 o4 o6
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
    omega
  · clear hug huf hsu hga hstg hstf hqG hqF f6
    intro j hj
    simp only [KeptJX] at hj
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug huf hsu hga hstg hstf hqW hqG hqF f6
    intro _
    have := hsok'.2.2.2.2.2.1
    simp only [stLen, stCap, stW] at hlen' this hzin ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the remainder of `x mod m` is an `XIn` operand at the stack level after the division -/
theorem rem_xin {R : RtInv} {L L' : List (Nat × Nat)}
    {g sp K st l0 n b b' costD stkD qp qc z2p xp xl mp Mv r rl rc : Nat} {M M' : Memory}
    (hrt : Outside (sp - 8 - K) (K + 688) R.rt) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hsu : Apart st 24 (stUp M st l0).1 (stUp M st l0).2)
    (hsok : StkOK M R L st) (hcap : 0 < stCap M st) (harr : AW sp K (stW M st) (8 * stCap M st))
    (hz2 : stW M st + 8 * l0 ≤ z2p ∧ z2p + 8 * n ≤ stW M st + 8 * stLen M st) (hn : 0 < n)
    (hmv : M.readLE mp (8 * n) = Mv) (hmB : Mv < Exp.B ^ n) (hM0 : 0 < Mv)
    (hD : DvPostG R b costD L L' b' g sp stkD st qp qc z2p n xp xl mp n M M' r rl rc) (hcap' : 0 < stCap M' st) :
    XIn R L' sp K st (stLen M' st) M' r rl rc ∧ M'.readLE r (8 * rl) = M.readLE xp (8 * xl) % Mv ∧ rl ≤ n ∧
      r < 2 ^ 64 := by
  obtain ⟨⟨hv, hN, hlc, hc40, hlive, hor⟩, hx, -, -, ⟨⟨hsok', hlen', hst'⟩, -⟩, hfr, -, -, -⟩ := hD
  have hsok0 := hsok
  obtain ⟨-, -, -, -, hla, hlcM, -⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hla hcap
  have hval : M'.readLE r (8 * rl) = M.readLE xp (8 * xl) % Mv := by
    have := hv; simp only [natVal] at this; rw [this, hmv]
  have hBn : Exp.B ^ n = 2 ^ (64 * n) := by
    rw [Exp.B_eq, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl, ← Nat.pow_mul]
  have hrln : rl ≤ n := norm_len_le hN (by rw [hval, ← hBn]; exact Nat.lt_trans (Nat.mod_lt _ hM0) hmB)
  have hrc0 : 0 < rc := by rcases hor with ⟨-, e⟩ | ⟨h1, -⟩ <;> omega
  obtain ⟨r8, rH, racc, r48⟩ := hlive hrc0
  refine ⟨⟨hlc, hrc0, hc40, M'.accessible_sub racc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _), r48, ?_⟩, hval, hrln,
    by omega⟩
  simp only [AW] at harr
  rcases hor with ⟨e1, e2⟩ | ⟨-, hin, hap⟩
  · -- the old `z2` buffer
    subst e1 e2
    refine ⟨rH, by simp only [AW, Apart] at harr ⊢; omega, by simp only [stUp, Apart] at hsu ⊢; omega, ?_,
      fun e he => by simp at he⟩
    rcases hst' with ⟨w1, w2⟩ | ⟨hin, hap⟩
    · simp only [stUp, Apart]; rw [w1, w2, hlen']; omega
    · have := apart_fresh (a := r) (n := 8 * rc) hin hap (held_sub lah (by omega) (by omega))
      simp only [stUp, Apart] at this ⊢; omega
  · -- a fresh object
    have hne : ¬ (r = z2p ∧ rc = n) := by
      intro ⟨e1, e2⟩
      rw [e1, e2] at hin hap
      have := apart_fresh (a := z2p) (n := 8 * n) hin hap (held_sub lah (by omega) (by omega))
      unfold Apart at this; omega
    have h1 := hfr hne hrc0 hcap'
    have h2 := out_inR hrt hin
    have h3 := apart_fresh hin hap hsth
    refine ⟨rH, by simp only [AW, Apart]; omega, by unfold Apart at h3 ⊢; omega, ?_, fun e he => by simp at he⟩
    have := hsok'.2.2.2.2.2.1
    simp only [stUp, Apart] at h1 ⊢; omega

end FvModexp.Amd64.W2Pro
