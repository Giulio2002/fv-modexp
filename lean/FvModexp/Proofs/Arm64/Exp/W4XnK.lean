import FvModexp.Proofs.Arm64.Exp.W4CtxB

/-!
# window-4 prologue (arm64): context transfer for the `x` normalisation

* `keeps_snB`: a `stk.nat(k)` call keeps `CtxB` (copy of `keeps_sn` for the context without `x`);
* `CtxB.raise`: the context's stack level `l0` may be raised up to the current stack length (the part of the array
  above the new level is a sub-range of the part above the old one).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf FinEnv)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- a `stk.nat(k)` call keeps the context without `x` -/
theorem keeps_snB {R : RtInv} {L L' : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret b b' k : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)}
    {M M' : Memory}
    (hC : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M) (hk : 0 < k)
    (hS : SnPost R b L L' b' g sp st k M M') : KeepsB R L L' g sp K st l0 ex M M' := by
  obtain ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmV, hnm, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, hgO, hstwb, hro, hty,
    r1016, r1024, r1032, r952, r936, r1000, r992, r960⟩ := hC
  obtain ⟨hxS, hbS, hinvS, hsok2, hlen2, hkept, hfresh, hFS, hLS, hrgS⟩ := hS
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro'⟩ := hce0
  have hsok0 := hsok
  obtain ⟨hst8, hsth', hstacc, hst48, hlive, hlc, hcap40⟩ := hsok0
  obtain ⟨la8, lah, laacc, la48⟩ := hlive hcap
  have hr : 0 < StackNat.rnd k := by simp only [StackNat.rnd]; omega
  have hstg := hfe.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [AW, Apart, stUp] at hstw huw hug hsu hga hstg
  clear hLs hd hro' hfe hm hmO hy hyO hz hgl hgO
  refine keeps_ofB hce hK hxS (by simpa only [List.append_assoc] using hFS) hLS hrgS ?_ ?_ ?_ ?_ ?_ ?_ hsok2
    (by omega) ?_ ?_
  · clear hstw huw hug hsu hga hstg
    intro r hr' hlt
    simp only [stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · exact M.accessible_sub hacc (Or.inr rfl) (by simp only; omega) (by simp only; omega)
    · simpa using hstacc
    · simp only at hlt ⊢; exact M.accessible_sub laacc (Or.inr rfl) (by omega) (by omega)
  · clear hstw huw hsu
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug hsu hga hstg
    intro a k' ho
    obtain ⟨-, o2, o3, o4, -⟩ := ho
    simp only [AW, Apart, stUp] at o2 o3 o4
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]
    omega
  · clear hug hsu hga hstg
    intro j hj
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hug hsu hga hstg
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hug hsu hga hstg
    simp only [stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega
  · clear hstw huw hug hsu hga hstg
    by_cases hc : stLen M st + StackNat.rnd k ≤ stCap M st
    · exact Or.inl (hkept hc)
    · exact Or.inr (hfresh (by omega))
  · clear hstw huw hug hsu hga hstg
    intro _
    by_cases hc : stLen M st + StackNat.rnd k ≤ stCap M st
    · rw [(hkept hc).2]; exact hcap
    · have := hsok2.2.2.2.2.2.1; simp only [stLen, stCap] at hlen2 this ⊢; omega

theorem stUp_raise {a k st l0 l1 : Nat} {M : Memory} (h : Apart a k (stUp M st l0).1 (stUp M st l0).2)
    (hl : l0 ≤ l1) (hl1 : l1 ≤ stCap M st) : Apart a k (stUp M st l1).1 (stUp M st l1).2 := by
  simp only [stUp, Apart] at h ⊢; omega

theorem stUp_raise' {a k st l0 l1 : Nat} {M : Memory} (h : Apart (stUp M st l0).1 (stUp M st l0).2 a k)
    (hl : l0 ≤ l1) (hl1 : l1 ≤ stCap M st) : Apart (stUp M st l1).1 (stUp M st l1).2 a k := by
  simp only [stUp, Apart] at h ⊢; omega

theorem obj_raise {R : RtInv} {L : List (Nat × Nat)} {sp K st l0 l1 a k : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : Obj R L sp K st l0 ex M a k) (hl : l0 ≤ l1) (hl1 : l1 ≤ stCap M st) : Obj R L sp K st l1 ex M a k :=
  ⟨h.1, h.2.1, h.2.2.1, stUp_raise h.2.2.2.1 hl hl1, h.2.2.2.2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem CtxB.raise {R : RtInv} {L : List (Nat × Nat)}
    {g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret : Nat} {r29 : BitVec 64} {ex : List (Nat × Nat)}
    {M : Memory} (h : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 ex M) {l1 : Nat}
    (hl : l0 ≤ l1) (hl1 : l1 ≤ stLen M st) :
    CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l1 ret r29 ex M := by
  obtain ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmV, hnm, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huw, hsu, hgl, hgO, hstwb, hro, hty,
    r1016, r1024, r1032, r952, r936, r1000, r992, r960⟩ := h
  have hc : l1 ≤ stCap M st := Nat.le_trans hl1 hsok.2.2.2.2.2.1
  exact ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, obj_raise hmO hl hc, hmV, hnm, hy, obj_raise hyO hl hc, hY, hyi,
    hyi0, hyl, hyl', hzc,
    fun h2 => ⟨(hz h2).1, (hz h2).2.1, obj_raise (hz h2).2.2.1 hl hc, (hz h2).2.2.2.1, (hz h2).2.2.2.2⟩,
    hfe, hsth, hstw, hsok, by omega, hl1, hcap, harr, stUp_raise' hug hl hc, stUp_raise' huw hl hc, stUp_raise hsu hl hc, hgl, obj_raise hgO hl hc, hstwb, hro, hty,
    r1016, r1024, r1032, r952, r936, r1000, r992, r960⟩

end FvModexp.Arm64.W4Pro
