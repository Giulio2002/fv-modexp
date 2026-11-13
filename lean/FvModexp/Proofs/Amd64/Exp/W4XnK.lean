import FvModexp.Proofs.Amd64.Exp.W4CtxX
import FvModexp.Proofs.Amd64.Exp.W4SnK
import FvModexp.Proofs.Amd64.Exp.W4SnP

set_option autoImplicit false

/-!
# window-4 prologue (amd64): context transfer for the `x` normalisation (agent expmc s55; twin of `Arm64.W4XnK`)

Before `x` is normalised the context is `CtxX` with `x := m` (`xp := mp`, `Xv := Mv`: `m` is a context object of `n`
words, so this carries no information about `x`); `CtxX.setX` installs the normalised `x` at the join `xJ`.
* `snPre_ofX`, `keeps_snX`: a `stk.nat(k)` call from `CtxX` (copies of `snPre_of` / `keeps_sn`);
* `CtxX.raise`: the context's stack level may be raised up to the current stack length;
* `XIn`: the not yet normalised `x` (its array `[xp, xp + 8 xr)`, `xl ≤ xr`), an object of the context.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf FinEnv)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the `stk.nat(k)` call's pre from the context -/
theorem snPre_ofX {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r k : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (hC : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) (hserv : RunIface.Serves R)
    (hk16 : k ≤ 2 ^ 16) (hl : stLen M st + k + 3 ≤ 2 ^ 16) (hc : stackNatCost (stLen M st) k ≤ b)
    (hinv : R.inv b L g (view R.rt L M)) : SnPre R b L g fs sp st k M := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, -, harr, -, -, -, hsu, -, -, -, -, hstwb, hwba,
    -, -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  exact ⟨CallW.CEnv.mono hce (by omega) (Nat.le_refl _), hserv, hsok, aw_w4 hK hstw,
    fun h => ⟨aw_w4 hK (harr h).1, (harr h).2.1⟩, hk16, hl, hc, hinv, hwba, hstwb,
    free_of_up hsu hl0 hsok.2.2.2.2.2.1⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- a `stk.nat(k)` call keeps the context -/
theorem keeps_snX {R : RtInv} {L L' : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r b b' k : Nat} {ex : List (Nat × Nat)}
    {M M' : Memory} (hC : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) (hk : 0 < k)
    (hS : SnPost R b L L' b' g sp st k M M') : KeepsX R L L' g fs sp K st l0 ex M M' := by
  obtain ⟨-, hce, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hstw, hsok, -, hl0, hcap, -, hug, huf, huw, hsu, hstg, hstf, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  have hai := sn_arrIn hk hS
  obtain ⟨hxS, -, -, hsok2, hlen2, hkept, hfresh, hFS, hLS, hrgS, -⟩ := hS
  have hce0 := hce
  obtain ⟨hal, hK0, hA, hacc, -, -, -, hrt, hga, -, -, -, -, -, -, -, -, -, f6⟩ := hce0
  have hsok0 := hsok
  obtain ⟨-, -, hstacc, -, hlive, hlc, -⟩ := hsok0
  obtain ⟨-, -, laacc, -⟩ := hlive hcap
  have hr : 0 < StackNat.rnd k := by simp only [StackNat.rnd]; omega
  simp only [AW, Apart, stUp] at hstw huw hug huf hsu hga hstg hstf f6
  refine keeps_ofX hce hxS (by simpa only [List.append_assoc] using hFS) hLS hrgS ?_ ?_ ?_ ?_ ?_ hsok2
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
    simp only [KeptJX] at hj
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
theorem CtxX.raise {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) {l1 : Nat}
    (hl : l0 ≤ l1) (hl1 : l1 ≤ stLen M st) :
    CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l1 fbp r ex M := by
  obtain ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, hmO, hmv, hnm, hx, hxO, hxv, hy, hyO, hY, hyi, hyi0, hyl, hyl',
    hzc, hz, hfe, hsth, hstw, hsok, hn0, hl0, hcap, harr, hug, huf, huw, hsu, hstg, hstf, hgl, hgO, hstwb, hwba,
    hcacc, hcrt, hcO, r3a8, r3b0, r3b8, r3d0, r3c0, r398, r390, r3d8, hstnz⟩ := h
  have hc : l1 ≤ stCap M st := Nat.le_trans hl1 hsok.2.2.2.2.2.1
  exact ⟨he, hce, hK, hK20, hn, hn128, hmc, hmc', hm, obj_raise hmO hl hc, hmv, hnm, hx, obj_raise hxO hl hc, hxv,
    hy, obj_raise hyO hl hc, hY, hyi, hyi0, hyl, hyl', hzc,
    fun h2 => ⟨(hz h2).1, (hz h2).2.1, obj_raise (hz h2).2.2.1 hl hc, (hz h2).2.2.2.1, (hz h2).2.2.2.2⟩,
    hfe, hsth, hstw, hsok, by omega, hl1, hcap, harr, stUp_raise' hug hl hc, stUp_raise' huf hl hc,
    stUp_raise' huw hl hc, stUp_raise hsu hl hc, hstg, hstf, hgl, obj_raise hgO hl hc, hstwb, hwba,
    hcacc, hcrt, obj_raise hcO hl hc, r3a8, r3b0, r3b8, r3d0, r3c0, r398, r390, r3d8, hstnz⟩

/-- install a new `x` (`n` words at `xp'`, value `Xv'`) in the context -/
theorem CtxX.setX {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M) {xp' Xv' : Nat}
    (hx : Inp R L sp n M xp') (hxO : Obj R L sp K st l0 ex M xp' (8 * n)) (hxv : M.readLE xp' (8 * n) = Xv') :
    CtxX R L g fs sp K n mp mc Mv xp' Xv' yp ylen Y yi zp zc st n0 l0 fbp r ex M := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, -, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42,
    h43, h44, h45, r1, r2, r3, r4, r5, r6, r7, r8, hstnz⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hx, hxO, hxv, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42,
    h43, h44, h45, r1, r2, r3, r4, r5, r6, r7, r8, hstnz⟩

/-- the `x` operand before normalisation (`[xp, xp + 8 xr)` its array, `xl ≤ xr` its length) -/
@[reducible] def XIn (R : RtInv) (L : List (Nat × Nat)) (sp K st l0 : Nat) (M : Memory) (xp xl xr : Nat) : Prop :=
  xl ≤ xr ∧ 0 < xr ∧ xr < 2 ^ 40 ∧ M.accessible xp (8 * xr) false = true ∧ xp + 8 * xr ≤ 2 ^ 48 ∧
    Obj R L sp K st l0 [] M xp (8 * xr)

theorem XIn.keep {R : RtInv} {L L' : List (Nat × Nat)} {g fs sp K st l0 xp xl xr : Nat} {M M' : Memory}
    (h : XIn R L sp K st l0 M xp xl xr) (hk : KeepsX R L L' g fs sp K st l0 [] M M') (hl : l0 ≤ stCap M' st) :
    XIn R L' sp K st l0 M' xp xl xr :=
  ⟨h.1, h.2.1, h.2.2.1, by rw [hk.2.1]; exact h.2.2.2.1, h.2.2.2.2.1, obj_keepX hk hl h.2.2.2.2.2⟩

theorem XIn.raise {R : RtInv} {L : List (Nat × Nat)} {sp K st l0 l1 xp xl xr : Nat} {M : Memory}
    (h : XIn R L sp K st l0 M xp xl xr) (hl : l0 ≤ l1) (hl1 : l1 ≤ stCap M st) : XIn R L sp K st l1 M xp xl xr :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, obj_raise h.2.2.2.2.2 hl hl1⟩

theorem obj_subk {R : RtInv} {L : List (Nat × Nat)} {sp K st l0 a k b k' : Nat} {ex : List (Nat × Nat)} {M : Memory}
    (h : Obj R L sp K st l0 ex M a k) (h1 : a ≤ b) (h2 : b + k' ≤ a + k) : Obj R L sp K st l0 ex M b k' := by
  obtain ⟨o1, o2, o3, o4, o5⟩ := h
  simp only [AW, Apart, stUp] at o2 o3 o4
  exact ⟨held_sub o1 h1 h2, by simp only [AW, Apart]; omega, by unfold Apart; omega,
    by simp only [Apart, stUp]; omega, fun e he => by have := o5 e he; unfold Apart at this ⊢; omega⟩

/-- a normalised `x` of exactly `n` words installs in the context -/
theorem CtxX.ofXIn {R : RtInv} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r : Nat} {M : Memory}
    (h : CtxX R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r [] M) {xp' xr : Nat}
    (hx : XIn R L sp K st l0 M xp' n xr) :
    CtxX R L g fs sp K n mp mc Mv xp' (M.readLE xp' (8 * n)) yp ylen Y yi zp zc st n0 l0 fbp r [] M := by
  obtain ⟨hl, -, -, ha, h48, hO⟩ := hx
  have hK := h.2.2.1
  have hO' := obj_subk hO (Nat.le_refl _) (show xp' + 8 * n ≤ xp' + 8 * xr by omega)
  exact CtxX.setX h ⟨M.accessible_sub ha (Or.inl rfl) (Nat.le_refl _) (by omega), by omega, hO'.1,
    aw_w4 hK hO'.2.1⟩ hO' rfl

theorem apartAll_of_ext {R : RtInv} {L L' : List (Nat × Nat)} {a k : Nat} (hx : LiveExt R L L')
    (h : ApartAll a k L') : ApartAll a k L := fun r hr => h r (hx.mem_old hr)

/-- two steps in a row (the second at the first's live set) -/
theorem KeepsX.trans {R : RtInv} {L L' L'' : List (Nat × Nat)} {g fs sp K st l0 : Nat} {ex : List (Nat × Nat)}
    {M M' M'' : Memory} (h1 : KeepsX R L L' g fs sp K st l0 ex M M') (h2 : KeepsX R L' L'' g fs sp K st l0 ex M' M'')
    (hl : l0 ≤ stCap M' st) : KeepsX R L L'' g fs sp K st l0 ex M M'' := by
  have h1' := h1
  obtain ⟨x1, a1, -, r1, s1, g1, f1, -, l1, w1, c1, i1⟩ := h1'
  obtain ⟨x2, a2, ce2, r2, s2, g2, f2, k2, l2, w2, c2, i2⟩ := h2
  refine ⟨x1.trans x2, fun a k w => (a2 a k w).trans (a1 a k w), ce2,
    fun a k ho => (r2 a k (obj_keepX h1 hl ho)).trans (r1 a k ho), fun j hj => (s2 j hj).trans (s1 j hj),
    g2.trans g1, f2.trans f1, k2, Nat.le_trans l1 l2, ?_, fun h => c2 (c1 h), i1.trans i2 x2⟩
  rcases w2 with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · rw [e1, e2]; exact w1
  · exact Or.inr ⟨hin, apartAll_of_ext x1 hap⟩

end FvModexp.Amd64.W4Pro
