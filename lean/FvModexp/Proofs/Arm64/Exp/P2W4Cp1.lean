import FvModexp.Proofs.Arm64.Exp.P2W4Mv

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the first window `z = z.set(powers[d])` — `LI` after the copy (agent infra)

`li_first`: from the facts at the copy point `CP = 0x1b5f98` (memory `M`: `WC`, slots, `TZ`, the destination
`(dp, dc)` a U-class buffer with `n ≤ dc`), through the spills `136/152/296` (`M1`), `memmove(dp, powers[d], 8n)` (`m`)
and the stores `200 := kk - 2`, `208 := i` (`M'`): the loop invariant `LI` with `z = (dp, n, dc)` (value
`powers[d] = p2Pow lm X d`, class U) and `zz = (zzp, 2w, 2w)` (class S).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

/-- the stack header through a step that keeps its three words -/
theorem hdr3 {M M' : Memory} {st : Nat} (h : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = M.readLE (st + j) 8) :
    stW M' st = stW M st ∧ stLen M' st = stLen M st ∧ stCap M' st = stCap M st :=
  ⟨by have := h 0 (by omega); simpa using this, h 8 (by omega), h 16 (by omega)⟩

/-- a sub-copy -/
theorem copied_sub {m0 m : Memory} {d s n j k : Nat} (h : Mem.Copied m0 m d s n) (hj : j + k ≤ n) :
    Mem.Copied m0 m (d + j) (s + j) k := fun i hi => by
  have := h (j + i) (by omega); rwa [← Nat.add_assoc, ← Nat.add_assoc] at this

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the loop invariant after the first copy** (see the module doc) -/
theorem li_first (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hw : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 (lvlL (stLen s.mem st) lm)) {ret : Nat}
    (hsl : ESl M sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st)) {zzp bp : Nat}
    (htz : TZ R L s.mem M L1 st sp zzp bp lm (natVal s.mem xp xl)) {dp dc n d kk i : Nat}
    (hub : UB R L K g sp st zp zc M L1 zzp bp lm dp dc) (hnd : n ≤ dc) (hn1 : 0 < n) (hd : d < 16) (hZo : Exp.p2Pow lm (natVal s.mem xp xl) d % 2 = 1)
    (hlen : M.readLE (sp + 320 + 24 * d + 8) 8 = n)
    {M1 m M' : Memory}
    (hF1 : MemFrame M M1 [(sp + 136, sp + 144), (sp + 152, sp + 160), (sp + 296, sp + 304)])
    (hrg1 : M1.regions = M.regions)
    (hF2 : MemFrame M1 m (R.rt ++ [(sp - 4096, sp - 8), (sp + 8, sp + 32)] ++ [(dp, dp + 8 * n)]))
    (hLF2 : LiveFrame M1 m L1 [(dp, dp + 8 * n)])
    (hinv2 : R.inv (b1 + stkR (HW (stLen s.mem st) lm) M1 st) L1 g (view R.rt L1 m))
    (hcp : Mem.Copied M1 m dp (bp + 8 * (d * W lm)) (8 * n)) (hrg2 : m.regions = M1.regions)
    (hF3 : MemFrame m M' [(sp + 200, sp + 208), (sp + 208, sp + 216)]) (hrg3 : M'.regions = m.regions)
    (r200 : M'.readLE (sp + 200) 8 = (BitVec.ofNat 64 kk - 2#64).toNat) (r208 : M'.readLE (sp + 208) 8 = i) :
    LI R L K g sp st zp zc xp xl xc yp yl lm ret s M' L1 b1 zzp bp kk i true dp n dc zzp (2 * W lm) (2 * W lm)
      (Exp.p2Pow lm (natVal s.mem xp xl) d) := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 848) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hdc0 : 0 < dc := by omega
  obtain ⟨hdW, hdH, -, -, -, hdZ, hdB⟩ := hub.ap hdc0
  have hdW' := hdW
  unfold Apart at hdW'
  obtain ⟨d0, d1, d2, d3, d4⟩ := htz.pw d hd
  rw [hlen] at d2 d3 d4
  have hjW : (d + 1) * P2Pre.W lm ≤ P2Pre.NB 16 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : d * P2Pre.W lm + P2Pre.W lm ≤ P2Pre.NB 16 lm := by rw [← Nat.succ_mul]; exact hjW
  have eW : P2Pre.W lm = W lm := rfl
  rw [eW] at d0 d1 d2 d3 d4 hjj
  have hbW := scr_win hP htz.bscr
  unfold Apart at hbW
  have hdB' := hdB
  unfold Apart at hdB'
  -- the three steps' reads
  have k1 : ∀ a k, (a + k ≤ sp + 136 ∨ sp + 304 ≤ a ∨ (sp + 160 ≤ a ∧ a + k ≤ sp + 296) ∨
      (sp + 144 ≤ a ∧ a + k ≤ sp + 152)) → M1.readLE a k = M.readLE a k := fun a k ha =>
    hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have k3 : ∀ a k, (a + k ≤ sp + 200 ∨ sp + 216 ≤ a) → M'.readLE a k = m.readLE a k := fun a k ha =>
    hF3.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hh1 : ∀ j, j + 8 ≤ 24 → M1.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj => k1 _ _ (by omega)
  have hh2 : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = M1.readLE (st + j) 8 := fun j hj =>
    mv_rdH (K := K) hF2 hLF2 (by omega) (hw.sok.2.1.sub (by omega) (by omega)) (by unfold Apart; omega)
      (by have := hdH; unfold Apart at this ⊢; omega)
  have hh3 : ∀ j, j + 8 ≤ 24 → M'.readLE (st + j) 8 = m.readLE (st + j) 8 := fun j hj => k3 _ _ (by omega)
  obtain ⟨e10, e11, e12⟩ := hdr3 hh1
  obtain ⟨e20, e21, e22⟩ := hdr3 hh2
  obtain ⟨e30, e31, e32⟩ := hdr3 hh3
  -- WC
  have hw1 := WC.win hP hw hF1 hrg1 (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
  have hw2 := WC.mv hP hw1 hF2 hLF2 hrg2 hinv2 (by have := hdH; unfold Apart at this ⊢; omega) (fun a k ho => ?_) (fun a k hin ho => ?_)
  rotate_left
  · rcases hub.org with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
    · simp only [ZS, outside_append, List.cons_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · rw [outside_append, outside_append] at ho
      have := hin.apart ho.1.1; unfold Apart at this
      simp only [outside_cons, outside_nil, and_true]; omega
  · rcases hub.org with ⟨rfl, rfl⟩ | ⟨-, -, hap⟩
    · simp only [ZS, outside_append, List.cons_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · have := hap.apart_of_inRanges hin
      simp only [outside_cons, outside_nil, and_true]; omega
  have hw3 := WC.win hP hw2 hF3 hrg3 (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega)
  -- the composed read of the window slots (outside the spills, the callee stack, the stores)
  have kW : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 32 ≤ a ∧ a + k ≤ sp + 848) →
      (a + k ≤ sp + 136 ∨ sp + 304 ≤ a ∨ (sp + 160 ≤ a ∧ a + k ≤ sp + 200) ∨ (sp + 216 ≤ a ∧ a + k ≤ sp + 296) ∨
        (sp + 144 ≤ a ∧ a + k ≤ sp + 152)) → M'.readLE a k = M.readLE a k := by
    intro a k ha hb
    rw [k3 a k (by omega), mv_rdW hP hF2 ha (by unfold Apart; omega), k1 a k (by omega)]
  have kB : ∀ a k, bp ≤ a → a + k ≤ bp + 8 * P2Pre.NB 16 lm → M'.readLE a k = M.readLE a k := by
    intro a k h1 h2
    rw [k3 a k (by omega), mv_rdH (K := K) hF2 hLF2 (by omega) (htz.bscr.held.sub h1 h2) (by unfold Apart; omega)
      (by unfold Apart; omega), k1 a k (by omega)]
  have hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w := fun a n w => by
    rw [hF3.accessible, hF2.accessible, hF1.accessible]
  have ee0 : stW M' st = stW M st := e30.trans (e20.trans e10)
  have ee1 : stLen M' st = stLen M st := e31.trans (e21.trans e11)
  have ee2 : stCap M' st = stCap M st := e32.trans (e22.trans e12)
  -- the copied value
  have hsrc : M'.readLE dp (8 * n) = M.readLE (bp + 8 * (d * W lm)) (8 * n) := by
    rw [k3 _ _ (by omega), Expmc.readLE_of_copied hcp, k1 _ _ (by omega)]
  refine ⟨hw3, ESl.keep hsl (fun a k ha => kW a k (by omega) (by omega)) (by omega), r200, r208,
    htz.keep hacc (LiveExt.refl R L1) ee0 ee1 ee2 fun a k ha => ?_, by omega, hnd, Nat.le_refl _, ?_, ?_,
    hub.keep hacc (LiveExt.refl R L1) ee0 ee1 ee2, ⟨rfl, rfl⟩, hZo, by have := hP.2.2.2.2.2.1; simp only [W]; omega⟩
  · rcases ha with ha | ha
    · exact kW a k (by omega) (by omega)
    · exact kB a k ha.1 ha.2
  · show M'.readLE dp (8 * n) = _
    rw [hsrc]; exact d3
  · right
    rcases d4 with d4 | d4
    · omega
    have hc' := copied_sub hcp (j := 8 * (n - 1)) (k := 8) (by omega)
    rw [k3 _ _ (by omega), Expmc.readLE_of_copied hc', k1 _ _ (by omega)]
    exact d4

end

end FvModexp.Arm64.P2W4
