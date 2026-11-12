import FvModexp.Proofs.Amd64.Int.IntASDefs

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (amd64): the callees' preconditions (twin of the arm64 IntASCall)

At a callee entry `RSP = RSP₀ - 96` and memory differs from the entry memory only inside the window
(`MemFrame s.mem S.mem (win s 4536 32)`, regions unchanged): the preconditions of `nat.add` / `nat.sub` follow from
`Pre`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64.IntAS

theorem natVal_frame {m m' : Arm64.Memory} {ws : List (Nat × Nat)} (h : MemFrame m m' ws) {p l : Nat}
    (ho : Outside p (8 * l) ws) : natVal m' p l = natVal m p l := h.readLE _ _ ho

theorem natNorm_frame {m m' : Arm64.Memory} {ws : List (Nat × Nat)} (h : MemFrame m m' ws) {p l : Nat}
    (ho : Outside p (8 * l) ws) (hn : NatNorm m p l) : NatNorm m' p l := by
  rcases hn with hn | hn
  · exact Or.inl hn
  · rcases Nat.eq_zero_or_pos l with h0 | h0
    · exact Or.inl h0
    refine Or.inr ?_
    rw [h.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact hn

/-- the facts of a read-only operand at a callee entry (memory changed only in the window) -/
theorem opR_at {R : RtInv} {L : List (Nat × Nat)} {s : State} {M : Arm64.Memory}
    (hF : MemFrame s.mem M (win s 4536 32)) {a : Nat} (h : OpR R L s a) :
    M.readLE (a + 8) 8 = hP s.mem a ∧ M.readLE (a + 16) 8 = hL s.mem a ∧ M.readLE (a + 24) 8 = hC s.mem a ∧
      M.readLE a 1 = hNeg s.mem a ∧
      M.accessible (hP s.mem a) (8 * hL s.mem a) false = true ∧ NatNorm M (hP s.mem a) (hL s.mem a) ∧
      natVal M (hP s.mem a) (hL s.mem a) = natVal s.mem (hP s.mem a) (hL s.mem a) := by
  obtain ⟨-, -, -, ho, -, -, -, hacc, -, -, hn, hpo⟩ := h
  exact ⟨hF.readLE _ _ (ho.of_sub (by omega) (by omega)), hF.readLE _ _ (ho.of_sub (by omega) (by omega)),
    hF.readLE _ _ (ho.of_sub (by omega) (by omega)), hF.readLE _ _ (ho.of_sub (by omega) (by omega)),
    by rw [hF.accessible]; exact hacc, natNorm_frame hF hpo hn, natVal_frame hF hpo⟩

/-- the window is outside the runtime-owned ranges -/
theorem win_rt {R : RtInv} {L : List (Nat × Nat)} {s : State} (hce : CallEnv R L s 4536 32) :
    LiveSep (win s 4536 32) R.rt := fun r hr => by
  simp only [win, List.mem_singleton] at hr; subst hr
  have hsp0 : 4536 ≤ (s.regs 4).toNat := hce.2.1.1
  have := hce.2.2.2.2.1
  simp only
  exact this.of_sub (by omega) (by omega)

set_option maxRecDepth 20000 in
/-- the precondition of `z.abs.add(x.abs, y.abs)` at `RSP - 96` -/
theorem addPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y : Nat} {s S : State}
    (hpre : Pre R b L z x y s) (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 96) (h14 : S.regs 14 = s.regs 14)
    (hfs : S.fsBase = s.fsBase)
    (hF : MemFrame s.mem S.mem (win s 4536 32)) (hreg : S.mem.regions = s.mem.regions) :
    NatAdd.Pre R b L (BitVec.ofNat 64 (hP s.mem z)) (BitVec.ofNat 64 (hC s.mem z)) (BitVec.ofNat 64 (hP s.mem x))
      (BitVec.ofNat 64 (hL s.mem x)) (BitVec.ofNat 64 (hC s.mem x)) (BitVec.ofNat 64 (hP s.mem y))
      (BitVec.ofNat 64 (hL s.mem y)) (BitVec.ofNat 64 (hC s.mem y)) S := by
  obtain ⟨hce, hsv, hwt, hx, hy, -, -, -, -, -, -, -, -, -, hzc, hzl, hzo, hz0, -, hcost, hinv⟩ := hpre
  have hce' := CallEnv.callee (stk1 := 4440) (above1 := 80) hce hsp h14 hfs (by decide) (by omega) (by omega) hF hreg
  have hsp0 : 4536 ≤ (s.regs 4).toNat := hce.2.1.1
  obtain ⟨-, -, -, -, hxlc, hxc, hxl16, hxa, hx48, hxh, hxn, hxo⟩ := hx
  obtain ⟨-, -, -, -, hylc, hyc, hyl16, hya, hy48, hyh, hyn, hyo⟩ := hy
  have hxp : hP s.mem x < 2 ^ 64 := by omega
  have hyp : hP s.mem y < 2 ^ 64 := by omega
  have hzp : hP s.mem z < 2 ^ 64 := by have := Arm64.Memory.readLE_lt s.mem (z + 8) 8; simpa using this
  have hrout := win_rt hce
  unfold NatAdd.Pre NatAdd.PreS
  simp only [NatAdd.need, NatAdd.mx]
  rw [tN hzp, tN (show hC s.mem z < 2 ^ 64 by omega), tN hxp, tN (show hL s.mem x < 2 ^ 64 by omega),
    tN (show hC s.mem x < 2 ^ 64 by omega), tN hyp, tN (show hL s.mem y < 2 ^ 64 by omega),
    tN (show hC s.mem y < 2 ^ 64 by omega)]
  simp only [win, hsp, outside_cons, outside_nil, and_true] at hzo hxo hyo ⊢
  have hcA := asCost_add (hL s.mem x) (hL s.mem y)
  unfold asNeed at hcA
  have hxn' := natNorm_frame hF (by simp only [win, outside_cons, outside_nil, and_true]; omega) hxn
  have hyn' := natNorm_frame hF (by simp only [win, outside_cons, outside_nil, and_true]; omega) hyn
  have hxa' : S.mem.accessible (hP s.mem x) (8 * hL s.mem x) false = true := by rw [hF.accessible]; exact hxa
  have hya' : S.mem.accessible (hP s.mem y) (8 * hL s.mem y) false = true := by rw [hF.accessible]; exact hya
  refine ⟨hce', hwt, hxlc, hylc, hxc, hyc, (by omega), (by omega), hzc, ?_, (by omega), fun hc => ?_,
    hxa', hx48, hxh, hxn', hyn', (by omega), hya', hy48, hyh, (by omega), ?_, fun _ => ⟨hsv.1 _ _ _ ?_, (by omega)⟩,
    fun d src k hk => hsv.2.1 d src k (by omega)⟩
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzl hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · obtain ⟨a1, a2, -, a3, a4⟩ := hz0 hc
    rw [h14, hfs]
    refine ⟨a1, a2, ?_, ?_⟩
    · rcases a3 with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h
    · rcases a4 with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h
  · rw [h14]; exact RtInv.inv_frame hF hrout hinv
  · unfold makeCap; split <;> split <;> omega

set_option maxRecDepth 20000 in
/-- the precondition of `z.abs.sub(u.abs, v.abs)` at `SP - 96` (`(u, v) = (x, y)` or `(y, x)`, `v ≤ u`) -/
theorem subPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y u v : Nat} {s S : State}
    (hpre : Pre R b L z x y s) (hu : OpR R L s u) (hv : OpR R L s v)
    (hzu : 0 < hC s.mem z → (hP s.mem z = hP s.mem u ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem u) (8 * hL s.mem u)))
    (hzv : 0 < hC s.mem z → (hP s.mem z = hP s.mem v ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem v) (8 * hL s.mem v)))
    (hvl : hL s.mem v ≤ hL s.mem u) (hvu : natVal s.mem (hP s.mem v) (hL s.mem v) ≤ natVal s.mem (hP s.mem u) (hL s.mem u))
    (hcu : makeCost (hL s.mem u) ≤ b)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 96) (h14 : S.regs 14 = s.regs 14)
    (hfs : S.fsBase = s.fsBase)
    (hF : MemFrame s.mem S.mem (win s 4536 32)) (hreg : S.mem.regions = s.mem.regions) :
    NatSub.Pre R b L (BitVec.ofNat 64 (hP s.mem z)) (BitVec.ofNat 64 (hC s.mem z)) (BitVec.ofNat 64 (hP s.mem u))
      (BitVec.ofNat 64 (hL s.mem u)) (BitVec.ofNat 64 (hC s.mem u)) (BitVec.ofNat 64 (hP s.mem v))
      (BitVec.ofNat 64 (hL s.mem v)) (BitVec.ofNat 64 (hC s.mem v)) S := by
  obtain ⟨hce, hsv, hwt, -, -, -, -, -, -, -, -, -, -, -, hzc, hzl, hzo, hz0, -, -, hinv⟩ := hpre
  have hce' := CallEnv.callee (stk1 := 4288) (above1 := 80) hce hsp h14 hfs (by decide) (by omega) (by omega) hF hreg
  have hsp0 : 4536 ≤ (s.regs 4).toNat := hce.2.1.1
  have hu' := opR_at hF hu
  have hv' := opR_at hF hv
  obtain ⟨-, -, -, -, hxlc, hxc, hxl16, hxa, hx48, hxh, hxn, hxo⟩ := hu
  obtain ⟨-, -, -, -, hylc, hyc, hyl16, hya, hy48, hyh, hyn, hyo⟩ := hv
  have hxp : hP s.mem u < 2 ^ 64 := by omega
  have hyp : hP s.mem v < 2 ^ 64 := by omega
  have hzp : hP s.mem z < 2 ^ 64 := by have := Arm64.Memory.readLE_lt s.mem (z + 8) 8; simpa using this
  have hrout := win_rt hce
  unfold NatSub.Pre NatSub.PreS
  rw [tN hzp, tN (show hC s.mem z < 2 ^ 64 by omega), tN hxp, tN (show hL s.mem u < 2 ^ 64 by omega),
    tN (show hC s.mem u < 2 ^ 64 by omega), tN hyp, tN (show hL s.mem v < 2 ^ 64 by omega),
    tN (show hC s.mem v < 2 ^ 64 by omega), hu'.2.2.2.2.2.2, hv'.2.2.2.2.2.2]
  simp only [win, hsp, outside_cons, outside_nil, and_true] at hzo hxo hyo ⊢
  refine ⟨hce', hwt, hvl, hvu, hxlc, hylc, hxc, hyc, (by omega), (by omega), hzc, ?_, (by omega), fun hc => ?_,
    hu'.2.2.2.2.1, hx48, hxh, hu'.2.2.2.2.2.1, hv'.2.2.2.2.2.1, (by omega), hv'.2.2.2.2.1, hy48, hyh, (by omega), ?_,
    fun _ => ⟨hsv.1 _ _ _ ?_, hcu⟩, fun d src k hk => hsv.2.1 d src k (by omega)⟩
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzl hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · obtain ⟨a1, a2, -, -, -⟩ := hz0 hc
    rw [h14, hfs]
    refine ⟨a1, a2, ?_, ?_⟩
    · rcases hzu hc with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h
    · rcases hzv hc with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h
  · rw [h14]; exact RtInv.inv_frame hF hrout hinv
  · unfold makeCap; split <;> omega

end FvModexp.Amd64.IntAS
