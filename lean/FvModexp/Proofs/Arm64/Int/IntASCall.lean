import FvModexp.Proofs.Arm64.Int.IntASDefs

/-!
# `(*Int).Add` / `(*Int).Sub` (arm64): the callees' preconditions and the call steps

At a callee entry the stack pointer is `SP - 96` and memory differs from the entry memory only inside the window
(`MemFrame s.mem S.mem (win s 4560 32)`, regions unchanged): the preconditions of `nat.add`, `nat.sub` (agent divmc)
and `nat.cmp` (agent asm) follow from `Pre`. The call steps (`addCall`, `subCall`) hand the destructured postcondition
to a continuation (pattern of agent infra's `SubMod2N.subCall`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.IntAS

open FvModexp.Arm64.RunIface (Serves)

theorem natVal_frame {m m' : Memory} {ws : List (Nat × Nat)} (h : MemFrame m m' ws) {p l : Nat}
    (ho : Outside p (8 * l) ws) : natVal m' p l = natVal m p l := h.readLE _ _ ho

theorem natNorm_frame {m m' : Memory} {ws : List (Nat × Nat)} (h : MemFrame m m' ws) {p l : Nat}
    (ho : Outside p (8 * l) ws) (hn : NatNorm m p l) : NatNorm m' p l := by
  rcases hn with hn | hn
  · exact Or.inl hn
  · rcases Nat.eq_zero_or_pos l with h0 | h0
    · exact Or.inl h0
    refine Or.inr ?_
    rw [h.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact hn

/-- the facts of a read-only operand at a callee entry (memory changed only in the window) -/
theorem opR_at {R : RtInv} {L : List (Nat × Nat)} {s : State} {M : Memory} (hF : MemFrame s.mem M (win s 4560 32))
    {a : Nat} (h : OpR R L s a) :
    M.readLE (a + 8) 8 = hP s.mem a ∧ M.readLE (a + 16) 8 = hL s.mem a ∧ M.readLE (a + 24) 8 = hC s.mem a ∧
      M.readLE a 1 = hNeg s.mem a ∧
      M.accessible (hP s.mem a) (8 * hL s.mem a) false = true ∧ NatNorm M (hP s.mem a) (hL s.mem a) ∧
      natVal M (hP s.mem a) (hL s.mem a) = natVal s.mem (hP s.mem a) (hL s.mem a) := by
  obtain ⟨-, -, -, ho, -, -, -, hacc, -, -, hn, hpo⟩ := h
  exact ⟨hF.readLE _ _ (ho.of_sub (by omega) (by omega)), hF.readLE _ _ (ho.of_sub (by omega) (by omega)),
    hF.readLE _ _ (ho.of_sub (by omega) (by omega)), hF.readLE _ _ (ho.of_sub (by omega) (by omega)),
    by rw [hF.accessible]; exact hacc, natNorm_frame hF hpo hn, natVal_frame hF hpo⟩

set_option maxRecDepth 20000 in
/-- the precondition of `z.abs.add(x.abs, y.abs)` at `SP - 96` -/
theorem addPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y : Nat} {s S : State}
    (hpre : Pre R b L z x y s) (hsp : S.sp.toNat = s.sp.toNat - 96) (h28 : S.regs 28 = s.regs 28)
    (hF : MemFrame s.mem S.mem (win s 4560 32)) (hreg : S.mem.regions = s.mem.regions) :
    NatAdd.Pre R b L (BitVec.ofNat 64 (hP s.mem z)) (BitVec.ofNat 64 (hC s.mem z)) (BitVec.ofNat 64 (hP s.mem x))
      (BitVec.ofNat 64 (hL s.mem x)) (BitVec.ofNat 64 (hC s.mem x)) (BitVec.ofNat 64 (hP s.mem y))
      (BitVec.ofNat 64 (hL s.mem y)) (BitVec.ofNat 64 (hC s.mem y)) S := by
  obtain ⟨hce, hsv, hwt, hx, hy, -, -, -, -, -, -, -, -, hzc, hzl, hzo, hz0, -, hcost, hinv⟩ := hpre
  have hce' := CallEnv.callee (stk1 := 4464) (above1 := 80) hce hsp h28 (by decide) (by omega) (by omega) hF hreg
  have hsp0 : 4560 ≤ s.sp.toNat := hce.2.1.2.1
  obtain ⟨-, -, -, -, hxlc, hxc, hxl16, hxa, hx48, hxh, hxn, hxo⟩ := hx
  obtain ⟨-, -, -, -, hylc, hyc, hyl16, hya, hy48, hyh, hyn, hyo⟩ := hy
  have hxp : hP s.mem x < 2 ^ 64 := by omega
  have hyp : hP s.mem y < 2 ^ 64 := by omega
  have hzp : hP s.mem z < 2 ^ 64 := by have := Memory.readLE_lt s.mem (z + 8) 8; simpa using this
  have hrout : LiveSep (win s 4560 32) R.rt := fun r hr => by
    simp only [win, List.mem_singleton] at hr; subst hr
    have := hce.2.2.2.1
    simp only
    exact this.of_sub (by omega) (by omega)
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
  · obtain ⟨a1, -, a3, a4⟩ := hz0 hc
    rw [h28]
    refine ⟨a1, ?_, ?_⟩
    · rcases a3 with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h
    · rcases a4 with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h
  · rw [h28]; exact RtInv.inv_frame hF hrout hinv
  · unfold makeCap; split <;> split <;> omega

set_option maxRecDepth 20000 in
/-- the precondition of `z.abs.sub(u.abs, v.abs)` at `SP - 96` (`(u, v) = (x, y)` or `(y, x)`, `v ≤ u`) -/
theorem subPre_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {z x y u v : Nat} {s S : State}
    (hpre : Pre R b L z x y s) (hu : OpR R L s u) (hv : OpR R L s v)
    (hzu : 0 < hC s.mem z → (hP s.mem z = hP s.mem u ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem u) (8 * hL s.mem u)))
    (hzv : 0 < hC s.mem z → (hP s.mem z = hP s.mem v ∨ Apart (hP s.mem z) (8 * hC s.mem z) (hP s.mem v) (8 * hL s.mem v)))
    (hvl : hL s.mem v ≤ hL s.mem u) (hvu : natVal s.mem (hP s.mem v) (hL s.mem v) ≤ natVal s.mem (hP s.mem u) (hL s.mem u))
    (hcu : makeCost (hL s.mem u) ≤ b)
    (hsp : S.sp.toNat = s.sp.toNat - 96) (h28 : S.regs 28 = s.regs 28)
    (hF : MemFrame s.mem S.mem (win s 4560 32)) (hreg : S.mem.regions = s.mem.regions) :
    NatSub.Pre R b L (BitVec.ofNat 64 (hP s.mem z)) (BitVec.ofNat 64 (hC s.mem z)) (BitVec.ofNat 64 (hP s.mem u))
      (BitVec.ofNat 64 (hL s.mem u)) (BitVec.ofNat 64 (hC s.mem u)) (BitVec.ofNat 64 (hP s.mem v))
      (BitVec.ofNat 64 (hL s.mem v)) (BitVec.ofNat 64 (hC s.mem v)) S := by
  obtain ⟨hce, hsv, hwt, -, -, -, -, -, -, -, -, -, -, hzc, hzl, hzo, hz0, -, -, hinv⟩ := hpre
  have hce' := CallEnv.callee (stk1 := 4304) (above1 := 80) hce hsp h28 (by decide) (by omega) (by omega) hF hreg
  have hsp0 : 4560 ≤ s.sp.toNat := hce.2.1.2.1
  have hu' := opR_at hF hu
  have hv' := opR_at hF hv
  obtain ⟨-, -, -, -, hxlc, hxc, hxl16, hxa, hx48, hxh, hxn, hxo⟩ := hu
  obtain ⟨-, -, -, -, hylc, hyc, hyl16, hya, hy48, hyh, hyn, hyo⟩ := hv
  have hxp : hP s.mem u < 2 ^ 64 := by omega
  have hyp : hP s.mem v < 2 ^ 64 := by omega
  have hzp : hP s.mem z < 2 ^ 64 := by have := Memory.readLE_lt s.mem (z + 8) 8; simpa using this
  have hrout : LiveSep (win s 4560 32) R.rt := fun r hr => by
    simp only [win, List.mem_singleton] at hr; subst hr
    have := hce.2.2.2.1
    simp only
    exact this.of_sub (by omega) (by omega)
  unfold NatSub.Pre NatSub.PreS
  rw [tN hzp, tN (show hC s.mem z < 2 ^ 64 by omega), tN hxp, tN (show hL s.mem u < 2 ^ 64 by omega),
    tN (show hC s.mem u < 2 ^ 64 by omega), tN hyp, tN (show hL s.mem v < 2 ^ 64 by omega),
    tN (show hC s.mem v < 2 ^ 64 by omega), hu'.2.2.2.2.2.2, hv'.2.2.2.2.2.2]
  simp only [win, hsp, outside_cons, outside_nil, and_true] at hzo hxo hyo ⊢
  refine ⟨hce', hwt, hvl, hvu, hxlc, hylc, hxc, hyc, (by omega), (by omega), hzc, ?_, (by omega), fun hc => ?_,
    hu'.2.2.2.2.1, hx48, hxh, hu'.2.2.2.2.2.1, hv'.2.2.2.2.2.1, (by omega), hv'.2.2.2.2.1, hy48, hyh, (by omega), ?_,
    fun _ => ⟨hsv.1 _ _ _ ?_, hcu⟩, fun d src k hk => hsv.2.1 d src k (by omega)⟩
  · intro hc; obtain ⟨a1, a2, a3, a4⟩ := hzl hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · obtain ⟨a1, -, -, -⟩ := hz0 hc
    rw [h28]
    refine ⟨a1, ?_, ?_⟩
    · rcases hzu hc with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h
    · rcases hzv hc with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h
  · rw [h28]; exact RtInv.inv_frame hF hrout hinv
  · unfold makeCap; split <;> omega

/-! ## Return addresses (adapted from agent infra's `CallW.retAddr_restrict`) -/

theorem pairwise_ne {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, hp, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hne
      · exact hp.1 b hb'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact hR _ _ (hp.1 a ha')
      · exact pairwise_ne hR hp.2 ha' hb' hne

theorem find_none_of {α : Type} {p : α → Bool} : ∀ {l : List α}, l.find? p = none → ∀ x ∈ l, p x = false
  | [], _, _, hx => absurd hx (List.not_mem_nil)
  | y :: ys, h, x, hx => by
    rw [List.find?_cons] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hy
      rcases List.mem_cons.1 hx with rfl | hx'
      · simpa using hy
      · exact find_none_of h x hx'

/-- A return address inside the code of a segment `cs` of `P` whose name is not in `ns` is a `RetAddr` of the
restricted program of `ns`. -/
theorem retAddr_restrict {P : Program} {impl : List Segment} (hap : ImplApart P impl) {ns : List String}
    {cs : Segment} (hcs : cs ∈ P.segments) (hn : ns.contains cs.name = false) (i : Nat) (hi : i < cs.words.length)
    (hu : cs.base + 4 * i < 2 ^ 48) (ha : cs.base % 4 = 0) :
    RetAddr ((P.onlySegments ns).link impl) (cs.base + 4 * i) := by
  refine ⟨by omega, hu, fun seg hseg => ?_, fun st hst => ?_⟩
  · have hseg' : seg ∈ P.segments ++ impl := by
      rcases List.mem_append.1 hseg with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    have hne : seg ≠ cs := by
      rintro rfl
      rcases List.mem_append.1 hseg with h | h
      · have := (List.mem_filter.1 h).2
        rw [hn] at this; exact absurd this (by decide)
      · have := hap.1
        rw [List.pairwise_append] at this
        have := this.2.2 seg hcs seg h
        unfold Segment.Apart at this
        have hl : 0 < seg.words.length := by omega
        omega
    have := pairwise_ne (fun a b h => by unfold Segment.Apart at h ⊢; omega) hap.1 hseg'
      (List.mem_append_left _ hcs) hne
    unfold Segment.Apart at this
    omega
  · have h1 := (hap.2 cs (List.mem_append_left _ hcs) i hi).1
    unfold Program.stubAt at h1
    have := find_none_of h1 st hst
    simp at this
    exact this

/-- the return address `entry sub + 4 i` of a call from `(*Int).Add/Sub` into a callee whose functions exclude both -/
theorem ra_of {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ns.contains fnAdd = false ∧ ns.contains fnSub = false) (sub : Bool) (i : Nat) (hi : i < 101) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (entry sub + 4 * i) := by
  cases sub
  · have := retAddr_restrict hap (cs := Extracted.seg8)
      (show Extracted.seg8 ∈ Extracted.program.segments from List.getElem_mem (l := Extracted.program.segments) (n := 8) (by decide))
      (show ns.contains Extracted.seg8.name = false from hns.1) i
      (by simp [Extracted.seg8]; omega) (by simp [Extracted.seg8]; omega) (by decide)
    simpa [Extracted.seg8, entry] using this
  · have := retAddr_restrict hap (cs := Extracted.seg7)
      (show Extracted.seg7 ∈ Extracted.program.segments from List.getElem_mem (l := Extracted.program.segments) (n := 7) (by decide))
      (show ns.contains Extracted.seg7.name = false from hns.2) i
      (by simp [Extracted.seg7]; omega) (by simp [Extracted.seg7]; omega) (by decide)
    simpa [Extracted.seg7, entry] using this

end FvModexp.Arm64.IntAS
