import FvModexp.Proofs.Arm64.Exp.P2PreWbC

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (arm64): pre-loop facts before the loop locals exist (agent infra)

`RS0 … k`: `RS` without the loop locals (used between the fill loop and the loop head). `rs0_rd` / `rs0_st` /
`rs0_call` / `rs0_of_rdr` / `rs0_next`: the `RS` lemmas for `RS0`. `x_ctx`: the operand `x` at a context memory.
`JT`: the join after `powers[1] = trunc(x, logM)` returns (`0x1b561c`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn)

/-- the round facts without loop locals: `powers[j]` computed for `j < k`, untouched for `k < j` -/
structure RS0 (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (st pw pl lm : Nat) (s : State) (X bp : Nat)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 : Nat) (k : Nat) : Prop where
  c : Ctx R kc L st pw pl lm s bp M L1 b1
  d : ∀ j, j < k → PwD M pw bp lm X j
  t : ∀ j, k < j → j < pl → PwT M pw bp lm j

section
variable {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm : Nat} {s : State}

theorem rs0_rd {X bp : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 k : Nat}
    (h : RS0 R kc L st pw pl lm s X bp M L1 b1 k) (hc' : Ctx R kc L st pw pl lm s bp M' L2 b2)
    (hrd : ∀ a n, 0 < n → ((pw ≤ a ∧ a + n ≤ pw + 24 * k) ∨ (pw + 24 * k + 24 ≤ a ∧ a + n ≤ pw + 24 * pl) ∨
      (bp ≤ a ∧ a + n ≤ bp + 8 * (k * W lm))) → M'.readLE a n = M.readLE a n) :
    RS0 R kc L st pw pl lm s X bp M' L2 b2 k := by
  refine ⟨hc', fun j hj => ?_, fun j hj hjp => pwt_keep (h.t j hj hjp) fun a n h1 h2 => ?_⟩
  · have hjk := pw_sep (lm := lm) hj
    refine pwd_keep (h.d j hj) (fun a n h1 h2 => ?_) fun a n h1 h2 h0 => hrd a n h0 (Or.inr (Or.inr
      ⟨by omega, by omega⟩))
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp [Memory.readLE]
    · exact hrd a n h0 (Or.inl ⟨by omega, by omega⟩)
  · rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp [Memory.readLE]
    · exact hrd a n h0 (Or.inr (Or.inl ⟨by omega, by omega⟩))

theorem rs0_next {X bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (h : RS0 R kc L st pw pl lm s X bp M L1 b1 k) (hd : PwD M pw bp lm X k) :
    RS0 R kc L st pw pl lm s X bp M L1 b1 (k + 1) :=
  ⟨h.c, fun j hj => by
    rcases Nat.lt_or_ge j k with h1 | h1
    · exact h.d j h1
    · rw [show j = k by omega]; exact hd, fun j hj hjp => h.t j (by omega) hjp⟩

theorem rs0_of_rdr {X bp : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 k : Nat}
    (h : RS0 R kc L st pw pl lm s X bp M L1 b1 k) (hc' : Ctx R kc L st pw pl lm s bp M' L2 b2) (hk : k ≤ pl)
    (hrd : ∀ a n, 0 < n → RdR s pw pl lm bp a n → M'.readLE a n = M.readLE a n) :
    RS0 R kc L st pw pl lm s X bp M' L2 b2 k ∧ KeepB bp (NB pl lm) M M' := by
  have hkn : k * W lm ≤ NB pl lm := Nat.le_trans (Nat.mul_le_mul_right _ hk) (Nat.mul_le_mul_right _ (by omega))
  refine ⟨rs0_rd h hc' fun a n h0 hr => hrd a n h0 ?_, fun a n h0 h1 h2 => hrd a n h0 ?_⟩
  · simp only [RdR]; omega
  · simp only [RdR]; omega

set_option maxRecDepth 20000 in
theorem rs0_call {S' : State} {X bp : Nat}
    {M M' : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 k : Nat} (h : RS0 R kc L st pw pl lm s X bp M L1 b1 k)
    (hf : PF R kc L st pw pl s) (hsa : StkApart s.mem st pw (24 * pl)) (hpl : 0 < pl)
    (hsp : S'.sp.toNat = s.sp.toNat - 208) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} {zp zn : Nat} (hws : ∀ r ∈ ws, r ∈ [(zp, zp + zn)] ++ stWs M st)
    (hwok : ∀ r ∈ ws, WOK R L s st r) (hz : bp + 8 * (k * W lm) ≤ zp) (hkp : k ≤ pl)
    (hF : MemFrame M M' (R.rt ++ winA S' kC aC ++ ws)) (hLF : LiveFrame M M' L1 ws)
    (hc' : Ctx R kc L st pw pl lm s bp M' L2 b2) : RS0 R kc L st pw pl lm s X bp M' L2 b2 k := by
  have hp : ∀ a n, pw ≤ a → a + n ≤ pw + 24 * pl → M'.readLE a n = M.readLE a n := fun a n h1 h2 =>
    pw_rd hf hsa hpl hsp hk ha hwok hF hLF h1 h2
  have hNB : ∀ j, j < k → k ≤ pl → bp + 8 * (j * W lm) + 8 * W lm ≤ bp + 8 * NB pl lm := by
    intro j hj hkp
    have : (j + 1) * W lm ≤ (pl + 1) * W lm := Nat.mul_le_mul_right _ (by omega)
    simp only [NB]; rw [Nat.add_mul] at this; omega
  refine ⟨hc', fun j hj => ?_, fun j hj hjp => pwt_keep (h.t j hj hjp) fun a n h1 h2 => hp a n (by omega) (by omega)⟩
  have hjk : (j + 1) * W lm ≤ k * W lm := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul] at hjk
  refine pwd_keep (h.d j hj) (fun a n h1 h2 => hp a n (by omega) (by
      have : j + 1 ≤ pl := by omega
      omega))
    fun a n h1 h2 h0 => buf_rd h.c hf hsp hk ha hws hF hLF (by omega) (by have := hNB j hj hkp; omega) h0
      (by unfold Apart; omega)

end

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat} {mlC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- **`RS0` after an own store** into `powers[k]`'s header or the frame -/
theorem rs0_st (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {X bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 k : Nat} (h : RS0 R kc L st pw pl lm s X bp M L1 b1 k) (hk : k < pl)
    {a0 n0 : Nat} (v : Nat) (hn0 : 0 < n0) (ho : pw + 24 * k ≤ a0 ∧ a0 + n0 ≤ pw + 24 * k + 24) :
    RS0 R kc L st pw pl lm s X bp (M.writeLE a0 n0 v) L1 b1 k := by
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hK hpww
  have hc := h.c
  have hkp : k * W lm + W lm ≤ NB pl lm := by
    have : (k + 1) * W lm ≤ (pl + 1) * W lm := Nat.mul_le_mul_right _ (by omega)
    simp only [NB]; rw [Nat.add_mul] at this; omega
  refine rs0_rd h (ctx_own hc hf v ⟨hn0, by omega⟩) fun a n h0 hr => ?_
  refine Memory.readLE_writeLE_of_disjoint _ _ ?_
  rcases hr with hr | hr | hr
  · omega
  · omega
  · have hwok := wok_buf (zp := a) (zn := n) hc.scr hr.1 (by omega)
    have := wok_pw hwok hf.pwrt (hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by omega) (a := a0) (n := n0) (by omega)
      (by omega) (by simp only; omega)
    simp only at this; omega

set_option maxRecDepth 20000 in
/-- the operand `x` at a context memory: reads kept (value, normalisation), readable, held, apart from `buf` -/
theorem x_ctx (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) :
    natVal M x xl = natVal s.mem x xl ∧ NatNorm M x xl ∧ M.accessible x (8 * xl) false = true ∧
      Held R L1 x (8 * xl) ∧ (0 < xl → Apart bp (8 * NB pl lm) x (8 * xl)) := by
  obtain ⟨hx40, hxa, hx48, hxh, hxw⟩ := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxn := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxs := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpx := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases Nat.eq_zero_or_pos xl with h0 | h0
  · subst h0
    refine ⟨by simp [natVal, Memory.readLE], Or.inl rfl, by rw [hc.fr.accessible]; exact hxa, hc.le.held hxh,
      fun h => absurd h (by decide)⟩
  have hrdx : ∀ a n, x ≤ a → a + n ≤ x + 8 * xl → M.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have h1' := hpx h0
    obtain ⟨h2', h3⟩ := hxs (by omega)
    unfold Apart at h1' h2'
    have hLW : ∀ r ∈ LW s pw pl st, r.1 < r.2 → a + n ≤ r.1 ∨ r.2 ≤ a := by
      intro r hr hlt
      simp only [LW, stWs, stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only at hlt ⊢
        have := h3 (by omega); unfold Apart at this; omega
    rcases hxh with hL' | hR
    · exact lf_read hc.lf (hL'.sub h1 h2) hLW
    · refine frame_read hc.fr fun r hr hlt => ?_
      simp only [AW, List.mem_append] at hr
      rcases hr with (hr | hr) | hr | hr
      · exact MemFrame.outside_mem (hR.of_sub h1 h2) hr
      · simp only [winA, K, A, List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [win, K, A, outside_cons, outside_nil, and_true] at hxw
        rcases hr with rfl | rfl <;> (dsimp only; omega)
      · exact hLW r (List.mem_append.2 (Or.inl hr)) hlt
      · exact hLW r (List.mem_append.2 (Or.inr hr)) hlt
  have hrd := hrdx x (8 * xl) (Nat.le_refl _) (Nat.le_refl _)
  have hrd1 := hrdx (x + 8 * (xl - 1)) 8 (by omega) (by omega)
  refine ⟨by simp only [natVal]; rw [hrd], ?_, by rw [hc.fr.accessible]; exact hxa, hc.le.held hxh, fun _ => ?_⟩
  · rcases hxn with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hrd1]; exact h)
  · have hnb : 0 < NB pl lm := Nat.mul_pos (by have := (pl_facts hpre).1; omega) (by have := (w_facts hpre).1; omega)
    rcases hc.scr.loc with ⟨-, l1, l2⟩ | ⟨hin, hap⟩
    · obtain ⟨-, h3⟩ := hxs (by omega)
      have := h3 (by omega); unfold Apart at this ⊢; omega
    · rcases hxh with hpL | hpO
      · exact hap.apart_of_inRanges hpL
      · exact (hin.apart hpO).symm
end

/-- the join after `powers[1] = trunc(x, logM)` returns -/
abbrev pcT : Nat := 1791516

def JT (impl : List Segment) (R : RtInv) (kc : Nat) (sqC : Nat → Nat) (mlC : Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State) : Prop :=
  ∀ (S : State) (bp : Nat) (L1 : List (Nat × Nat)) (b1 l : Nat),
    S.pc = BitVec.ofNat 64 pcT → S.sp = BitVec.ofNat 64 (s.sp.toNat - 208) → S.regs 28 = s.regs 28 →
    S.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216) → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 (bp + 8 * (1 * W lm)) → S.regs 1 = BitVec.ofNat 64 l →
    S.regs 2 = BitVec.ofNat 64 (2 * W lm) →
    RS0 R kc L st pw pl lm s (natVal s.mem x xl) bp S.mem L1 b1 1 → l ≤ W lm →
    natVal S.mem (bp + 8 * (1 * W lm)) l = PV lm x xl s 1 → NatNorm S.mem (bp + 8 * (1 * W lm)) l →
    b - c0 (stLen s.mem st) pl lm ≤ b1 →
    Goal impl R kc sqC mlC b L st pw pl lm x xl s S

end FvModexp.Arm64.P2Pre
