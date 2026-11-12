import FvModexp.Proofs.Arm64.Exp.P2PreJ

/-!
# `buildPrecomputationWindowModPower2` (arm64): the round facts `RS` through a callee (agent infra)

`slot_keep`: frame slots / locals of the function are kept by a callee at `SP' = SP - 208` (window `kC ≤ kc`,
`aC ≤ 88`, other writes `WOK`). `pwd_keep` / `pwt_keep`: the `powers` entries from kept reads. `rs_call`: `RS` after a
callee writing `z = [zp, zp + zn)` inside `buf` at or above `powers[k]`'s words (and possibly the stack's header / free
part), given the new context.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs)

set_option maxRecDepth 20000 in
/-- a word of the function's frame outside the callee spill area `[sp - 200, sp - 120)` is kept by a callee -/
theorem slot_keep {R : RtInv} {L : List (Nat × Nat)} {s S' : State} {kc st : Nat} {M M' : Memory}
    (hw : WinF R kc s st) (hsp : S'.sp.toNat = s.sp.toNat - 208) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} (hws : ∀ r ∈ ws, WOK R L s st r) (hF : MemFrame M M' (R.rt ++ winA S' kC aC ++ ws))
    {a : Nat} (h1 : s.sp.toNat - 216 ≤ a) (h2 : a + 8 ≤ s.sp.toNat + 80)
    (h3 : a + 8 ≤ s.sp.toNat - 200 ∨ s.sp.toNat - 120 ≤ a) : M'.readLE a 8 = M.readLE a 8 := by
  have hK := hw.sp
  have hrt := hw.rt
  have hk8 := hw.kc8
  simp only [K, A] at hK hrt
  refine frame_read hF fun ⟨r1, r2⟩ hr hr' => ?_
  show a + 8 ≤ r1 ∨ r2 ≤ a
  simp only [List.mem_append, winA, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr hr'
  rcases hr with (hr | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | hr
  · have := MemFrame.outside_mem (hrt.of_sub (a := a) (n := 8) (by omega) (by omega)) hr
    simp only at this; omega
  · omega
  · omega
  · have := wok_win (hws _ hr) hw hr'; simp only [K, A] at this; omega

theorem lo_keep {R : RtInv} {L : List (Nat × Nat)} {s S' : State} {kc st pw i : Nat} {M M' : Memory}
    (hw : WinF R kc s st) (hsp : S'.sp.toNat = s.sp.toNat - 208) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} (hws : ∀ r ∈ ws, WOK R L s st r) (hF : MemFrame M M' (R.rt ++ winA S' kC aC ++ ws))
    (h : Lo s pw i M) : Lo s pw i M' := by
  have hK := hw.sp
  simp only [K] at hK
  obtain ⟨e0, e1, e2, e3⟩ := h
  exact ⟨(slot_keep hw hsp hk ha hws hF (by omega) (by omega) (by omega)).trans e0,
    (slot_keep hw hsp hk ha hws hF (by omega) (by omega) (by omega)).trans e1,
    (slot_keep hw hsp hk ha hws hF (by omega) (by omega) (by omega)).trans e2,
    (slot_keep hw hsp hk ha hws hF (by omega) (by omega) (by omega)).trans e3⟩

theorem lo2_keep {R : RtInv} {L : List (Nat × Nat)} {s S' : State} {kc st pw i : Nat} {M M' : Memory}
    (hw : WinF R kc s st) (hsp : S'.sp.toNat = s.sp.toNat - 208) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} (hws : ∀ r ∈ ws, WOK R L s st r) (hF : MemFrame M M' (R.rt ++ winA S' kC aC ++ ws))
    (h : Lo2 s pw i M) : Lo2 s pw i M' := by
  have hK := hw.sp
  simp only [K] at hK
  exact (slot_keep hw hsp hk ha hws hF (by omega) (by omega) (by omega)).trans h

/-- `powers[j]` (computed) from kept reads of its header and its `w` words -/
theorem pwd_keep {M M' : Memory} {pw bp lm X j : Nat} (h : PwD M pw bp lm X j)
    (hp : ∀ a n, pw + 24 * j ≤ a → a + n ≤ pw + 24 * j + 24 → M'.readLE a n = M.readLE a n)
    (hb : ∀ a n, bp + 8 * (j * W lm) ≤ a → a + n ≤ bp + 8 * (j * W lm) + 8 * W lm → 0 < n →
      M'.readLE a n = M.readLE a n) : PwD M' pw bp lm X j := by
  obtain ⟨e0, e2, e1, ev, en⟩ := h
  have r0 := hp (pw + 24 * j) 8 (by omega) (by omega)
  have r1 := hp (pw + 24 * j + 8) 8 (by omega) (by omega)
  have r2 := hp (pw + 24 * j + 16) 8 (by omega) (by omega)
  simp only [PwD]
  rw [r1]
  refine ⟨r0.trans e0, r2.trans e2, e1, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (M.readLE (pw + 24 * j + 8) 8) with h0 | h0
    · rw [h0] at ev ⊢; exact ev
    · simp only [natVal] at ev ⊢
      rw [hb _ _ (Nat.le_refl _) (by omega) (by omega)]; exact ev
  · rcases Nat.eq_zero_or_pos (M.readLE (pw + 24 * j + 8) 8) with hl | hl
    · exact Or.inl hl
    rcases en with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [hb _ _ (by omega) (by
        have : 8 * (M.readLE (pw + 24 * j + 8) 8 - 1) + 8 ≤ 8 * W lm := by omega
        omega) (by omega)]
      exact h0

theorem pwt_keep {M M' : Memory} {pw bp lm j : Nat} (h : PwT M pw bp lm j)
    (hp : ∀ a n, pw + 24 * j ≤ a → a + n ≤ pw + 24 * j + 24 → M'.readLE a n = M.readLE a n) :
    PwT M' pw bp lm j := by
  obtain ⟨e0, e1, e2⟩ := h
  exact ⟨(hp _ _ (by omega) (by omega)).trans e0, (hp _ _ (by omega) (by omega)).trans e1,
    (hp _ _ (by omega) (by omega)).trans e2⟩

set_option maxRecDepth 20000 in
/-- **`RS` after a callee** at `S'` writing `z = [zp, zp + zn)` (`bp + 8 k w ≤ zp`, inside `buf`) and possibly the stack
(`ws ⊆ [z] ++ stWs M st`, all `WOK`), given the new context `hc'` -/
theorem rs_call {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm : Nat} {s S' : State} {X bp : Nat}
    {M M' : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 i k : Nat} (h : RS R kc L st pw pl lm s X bp M L1 b1 i k)
    (hf : PF R kc L st pw pl s) (hsa : StkApart s.mem st pw (24 * pl)) (hpl : 0 < pl)
    (hsp : S'.sp.toNat = s.sp.toNat - 208) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} {zp zn : Nat} (hws : ∀ r ∈ ws, r ∈ [(zp, zp + zn)] ++ stWs M st)
    (hwok : ∀ r ∈ ws, WOK R L s st r) (hz : bp + 8 * (k * W lm) ≤ zp) (hkp : k ≤ pl)
    (hF : MemFrame M M' (R.rt ++ winA S' kC aC ++ ws)) (hLF : LiveFrame M M' L1 ws)
    (hc' : Ctx R kc L st pw pl lm s bp M' L2 b2) : RS R kc L st pw pl lm s X bp M' L2 b2 i k := by
  have hp : ∀ a n, pw ≤ a → a + n ≤ pw + 24 * pl → M'.readLE a n = M.readLE a n := fun a n h1 h2 =>
    pw_rd hf hsa hpl hsp hk ha hwok hF hLF h1 h2
  have hNB : ∀ j, j < k → k ≤ pl → bp + 8 * (j * W lm) + 8 * W lm ≤ bp + 8 * NB pl lm := by
    intro j hj hkp
    have : (j + 1) * W lm ≤ (pl + 1) * W lm := Nat.mul_le_mul_right _ (by omega)
    simp only [NB]; rw [Nat.add_mul] at this; omega
  refine ⟨hc', fun j hj => ?_, fun j hj hjp => pwt_keep (h.t j hj hjp) fun a n h1 h2 => hp a n (by omega) (by omega),
    lo_keep hf.w hsp hk ha hwok hF h.lo⟩
  · have hjk : (j + 1) * W lm ≤ k * W lm := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul] at hjk
    refine pwd_keep (h.d j hj) (fun a n h1 h2 => hp a n (by omega) (by
        have : j + 1 ≤ pl := by omega
        omega))
      fun a n h1 h2 h0 => buf_rd h.c hf hsp hk ha hws hF hLF (by omega) (by have := hNB j hj hkp; omega) h0
        (by unfold Apart; omega)

end FvModexp.Arm64.P2Pre
