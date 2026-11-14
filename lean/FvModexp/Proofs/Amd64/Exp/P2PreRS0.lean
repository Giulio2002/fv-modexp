import FvModexp.Proofs.Amd64.Exp.P2PreLJ

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): reads kept and `RS0` (agent divmc s64; twin of infra's
`Arm64/Exp/P2PrePw`, `P2PreRS` (`pwd_keep`, `pwt_keep`), `P2PreX0`, `P2PreWbC` (`keepB_st`))

`pw_rd`: the `powers` array is kept by a callee (outside the runtime, the window and every `WOK` range); `buf_rd`: a
range of `buf` apart from the callee's `z`. `rs0_rd` / `rs0_of_rdr` / `rs0_call` / `rs0_st`: `RS0` after reads kept,
a callee, an own store into `powers[k]`. `keepB_st`: an own store keeps `buf`. `x_ctx`: the operand `x` at a context
memory.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkSep)

theorem wok_pw {R : RtInv} {L : List (Nat × Nat)} {s : State} {st pw pl : Nat} {r : Nat × Nat}
    (h : WOK R L s st r) (hrt : Outside pw (24 * pl) R.rt) (hsa : StkSep s.mem st pw (24 * pl))
    {a n : Nat} (h1 : pw ≤ a) (h2 : a + n ≤ pw + 24 * pl) (hr : r.1 < r.2) : a + n ≤ r.1 ∨ r.2 ≤ a := by
  obtain ⟨s1, s2, -⟩ := hsa
  simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at s2
  unfold Apart at s1 s2
  rcases h hr with h | h | ⟨h, -⟩
  · omega
  · omega
  · have := in_rt_sep h hrt hr; omega

theorem pw_rd {R : RtInv} {kc : Nat} {L L1 : List (Nat × Nat)} {s S' : State} {st pw pl : Nat}
    (hf : PF R kc L st pw pl s) (hsa : StkSep s.mem st pw (24 * pl))
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} (hws : ∀ r ∈ ws, WOK R L s st r) {M M' : Memory}
    (hF : MemFrame M M' (R.rt ++ win S' kC aC ++ ws)) (hLF : LiveFrame M M' L1 ws) {a n : Nat}
    (h1 : pw ≤ a) (h2 : a + n ≤ pw + 24 * pl) : M'.readLE a n = M.readLE a n := by
  have hw := hf.pww
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hw
  exact rd_keep hf.w hsp hk ha hF hLF (Or.inr (hf.pwrt.of_sub h1 h2)) (by simp only [K, A]; omega)
    fun r hr hr' => wok_pw (hws r hr) hf.pwrt hsa h1 h2 hr'

theorem buf_rd {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm x xl : Nat} {s S' : State} {bp : Nat}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1)
    (hf : PF R kc L st pw pl s) (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184) {kC aC : Nat} (hk : kC ≤ kc)
    (ha : aC ≤ 88) {ws : List (Nat × Nat)} {zp zn : Nat} (hws : ∀ r ∈ ws, r ∈ [(zp, zp + zn)] ++ stkWs M st)
    {M' : Memory} (hF : MemFrame M M' (R.rt ++ win S' kC aC ++ ws)) (hLF : LiveFrame M M' L1 ws) {a n : Nat}
    (h1 : bp ≤ a) (h2 : a + n ≤ bp + 8 * NB pl lm) (h0 : 0 < n) (hz : Apart a n zp zn) :
    M'.readLE a n = M.readLE a n := by
  have hwok := wok_buf (zp := a) (zn := n) hc.scr h1 h2
  have hwin := wok_win hwok hf.w (by simp only; omega)
  simp only [K, A] at hwin ⊢
  exact rd_keep hf.w hsp hk ha hF hLF (hc.scr.held.sub h1 h2) (by simp only [K, A]; omega)
    fun r hr hr' => ws_apart hc.sap h1 h2 h0 hz r (hws r hr) hr'

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
  · generalize M.readLE (pw + 24 * j + 8) 8 = r at e1 en ⊢
    rcases Nat.eq_zero_or_pos r with h0 | hr0
    · exact Or.inl h0
    rcases en with h0 | hn
    · exact Or.inl h0
    · refine Or.inr ?_
      have hb' := hb (bp + 8 * (j * W lm) + 8 * (r - 1)) 8 (by omega) (by omega) (by decide)
      rw [hb']; exact hn

theorem pwt_keep {M M' : Memory} {pw bp lm j : Nat} (h : PwT M pw bp lm j)
    (hp : ∀ a n, pw + 24 * j ≤ a → a + n ≤ pw + 24 * j + 24 → M'.readLE a n = M.readLE a n) :
    PwT M' pw bp lm j := by
  obtain ⟨e0, e1, e2⟩ := h
  exact ⟨(hp _ _ (by omega) (by omega)).trans e0, (hp _ _ (by omega) (by omega)).trans e1,
    (hp _ _ (by omega) (by omega)).trans e2⟩

section
variable {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm x xl : Nat} {s : State}

theorem rs0_rd {X bp : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 k : Nat}
    (h : RS0 R kc L st pw pl lm x xl s X bp M L1 b1 k) (hc' : Ctx R kc L st pw pl lm x xl s bp M' L2 b2)
    (hrd : ∀ a n, 0 < n → ((pw ≤ a ∧ a + n ≤ pw + 24 * k) ∨ (pw + 24 * k + 24 ≤ a ∧ a + n ≤ pw + 24 * pl) ∨
      (bp ≤ a ∧ a + n ≤ bp + 8 * (k * W lm))) → M'.readLE a n = M.readLE a n) :
    RS0 R kc L st pw pl lm x xl s X bp M' L2 b2 k := by
  refine ⟨hc', fun j hj => ?_, fun j hj hjp => pwt_keep (h.t j hj hjp) fun a n h1 h2 => ?_⟩
  · have hjk := pw_sep (lm := lm) hj
    refine pwd_keep (h.d j hj) (fun a n h1 h2 => ?_) fun a n h1 h2 h0 => hrd a n h0 (Or.inr (Or.inr
      ⟨by omega, by omega⟩))
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp [Janus.Arm64.Memory.readLE]
    · exact hrd a n h0 (Or.inl ⟨by omega, by omega⟩)
  · rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp [Janus.Arm64.Memory.readLE]
    · exact hrd a n h0 (Or.inr (Or.inl ⟨by omega, by omega⟩))

theorem rs0_of_rdr {X bp : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 k : Nat}
    (h : RS0 R kc L st pw pl lm x xl s X bp M L1 b1 k) (hc' : Ctx R kc L st pw pl lm x xl s bp M' L2 b2)
    (hk : k ≤ pl) (hrd : ∀ a n, 0 < n → RdR s pw pl lm bp a n → M'.readLE a n = M.readLE a n) :
    RS0 R kc L st pw pl lm x xl s X bp M' L2 b2 k ∧ KeepB bp (NB pl lm) M M' := by
  have hkn : k * W lm ≤ NB pl lm := Nat.le_trans (Nat.mul_le_mul_right _ hk) (Nat.mul_le_mul_right _ (by omega))
  refine ⟨rs0_rd h hc' fun a n h0 hr => hrd a n h0 ?_, fun a n h0 h1 h2 => hrd a n h0 ?_⟩
  · simp only [RdR]; omega
  · simp only [RdR]; omega

set_option maxRecDepth 20000 in
/-- **`RS0` after a callee** at `S'` writing `z = [zp, zp + zn)` (`bp + 8 k w ≤ zp`, inside `buf`) and possibly the
stack (`ws ⊆ [z] ++ stkWs M st`, all `WOK`), given the new context `hc'` -/
theorem rs0_call {S' : State} {X bp : Nat}
    {M M' : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 k : Nat} (h : RS0 R kc L st pw pl lm x xl s X bp M L1 b1 k)
    (hf : PF R kc L st pw pl s) (hsa : StkSep s.mem st pw (24 * pl))
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {ws : List (Nat × Nat)} {zp zn : Nat} (hws : ∀ r ∈ ws, r ∈ [(zp, zp + zn)] ++ stkWs M st)
    (hwok : ∀ r ∈ ws, WOK R L s st r) (hz : bp + 8 * (k * W lm) ≤ zp) (hkp : k ≤ pl)
    (hF : MemFrame M M' (R.rt ++ win S' kC aC ++ ws)) (hLF : LiveFrame M M' L1 ws)
    (hc' : Ctx R kc L st pw pl lm x xl s bp M' L2 b2) : RS0 R kc L st pw pl lm x xl s X bp M' L2 b2 k := by
  have hp : ∀ a n, pw ≤ a → a + n ≤ pw + 24 * pl → M'.readLE a n = M.readLE a n := fun a n h1 h2 =>
    pw_rd hf hsa hsp hk ha hwok hF hLF h1 h2
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
variable {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `powers` is apart from the stack's header and free part -/
theorem pw_sep_stk (hpre : Pre R kc b L st pw pl ws lm x xl s) : StkSep s.mem st pw (24 * pl) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hpre
  exact h

set_option maxRecDepth 20000 in
/-- **`RS0` after an own store** into `powers[k]`'s header -/
theorem rs0_st (hpre : Pre R kc b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {X bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 k : Nat} (h : RS0 R kc L st pw pl lm x xl s X bp M L1 b1 k) (hk : k < pl)
    {a0 n0 : Nat} (v : Nat) (hn0 : 0 < n0) (ho : pw + 24 * k ≤ a0 ∧ a0 + n0 ≤ pw + 24 * k + 24) :
    RS0 R kc L st pw pl lm x xl s X bp (M.writeLE a0 n0 v) L1 b1 k := by
  have hf := pf_of hpre (by omega)
  have hc := h.c
  have hkp : k * W lm + W lm ≤ NB pl lm := by
    have : (k + 1) * W lm ≤ (pl + 1) * W lm := Nat.mul_le_mul_right _ (by omega)
    simp only [NB]; rw [Nat.add_mul] at this; omega
  refine rs0_rd h (ctx_own hc hf v ⟨hn0, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩) fun a n h0 hr => ?_
  refine Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_
  rcases hr with hr | hr | hr
  · omega
  · omega
  · have hwok := wok_buf (zp := a) (zn := n) hc.scr hr.1 (by omega)
    have := wok_pw hwok hf.pwrt (pw_sep_stk hpre) (a := a0) (n := n0) (by omega) (by omega) (by simp only; omega)
    simp only at this; omega

set_option maxRecDepth 20000 in
/-- an own store into `powers` or the frame (below the `Sl` slots) keeps `buf` -/
theorem keepB_st (hpre : Pre R kc b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) {a0 n0 : Nat} (v : Nat)
    (ho : (pw ≤ a0 ∧ a0 + n0 ≤ pw + 24 * pl) ∨ ((s.regs 4).toNat - 184 ≤ a0 ∧ a0 + n0 ≤ (s.regs 4).toNat + 80)) :
    KeepB bp (NB pl lm) M (M.writeLE a0 n0 v) := by
  intro a n h0 h1 h2
  refine Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ ?_
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  simp only [K] at hK
  have hwok := wok_buf (zp := a) (zn := n) hc.scr h1 h2
  rcases ho with ho | ho
  · have := wok_pw hwok hf.pwrt (pw_sep_stk hpre) (a := a0) (n := n0) ho.1 ho.2 (by simp only; omega)
    simp only at this; omega
  · have := wok_win hwok hf.w (by simp only; omega)
    simp only [K, A] at this; omega

set_option maxRecDepth 20000 in
/-- the operand `x` at a context memory: reads kept (value, normalisation), readable, held, apart from `buf` -/
theorem x_ctx (hpre : Pre R kc b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) :
    natVal M x xl = natVal s.mem x xl ∧ NatNorm M x xl ∧ M.accessible x (8 * xl) false = true ∧
      Held R L1 x (8 * xl) ∧ (0 < xl → Apart bp (8 * NB pl lm) x (8 * xl)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpx, ⟨hx40, hxa, hx48, hxh, hxw⟩, hxn, -, hxs, -⟩ := hpre
  rcases Nat.eq_zero_or_pos xl with h0 | h0
  · subst h0
    refine ⟨by simp [natVal, Janus.Arm64.Memory.readLE], Or.inl rfl, by rw [hc.fr.accessible]; exact hxa,
      hc.le.held hxh, fun h => absurd h (by decide)⟩
  have hrdx : ∀ a n, x ≤ a → a + n ≤ x + 8 * xl → M.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    have h1' := hpx h0
    obtain ⟨h2', h3, -⟩ := hxs h0
    simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at h3
    unfold Apart at h1' h2' h3
    have hLW : ∀ r ∈ LW s pw pl st, r.1 < r.2 → a + n ≤ r.1 ∨ r.2 ≤ a := by
      intro r hr hlt
      simp only [LW, stkWs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl <;> (dsimp only at hlt ⊢; omega)
    rcases hxh with hL' | hR
    · exact lf_read hc.lf (hL'.sub h1 h2) hLW
    · refine frame_read hc.fr fun r hr hlt => ?_
      simp only [AW, List.mem_append] at hr
      rcases hr with (hr | hr) | hr
      · exact MemFrame.outside_mem (hR.of_sub h1 h2) hr
      · simp only [win, K, A, List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [win, K, A, outside_cons, outside_nil, and_true] at hxw
        subst hr; dsimp only; omega
      · exact hLW r (by simp only [LW, List.mem_append]; exact hr) hlt
  have hrd := hrdx x (8 * xl) (Nat.le_refl _) (Nat.le_refl _)
  have hrd1 := hrdx (x + 8 * (xl - 1)) 8 (by omega) (by omega)
  refine ⟨by simp only [natVal]; rw [hrd], ?_, by rw [hc.fr.accessible]; exact hxa, hc.le.held hxh, fun _ => ?_⟩
  · rcases hxn with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hrd1]; exact h)
  · rcases hc.scr.loc with ⟨-, l1, l2⟩ | ⟨hin, hap⟩
    · obtain ⟨-, h3, -⟩ := hxs h0
      simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN] at h3
      unfold Apart at h3 ⊢; omega
    · rcases hxh with hpL | hpO
      · exact hap.apart_of_inRanges hpL
      · exact (hin.apart hpO).symm

end

end FvModexp.Amd64.P2Pre
