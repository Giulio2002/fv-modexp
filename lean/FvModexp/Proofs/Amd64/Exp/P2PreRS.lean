import FvModexp.Proofs.Amd64.Exp.P2PreSk

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the round facts `RS` (with the loop locals `Lo`) through stores and
calls (agent divmc s65; twin of infra's `Arm64/Exp/P2PreRS`)

* `frm_keep`: a frame word at `[RSP - 96, RSP + 80)` survives a callee (`RSP_c = RSP - 184`, above `≤ 88`: the callee's
  window ends at `RSP - 96`).
* `rs_call` / `rs_st` / `rs_own`: `RS` after a callee, after a store into `powers[k]`'s header, after an own frame
  store apart from the locals.
* `memH`, `rs_head`: the round's local stores at the loop body (`i` at `RSP - 56` `+0x3d7`, `3 i` at `RSP - 64`
  `+0x3e5`), in the form the run produces, and the round facts they establish.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.Q.NatSqr (StkSep)

theorem RS.to0 {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm x xl : Nat} {s : State} {X bp : Nat}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 i k : Nat} (h : RS R kc L st pw pl lm x xl s X bp M L1 b1 i k) :
    RS0 R kc L st pw pl lm x xl s X bp M L1 b1 k := ⟨h.c, h.d, h.t⟩

set_option maxRecDepth 20000 in
/-- a frame word at `[RSP - 96, RSP + 80)` survives a callee -/
theorem frm_keep {R : RtInv} {L : List (Nat × Nat)} {s S' : State} {kc st : Nat} {M M' : Memory}
    (hw : WinF R kc s st) (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184) {kC aC : Nat} (hk : kC ≤ kc)
    (ha : aC ≤ 88) {ws : List (Nat × Nat)} (hws : ∀ r ∈ ws, WOK R L s st r)
    (hF : MemFrame M M' (R.rt ++ win S' kC aC ++ ws)) {a : Nat} (h1 : (s.regs 4).toNat ≤ a + 96)
    (h2 : a + 8 ≤ (s.regs 4).toNat + 80) : M'.readLE a 8 = M.readLE a 8 := by
  have hK := hw.sp
  have hrt := hw.rt
  have hk8 := hw.kc8
  simp only [K, A] at hK hrt
  refine frame_read hF fun ⟨r1, r2⟩ hr hr' => ?_
  show a + 8 ≤ r1 ∨ r2 ≤ a
  simp only [List.mem_append, win, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr hr'
  rcases hr with (hr | ⟨rfl, rfl⟩) | hr
  · have := MemFrame.outside_mem (hrt.of_sub (a := a) (n := 8) (by omega) (by omega)) hr
    simp only at this; omega
  · omega
  · have := wok_win (hws _ hr) hw hr'; simp only [K, A] at this; omega

section
variable {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

theorem lo_keep {S' : State} {M M' : Memory} {i : Nat}
    (hw : WinF R kc s st) (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184) {kC aC : Nat} (hk : kC ≤ kc)
    (ha : aC ≤ 88) {wl : List (Nat × Nat)} (hws : ∀ r ∈ wl, WOK R L s st r)
    (hF : MemFrame M M' (R.rt ++ win S' kC aC ++ wl)) (h : Lo s i M) : Lo s i M' := by
  have hK := hw.sp; simp only [K] at hK
  exact ⟨(frm_keep hw hsp hk ha hws hF (by omega) (by omega)).trans h.1,
    (frm_keep hw hsp hk ha hws hF (by omega) (by omega)).trans h.2⟩

/-- **`RS` after a callee** (as `rs0_call`, plus the locals) -/
theorem rs_call {S' : State} {X bp : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 i k : Nat}
    (h : RS R kc L st pw pl lm x xl s X bp M L1 b1 i k)
    (hf : PF R kc L st pw pl s) (hsa : StkSep s.mem st pw (24 * pl))
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184) {kC aC : Nat} (hk : kC ≤ kc) (ha : aC ≤ 88)
    {wl : List (Nat × Nat)} {zp zn : Nat} (hws : ∀ r ∈ wl, r ∈ [(zp, zp + zn)] ++ stkWs M st)
    (hwok : ∀ r ∈ wl, WOK R L s st r) (hz : bp + 8 * (k * W lm) ≤ zp) (hkp : k ≤ pl)
    (hF : MemFrame M M' (R.rt ++ win S' kC aC ++ wl)) (hLF : LiveFrame M M' L1 wl)
    (hc' : Ctx R kc L st pw pl lm x xl s bp M' L2 b2) : RS R kc L st pw pl lm x xl s X bp M' L2 b2 i k := by
  have h0 := rs0_call h.to0 hf hsa hsp hk ha hws hwok hz hkp hF hLF hc'
  exact ⟨h0.c, h0.d, h0.t, lo_keep hf.w hsp hk ha hwok hF h.lo⟩

set_option maxRecDepth 20000 in
/-- **`RS` after an own store** into `powers[k]`'s header -/
theorem rs_st (hpre : Pre R kc b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {X bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 i k : Nat} (h : RS R kc L st pw pl lm x xl s X bp M L1 b1 i k) (hk : k < pl)
    {a0 n0 : Nat} (v : Nat) (hn0 : 0 < n0) (ho : pw + 24 * k ≤ a0 ∧ a0 + n0 ≤ pw + 24 * k + 24) :
    RS R kc L st pw pl lm x xl s X bp (M.writeLE a0 n0 v) L1 b1 i k := by
  have h0 := rs0_st hpre hkc h.to0 hk v hn0 ho
  have hf := pf_of hpre (by omega)
  have hpw := hf.pww
  have hK := hf.w.sp
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hpw hK
  have hkp : 24 * k + 24 ≤ 24 * pl := by omega
  refine ⟨h0.c, h0.d, h0.t, ?_, ?_⟩
  · exact (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)).trans h.lo.1
  · exact (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)).trans h.lo.2

set_option maxRecDepth 20000 in
/-- **`RS` after an own frame store** apart from the locals -/
theorem rs_own (hpre : Pre R kc b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {X bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 i k : Nat} (h : RS R kc L st pw pl lm x xl s X bp M L1 b1 i k) (hkp : k ≤ pl)
    {a0 : Nat} (v : Nat) (h1 : (s.regs 4).toNat - 184 ≤ a0) (h2 : a0 + 8 ≤ (s.regs 4).toNat - 64) :
    RS R kc L st pw pl lm x xl s X bp (M.writeLE a0 8 v) L1 b1 i k := by
  have hf := pf_of hpre (by omega)
  have hpw := hf.pww
  have hK := hf.w.sp
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hpw hK
  have hbw := wok_win (wok_buf (zp := bp) (zn := 8 * NB pl lm) h.c.scr (Nat.le_refl _) (Nat.le_refl _)) hf.w
    (by have := nb_pos (pl := pl) (lm := lm) (by have := pl_facts hpre; omega) (w_facts hpre).1; simp only; omega)
  simp only [K, A] at hbw
  have hrd : ∀ c n, ((pw ≤ c ∧ c + n ≤ pw + 24 * pl) ∨ (bp ≤ c ∧ c + n ≤ bp + 8 * NB pl lm)) →
      (M.writeLE a0 8 v).readLE c n = M.readLE c n := fun c n hc =>
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have hpin : ∀ j, j < k → bp + 8 * (j * W lm) + 8 * W lm ≤ bp + 8 * NB pl lm := fun j hj => by
    have := pw_in (pl := pl) (lm := lm) (bp := bp) (j := j) (by omega); omega
  refine ⟨ctx_own h.c hf v ⟨by omega, Or.inl ⟨h1, by omega⟩⟩, fun j hj => pwd_keep (h.d j hj)
      (fun c n e1 e2 => hrd c n (Or.inl ⟨by omega, by omega⟩))
      (fun c n e1 e2 _ => hrd c n (Or.inr ⟨by omega, by have := hpin j hj; omega⟩)),
    fun j hj hjp => pwt_keep (h.t j hj hjp) (fun c n e1 e2 => hrd c n (Or.inl ⟨by omega, by omega⟩)), ?_, ?_⟩
  · exact (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)).trans h.lo.1
  · exact (Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)).trans h.lo.2

/-- the round locals stored at the loop body's start, in the form the run produces -/
@[reducible] def memH (s : State) (M : Memory) (i : Nat) : Memory :=
  (M.writeLE ((s.regs 4).toNat - 176 + 120) 8 i).writeLE ((s.regs 4).toNat - 176 + 112) 8 (i + i * 2)

set_option maxRecDepth 20000 in
theorem rs_head (hpre : Pre R kc b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 i : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1)
    (hd : ∀ j, j < i → PwD M pw bp lm (natVal s.mem x xl) j) (ht : ∀ j, i ≤ j → j < pl → PwT M pw bp lm j)
    (hip : i + 2 ≤ pl) : RS R kc L st pw pl lm x xl s (natVal s.mem x xl) bp (memH s M i) L1 b1 i i := by
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hK := hf.w.sp
  have hpww := hf.pww
  have hs48 := hf.sp48
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hK hpww hs48
  have hnb : 0 < NB pl lm := Nat.mul_pos (by omega) (by omega)
  have hbw := wok_win (wok_buf (zp := bp) (zn := 8 * NB pl lm) hc.scr (Nat.le_refl _) (Nat.le_refl _)) hf.w
    (by simp only; omega)
  simp only [K, A] at hbw
  have hrd : ∀ c n, ((pw ≤ c ∧ c + n ≤ pw + 24 * pl) ∨ (bp ≤ c ∧ c + n ≤ bp + 8 * NB pl lm)) →
      (memH s M i).readLE c n = M.readLE c n := by
    intro c n h
    simp only [memH]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hpin : ∀ j, j < i → bp + 8 * (j * W lm) + 8 * (2 * W lm) ≤ bp + 8 * NB pl lm := fun j hj =>
    pw_in (by omega)
  have o : ∀ a, (s.regs 4).toNat - 184 ≤ a → a + 8 ≤ (s.regs 4).toNat - 48 → OwnW s pw pl a 8 := fun a h1 h2 => by
    simp only [OwnW]; omega
  refine ⟨ctx_own (ctx_own hc hf _ (o _ (by omega) (by omega))) hf _ (o _ (by omega) (by omega)),
    fun j hj => pwd_keep (hd j hj) (fun c n h1 h2 => hrd c n (Or.inl ⟨by omega, by omega⟩))
      (fun c n h1 h2 _ => hrd c n (Or.inr ⟨by omega, by have := hpin j hj; omega⟩)),
    fun j hj hjp => pwt_keep (ht j (by omega) hjp) (fun c n h1 h2 => hrd c n (Or.inl ⟨by omega, by omega⟩)), ?_, ?_⟩
  · simp only [memH]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      show (s.regs 4).toNat - 56 = (s.regs 4).toNat - 176 + 120 by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [memH]
    rw [show (s.regs 4).toNat - 64 = (s.regs 4).toNat - 176 + 112 by omega, Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (by omega)]
    omega

end

end FvModexp.Amd64.P2Pre
