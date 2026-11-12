import FvModexp.Proofs.Arm64.Exp.P2PreCall

/-!
# `buildPrecomputationWindowModPower2` (arm64): the write-barrier call and the round's own stores (agent infra)

`wbCall`: at a `gcWriteBarrier2` call (`SP' = SP - 208`), the continuation gets the return state with the context
after the two buffer stores and the reads of `powers`, `buf` and the frame `[SP - 216, SP + 80)` unchanged.
`rs_rd`: `RS` from kept reads. `rs_st`: `RS` after an own store into `powers[k]`'s header or the slot `SP - 24`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs)

/-- `gcWriteBarrier2`'s contract address -/
abbrev wbE : Nat := 608160

theorem wbE_eq : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbE := by decide

/-- the ranges whose reads a segment needs kept: `powers`, `buf`, the frame -/
@[reducible] def RdR (s : State) (pw pl lm bp a n : Nat) : Prop :=
  (pw ≤ a ∧ a + n ≤ pw + 24 * pl) ∨ (bp ≤ a ∧ a + n ≤ bp + 8 * NB pl lm) ∨
    (s.sp.toNat - 216 ≤ a ∧ a + n ≤ s.sp.toNat + 80)

/-- the two buffer stores after the barrier -/
@[reducible] def W2 (m : Memory) (buf v1 v2 : Nat) : Memory := (m.writeLE buf 8 v1).writeLE (buf + 8) 8 v2

/-- reads of a held range are kept by a store into a runtime range apart from the live set -/
theorem rd_rtw {R : RtInv} {L1 : List (Nat × Nat)} {M : Memory} {a k v c n : Nat} (hin : InRanges a k R.rt)
    (hap : ApartAll a k L1) (hh : Held R L1 c n) (h0 : 0 < n) (hk : 0 < k) :
    (M.writeLE a k v).readLE c n = M.readLE c n := by
  refine Memory.readLE_writeLE_of_disjoint _ _ ?_
  rcases hh with hL | hO
  · have := hap.apart_of_inRanges hL; unfold Apart at this; omega
  · have := hin.apart hO; unfold Apart at this; omega

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the ranges of `RdR` are held and apart from the barrier's window `[SP' - 4096, SP' - 8)` -/
theorem rdr_held (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {a n : Nat} (h0 : 0 < n)
    (h : RdR s pw pl lm bp a n) :
    Held R L1 a n ∧ (a + n ≤ s.sp.toNat - 208 - 4096 ∨ s.sp.toNat - 208 - 8 ≤ a) := by
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  have hrt := hf.w.rt
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hK hrt hpww
  rcases h with h | h | h
  · exact ⟨Or.inr (hf.pwrt.of_sub h.1 h.2), by omega⟩
  · have hwok := wok_buf (zp := a) (zn := n) hc.scr h.1 h.2
    have hwin := wok_win hwok hf.w (by simp only; omega)
    simp only [K, A] at hwin
    exact ⟨hc.scr.held.sub h.1 h.2, by omega⟩
  · exact ⟨Or.inr (hrt.of_sub (by omega) (by omega)), by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`gcWriteBarrier2`** called at `S` (`SP' = SP - 208`, return address in `X30`) -/
theorem wbCall (hwb : WbLiveContract (LibExp.program.link impl) wbE 4096 R 2)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {r : W64} {Q : State → Prop}
    {S : State} (hpc : S.pc = BitVec.ofNat 64 wbE) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 208))
    (h28 : S.regs 28 = s.regs 28) (hm : S.mem = M) {ra : Nat} (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (hra4 : ra % 4 = 0) (hra48 : ra < 2 ^ 48)
    (k : ∀ (buf : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m' : Memory)
      (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      buf.toNat + 16 ≤ 2 ^ 48 → buf.toNat % 8 = 0 → m'.accessible buf.toNat 16 true = true →
      (∀ v1 v2, Ctx R kc L st pw pl lm s bp (W2 m' buf.toNat v1 v2) L1 b1) →
      (∀ v1 v2 a n, 0 < n → RdR s pw pl lm bp a n → (W2 m' buf.toNat v1 v2).readLE a n = M.readLE a n) →
      ReachesRet (LibExp.program.link impl) r (wbRetX S junk buf f v m' ex ep) Q) :
    ReachesRet (LibExp.program.link impl) r S Q := by
  have hf := pf_of hpre (by omega)
  have hspN : S.sp.toNat = s.sp.toNat - 208 := by
    rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)
  have hce := callEnv_ctx hpre hc hsp h28 hm (stk := 4096) (above := 8) (by omega) (by omega)
  obtain ⟨-, ⟨hal, hb', ha8, hw⟩, -, hout, -, -, hLs, -⟩ := hce
  simp only [win] at hLs
  have hsv := hpre.2.1
  have hok : R.ok wbE [2] := by rw [← wbE_eq]; exact hsv.2.2.2.2.2.1 [2]
  refine ReachesRet.call_regions (hwb L1 b1) hpc ⟨⟨?_, ?_, hal, hb', by omega, by omega, ?_⟩, hok, ?_, ?_, ?_⟩ ?_
  · rw [h30, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ra < 2 ^ 64 by omega)]; exact hra4
  · rw [h30, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ra < 2 ^ 64 by omega)]; exact hra48
  · exact Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)
  · rw [h28, hm]; exact hc.inv
  · intro r' hr'
    have := hLs r' hr'
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  · intro r' hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hout.of_sub (by omega) (by simp only; omega)
  intro S2 _ ⟨buf, junk, f2, v2, m', ex2, ep2, hs2, hfr2, hlf2, hsl, hapL, hapW, hinvS⟩ hrg0
  subst hs2
  rw [hm, hspN] at hfr2
  rw [hm] at hlf2
  rw [h28] at hinvS
  have hsl' := hsl
  obtain ⟨hbR, hb48, hbacc, hbal⟩ := hsl'
  have hrg : m'.regions = M.regions := by rw [← hm]; exact hrg0
  refine k buf junk f2 v2 m' ex2 ep2 hb48 hbal hbacc (fun v1 v2 => ?_) (fun v1 v2 a n h0 hr => ?_)
  · exact ctx_wb hc hf (by omega) hspN (by rw [hspN]; exact hfr2) hlf2 (by rw [← hm] at hrg ⊢; exact hrg) hsl hapL
      hinvS v1 v2
  · obtain ⟨hh, hwin⟩ := rdr_held hpre hkc hc h0 hr
    have hh' : Held R L1 a n := hh
    simp only [W2]
    rw [rd_rtw (hbR.sub (a := buf.toNat + 8) (n := 8) (by omega) (by omega))
        (ApartAll.sub' (a := buf.toNat + 8) (n := 8) hapL (by omega) (by omega)) hh' h0 (by omega),
      rd_rtw (hbR.sub (a := buf.toNat) (n := 8) (Nat.le_refl _) (by omega))
        (ApartAll.sub' (a := buf.toNat) (n := 8) hapL (Nat.le_refl _) (by omega)) hh' h0 (by omega)]
    rcases hh with hL | hO
    · exact lf_read hlf2 hL (by simp)
    · refine frame_read hfr2 fun r' hr' hr'' => ?_
      simp only [List.mem_append, List.mem_singleton] at hr'
      rcases hr' with hr' | rfl
      · have := MemFrame.outside_mem hO hr'; omega
      · simp only at hr'' ⊢; omega

/-- `RS` from kept reads (`powers` except `powers[k]`'s header, `buf` below `powers[k]`, the `Lo` slots) -/
theorem rs_rd {X bp : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 i k : Nat}
    (h : RS R kc L st pw pl lm s X bp M L1 b1 i k) (hc' : Ctx R kc L st pw pl lm s bp M' L2 b2)
    (hK : 216 ≤ s.sp.toNat) (hrd : ∀ a n, 0 < n → ((pw ≤ a ∧ a + n ≤ pw + 24 * k) ∨ (pw + 24 * k + 24 ≤ a ∧ a + n ≤ pw + 24 * pl) ∨
      (bp ≤ a ∧ a + n ≤ bp + 8 * (k * W lm)) ∨ (s.sp.toNat - 88 ≤ a ∧ a + n ≤ s.sp.toNat - 64) ∨
      (s.sp.toNat - 16 ≤ a ∧ a + n ≤ s.sp.toNat - 8)) → M'.readLE a n = M.readLE a n) :
    RS R kc L st pw pl lm s X bp M' L2 b2 i k := by
  refine ⟨hc', fun j hj => ?_, fun j hj hjp => pwt_keep (h.t j hj hjp) fun a n h1 h2 => ?_, ?_⟩
  · have hjk := pw_sep (lm := lm) hj
    refine pwd_keep (h.d j hj) (fun a n h1 h2 => ?_) fun a n h1 h2 h0 => hrd a n h0 (Or.inr (Or.inr (Or.inl
      ⟨by omega, by omega⟩)))
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp [Memory.readLE]
    · exact hrd a n h0 (Or.inl ⟨by omega, by omega⟩)
  · rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp [Memory.readLE]
    · exact hrd a n h0 (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · obtain ⟨e0, e1, e2, e3⟩ := h.lo
    exact ⟨(hrd _ 8 (by omega) (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans e0,
      (hrd _ 8 (by omega) (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans e1,
      (hrd _ 8 (by omega) (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans e2,
      (hrd _ 8 (by omega) (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))).trans e3⟩

set_option maxRecDepth 20000 in
/-- **`RS` after an own store** into `powers[k]`'s header or the slot `SP - 24` -/
theorem rs_st (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {X bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 i k : Nat} (h : RS R kc L st pw pl lm s X bp M L1 b1 i k) (hk : k < pl)
    {a0 n0 : Nat} (v : Nat) (hn0 : 0 < n0)
    (ho : (pw + 24 * k ≤ a0 ∧ a0 + n0 ≤ pw + 24 * k + 24) ∨ (s.sp.toNat - 24 ≤ a0 ∧ a0 + n0 ≤ s.sp.toNat - 16)) :
    RS R kc L st pw pl lm s X bp (M.writeLE a0 n0 v) L1 b1 i k := by
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hK hpww
  have hc := h.c
  have hkp : k * W lm + W lm ≤ NB pl lm := by
    have : (k + 1) * W lm ≤ (pl + 1) * W lm := Nat.mul_le_mul_right _ (by omega)
    simp only [NB]; rw [Nat.add_mul] at this; omega
  refine rs_rd h (ctx_own hc hf v ⟨hn0, by rcases ho with ho | ho <;> omega⟩) (by omega) fun a n h0 hr => ?_
  refine Memory.readLE_writeLE_of_disjoint _ _ ?_
  rcases hr with hr | hr | hr | hr | hr
  · omega
  · omega
  · have hwok := wok_buf (zp := a) (zn := n) hc.scr hr.1 (by omega)
    have hwin := wok_win hwok hf.w (by simp only; omega)
    simp only [K, A] at hwin
    rcases ho with ho | ho
    · have := wok_pw hwok hf.pwrt (hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by omega) (a := a0) (n := n0) (by omega)
        (by omega) (by simp only; omega)
      simp only at this; omega
    · omega
  · omega
  · omega

theorem lo2_st (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {M : Memory} {i a0 n0 : Nat}
    (v : Nat) (h : Lo2 s pw i M) (ho : pw ≤ a0 ∧ a0 + n0 ≤ pw + 24 * pl) : Lo2 s pw i (M.writeLE a0 n0 v) := by
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hK hpww
  simp only [Lo2] at h ⊢
  rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h

theorem lo2_set {M : Memory} {i a0 v : Nat} (ha : a0 = s.sp.toNat - 24) (he : v = pw + 24 * i + 24)
    (hv : v < 2 ^ 64) : Lo2 s pw i (M.writeLE a0 8 v) := by
  subst ha
  simp only [Lo2]
  rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt hv, he]

theorem lo2_rd (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {M M' : Memory} {i : Nat}
    (h : Lo2 s pw i M) (hrd : ∀ a n, 0 < n → s.sp.toNat - 216 ≤ a → a + n ≤ s.sp.toNat + 80 → M'.readLE a n = M.readLE a n) :
    Lo2 s pw i M' := by
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  simp only [K] at hK
  simp only [Lo2] at h ⊢
  rw [hrd _ 8 (by omega) (by omega) (by omega)]; exact h

/-- the reads of `buf` are kept -/
@[reducible] def KeepB (bp nb : Nat) (M M' : Memory) : Prop :=
  ∀ a n, 0 < n → bp ≤ a → a + n ≤ bp + 8 * nb → M'.readLE a n = M.readLE a n

theorem keepB_trans {bp nb : Nat} {M M' M'' : Memory} (h1 : KeepB bp nb M M') (h2 : KeepB bp nb M' M'') :
    KeepB bp nb M M'' := fun a n h0 ha hb => (h2 a n h0 ha hb).trans (h1 a n h0 ha hb)

theorem keepB_refl (bp nb : Nat) (M : Memory) : KeepB bp nb M M := fun _ _ _ _ _ => rfl

/-- a nat inside `buf`: value and normalisation transfer -/
theorem nat_keepB {bp nb : Nat} {M M' : Memory} (h : KeepB bp nb M M') {p l : Nat} (h1 : bp ≤ p)
    (h2 : p + 8 * l ≤ bp + 8 * nb) : natVal M' p l = natVal M p l ∧ (NatNorm M p l → NatNorm M' p l) := by
  refine ⟨?_, fun hn => ?_⟩
  · rcases Nat.eq_zero_or_pos l with rfl | h0
    · simp [natVal, Memory.readLE]
    · exact h p (8 * l) (by omega) h1 h2
  · rcases Nat.eq_zero_or_pos l with h0 | h0
    · exact Or.inl h0
    rcases hn with hn | hn
    · exact Or.inl hn
    · refine Or.inr ?_
      rw [h _ 8 (by omega) (by omega) (by omega)]
      exact hn

set_option maxRecDepth 20000 in
/-- an own store into `powers` or the frame keeps `buf` -/
theorem keepB_st (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {a0 n0 : Nat} (v : Nat)
    (ho : (pw ≤ a0 ∧ a0 + n0 ≤ pw + 24 * pl) ∨ (s.sp.toNat - 216 ≤ a0 ∧ a0 + n0 ≤ s.sp.toNat + 80)) :
    KeepB bp (NB pl lm) M (M.writeLE a0 n0 v) := by
  intro a n h0 h1 h2
  refine Memory.readLE_writeLE_of_disjoint _ _ ?_
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  simp only [K, A] at hK
  have hwok := wok_buf (zp := a) (zn := n) hc.scr h1 h2
  have hwin := wok_win hwok hf.w (by simp only; omega)
  simp only [K, A] at hwin
  have hpl4 := (pl_facts hpre).1
  rcases ho with ho | ho
  · have := wok_pw hwok hf.pwrt (hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by omega) (a := a0) (n := n0) ho.1 ho.2
      (by simp only; omega)
    simp only at this; omega
  · omega

theorem p2_even {lm X i : Nat} (h2 : 2 ≤ i) (he : i % 2 = 0) :
    Exp.p2Pow lm X i = Exp.p2Pow lm X (i / 2) * Exp.p2Pow lm X (i / 2) % 2 ^ lm := by
  rw [Exp.p2Pow]; simp only [show i ≠ 0 by omega, show i ≠ 1 by omega, he, dite_false, if_true]

theorem p2_odd {lm X i : Nat} (h2 : 2 ≤ i) (he : i % 2 = 0) :
    Exp.p2Pow lm X (i + 1) = Exp.p2Pow lm X i * Exp.p2Pow lm X 1 % 2 ^ lm := by
  rw [Exp.p2Pow]
  simp only [show i + 1 ≠ 0 by omega, show i + 1 ≠ 1 by omega, show (i + 1) % 2 ≠ 0 by omega, dite_false,
    if_false, Nat.add_sub_cancel]
  rw [show Exp.p2Pow lm X 1 = X % 2 ^ lm by rw [Exp.p2Pow]; simp]

end

section
variable {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm : Nat} {s : State}

/-- `RS`, `Lo2` and `KeepB` from kept `RdR` reads (e.g. through the write barrier) -/
theorem rs_of_rdr {X bp : Nat} {M M' : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 i k : Nat}
    (h : RS R kc L st pw pl lm s X bp M L1 b1 i k) (hc' : Ctx R kc L st pw pl lm s bp M' L2 b2)
    (hK : 216 ≤ s.sp.toNat) (hk : k ≤ pl)
    (hrd : ∀ a n, 0 < n → RdR s pw pl lm bp a n → M'.readLE a n = M.readLE a n) :
    RS R kc L st pw pl lm s X bp M' L2 b2 i k ∧ (Lo2 s pw i M → Lo2 s pw i M') ∧ KeepB bp (NB pl lm) M M' := by
  have hkn : k * W lm ≤ NB pl lm := Nat.le_trans (Nat.mul_le_mul_right _ hk) (Nat.mul_le_mul_right _ (by omega))
  refine ⟨rs_rd h hc' hK fun a n h0 hr => hrd a n h0 ?_, fun h2 => ?_, fun a n h0 h1 h2 => hrd a n h0 ?_⟩
  · simp only [RdR]; omega
  · simp only [Lo2] at h2 ⊢; rw [hrd _ 8 (by omega) (by simp only [RdR]; omega)]; exact h2
  · simp only [RdR]; omega

end

end FvModexp.Arm64.P2Pre
