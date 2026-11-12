import FvModexp.Proofs.Arm64.Exp.P2W2WC
import FvModexp.Proofs.Arm64.Exp.P2PreDefs

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): `WC` at `rsE`, through `stk.nat`, and the callee preconditions of
`(*stack).nat` and `buildPrecomputationWindowModPower2` at `SP = sp` (agent infra)

`wc_rs`: the context after the inline `stk.reserve(8w)` from `ent`'s continuation facts (`RsK`); `WC.stkNat`: through
`(*stack).nat`'s `PostL` (new nat = scratch relative to the entry); `snPre`: `StackNat.Pre`; `ppre`: `P2Pre.Pre` at the
table's entry (`powers` = `sp + 320 … sp + 416`, `windowSize = 2`, `len = 4`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.EvenHyp

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}

/-- the context at `rsE` -/
theorem wc_rs (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hF : MemFrame s.mem M (R.rt ++ [(sp - K, sp + 456), (sp + 472, sp + 560), (st, st + 24)]))
    (hLF : LiveFrame s.mem M L [(st, st + 24)]) (hrg : M.regions = s.mem.regions) (hx : LiveExt R L L1)
    (hkf : ArrKF R L st s.mem M) (hlen : stLen M st = stLen s.mem st + 8 * W lm) (hlc : stLen M st ≤ stCap M st)
    (hc40 : stCap M st < 2 ^ 40) (hnl : NatLive M R L1 (stW M st) (stCap M st))
    (hmem : ¬(stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st) → (stW M st, stW M st + 8 * stCap M st) ∈ L1)
    (hinv : R.inv b1 L1 g (view R.rt L1 M)) :
    WC R L K g sp st zp zc s.mem M L1 b1 (stLen s.mem st + 8 * W lm) := by
  obtain ⟨k1, k2, k3, k4, -, k6, -⟩ := hP.stk0
  refine ⟨hF.mono fun a k ho => ?_, Expmc.liveFrame_widen hLF fun a k ho => ?_, hrg, hx, hinv,
    ⟨k1, hx.held k2, by rw [hF.accessible]; exact k3, k4, hnl, hlc, hc40⟩, hlen, by omega, k6, hkf, hmem⟩
  · simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_append, outside_cons, outside_nil,
      and_true] at ho ⊢
    exact ⟨ho.1.1, ho.1.2.1, ho.1.2.2, ho.2.2.1⟩
  · simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢
    all_goals exact ho.2.1

variable {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- `WC` through `(*stack).nat(n)` called at `SP = sp` (window `stk ≤ K` below, `above ≤ 88` above) -/
theorem WC.stkNat (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {stk above n : Nat} (hstk : stk ≤ K) (habove : above ≤ 88)
    {S1 s' : State} (hsp : S1.sp.toNat = sp) (h28 : (S1.regs 28).toNat = g) (hm : S1.mem = M) (hrg : s'.mem.regions = M.regions) (hn : 0 < n)
    (hpost : StackNat.PostL R b1 L1 stk above st n S1 s') :
    ∃ (L2 : List (Nat × Nat)) (b2 : Nat), b1 - stackNatCost ℓ n ≤ b2 ∧
      WC R L K g sp st zp zc s.mem s'.mem L2 b2 (ℓ + StackNat.rnd n) ∧
      Scr R L L2 s.mem s'.mem st (stW s'.mem st + 8 * ℓ) n ∧
      s'.regs 0 = BitVec.ofNat 64 (stW s'.mem st + 8 * ℓ) ∧ s'.regs 1 = BitVec.ofNat 64 n ∧
      s'.regs 2 = BitVec.ofNat 64 n ∧ MemFrame M s'.mem (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ stkWs M st) := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  obtain ⟨h0, h1, h2, L2, b2, ⟨hx, hb, hinv⟩, hok, hlen, hsame, hgrow, hF, hLF, hmemb⟩ := hpost
  subst hm
  rw [h28] at hinv
  rw [h.len] at hlen hsame hgrow hb h0
  have hF' : MemFrame S1.mem s'.mem (R.rt ++ [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ stkWs S1.mem st) := by
    simpa only [winA, hsp] using hF
  have hsc : Scr R L1 L2 S1.mem s'.mem st (stW s'.mem st + 8 * ℓ) n :=
    Scr.of_post hok hlen hn hsame hgrow h.len.symm
  refine ⟨L2, b2, hb, ?_, Scr.rebase h hsc, h0 hn, h1, h2, hF'⟩
  refine h.call (ws := [(sp - stk, sp - 8), (sp + 8, sp + above)] ++ stkWs S1.mem st) (by rwa [List.append_assoc] at hF')
    hLF hrg ?_ (fun a k hin ho => stk_out h (Or.inl hin) ho) hx hinv hok hlen (by omega) ?_ ?_
  · intro a k o1 o2 o3 o4
    rw [outside_append]
    refine ⟨?_, o3⟩
    simp only [WN, outside_cons, outside_nil, and_true] at o2 ⊢
    exact ⟨by omega, by omega⟩
  · by_cases hc : ℓ + StackNat.rnd n ≤ stCap S1.mem st
    · exact Or.inl (hsame hc)
    · exact Or.inr (hgrow (by omega))
  · intro hne
    by_cases hc : ℓ + StackNat.rnd n ≤ stCap S1.mem st
    · exact absurd (hsame hc) hne
    · exact hmemb (by rw [h.len]; omega)

/-- `(*stack).nat(n)`'s precondition at `SP = sp` -/
theorem snPre (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {stk above n : Nat} (hstk : stk ≤ K) (habove : above ≤ 88) {S1 : State} (hsp : S1.sp = BitVec.ofNat 64 sp)
    (h28 : S1.regs 28 = BitVec.ofNat 64 g) (hm : S1.mem = M) (hn : n ≤ 2 ^ 16) (hl : ℓ + n + 3 ≤ 2 ^ 16)
    (hb : stackNatCost ℓ n ≤ b1) : StackNat.Pre R b1 L1 stk above st n S1 := by
  have hce := h.cenv hP
  have hsN : S1.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; have := hce.2.2.1; omega
  have hgN : (S1.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; have := hce.2.2.2.2.1; omega
  have hsi := h.stkIn hP hsN hgN hm hstk habove
  have hst := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwbf := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwbA := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsv := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hheld := hP.stk0.2.1
  subst hm
  refine ⟨CallW.callEnv_of hce hsp h28 rfl (by omega) habove, hsv, h.sok, hsi.2.1, hsi.2.2.2, hn,
    by rw [h.len]; omega, by rw [h.len]; exact hb, by rw [hgN]; exact h.inv, by rw [h.fr.accessible]; exact hwbf, hwbA,
    ?_⟩
  exact free_apart h hheld hst

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- an entry input nat `(p, n)` (`OE`, readable, normalised, apart from `z`) as a callee at `SP = sp` reads it -/
theorem obj_at (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {p n : Nat} (hoe : OE R L sp K st s.mem p (8 * n)) (hacc : s.mem.accessible p (8 * n) false = true)
    (h48 : p + 8 * n ≤ 2 ^ 48) (hN : NatNorm s.mem p n) (hn : n ≤ 2 ^ 12)
    (hza : 0 < zc → Apart zp (8 * zc) p (8 * n))
    {S' : State} (hsp : S'.sp.toNat = sp) (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 88) :
    ExpHyp.RdIn R L1 S' stk above p n ∧ NatNorm M p n ∧ StkApart M st p (8 * n) ∧ natVal M p n = natVal s.mem p n := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hb := oe_bytes hP hoe hza
  have hoe' := hoe
  obtain ⟨o1, o2, o3, o4⟩ := hoe'
  subst hm
  have hv : natVal S'.mem p n = natVal s.mem p n := h.readB o1 hb
  refine ⟨⟨by omega, by rw [h.fr.accessible]; exact hacc, h48, h.le.held o1, ?_⟩, ?_, fun hn0 => ⟨o3, ?_⟩, hv⟩
  · unfold Apart at o2
    simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  · rcases Nat.eq_zero_or_pos n with h0 | hn0
    · exact Or.inl h0
    · have hne := hN.resolve_left (by omega)
      right
      rw [h.readB (o1.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega)))
        fun i hi => by have := hb (8 * (n - 1) + i) (by omega); rwa [← Nat.add_assoc] at this]
      exact hne
  · exact fun _ => free_apart h o1 o4
end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

theorem out_bytes {a k : Nat} {m0 : Memory} (ho : Outside a k ([(sp - K, sp + 560), (zp, zp + 8 * zc)] ++ stkWs m0 st)) :
    ∀ i, i < k → Outside (a + i) 1 (WN sp K) ∧ Outside (a + i) 1 (ZS zp zc st m0) := by
  intro i hi
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢
  omega

set_option maxRecDepth 20000 in
/-- `natOne` at `M`, outside a callee window at `SP = sp`, a window range `[lo, hi)` and the stack's writable ranges -/
theorem natOne_at (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {S' : State} (hsp : S'.sp.toNat = sp) {stk above lo hi : Nat} (hstk : stk ≤ K) (habove : above ≤ 88)
    (hlo : sp - K ≤ lo) (hhi : hi ≤ sp + 560) :
    ∃ op, NatOne R L1 M op (winA S' stk above ++ ([(lo, hi)] ++ stkWs M st)) ∧ StkApart M st op 8 := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hlc := h.lc0
  obtain ⟨op, ⟨n0, n8, n16, nw, na, nrt, nwin, oa, o48, oh, ow⟩, -⟩ :=
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have bA := out_bytes nwin
  have bO := out_bytes ow
  have hrd : ∀ j, j + 8 ≤ 24 → M.readLE (natOneA + j) 8 = s.mem.readLE (natOneA + j) 8 := fun j hj =>
    h.readB (Or.inr (nrt.of_sub (by omega) (by omega))) fun i hi => by
      have := bA (j + i) (by omega); rwa [← Nat.add_assoc] at this
  have hO : M.readLE op 8 = s.mem.readLE op 8 := h.readB oh bO
  have sA : Outside natOneA 24 (stkWs M st) :=
    stk_out h (Or.inr nrt) (by simp only [ZS, List.cons_append, List.nil_append, outside_cons, outside_append] at nwin ⊢; exact nwin.2)
  have sO : Outside op 8 (stkWs M st) :=
    stk_out h oh (by simp only [ZS, List.cons_append, List.nil_append, outside_cons, outside_append] at ow ⊢; exact ow.2)
  refine ⟨op, ⟨by rw [show natOneA = natOneA + 0 from rfl, hrd 0 (by omega)]; exact n0, by rw [hrd 8 (by omega)]; exact n8,
    by rw [hrd 16 (by omega)]; exact n16, by rw [hO]; exact nw, by rw [h.fr.accessible]; exact na, nrt, ?_,
    by rw [h.fr.accessible]; exact oa, o48, h.le.held oh, ?_⟩, fun _ => ⟨?_, fun _ => ?_⟩⟩
  · rw [outside_append, outside_append]
    refine ⟨?_, ?_, sA⟩ <;> simp only [winA, hsp, List.cons_append, outside_append, outside_cons, outside_nil, and_true] at nwin ⊢ <;> omega
  · rw [outside_append, outside_append]
    refine ⟨?_, ?_, sO⟩ <;> simp only [winA, hsp, List.cons_append, outside_append, outside_cons, outside_nil, and_true] at ow ⊢ <;> omega
  · simp only [stkWs, outside_cons, outside_append] at sO; unfold Apart; omega
  · refine free_apart h oh ?_
    simp only [free, stkWs, List.cons_append, List.nil_append, outside_cons, outside_append, outside_nil, and_true] at ow ⊢
    unfold Apart; omega

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- **`buildPrecomputationWindowModPower2(stk, powers[:], 2, logM, x)`'s precondition** at `SP = sp`
(`powers` = the four headers at `sp + 320`) -/
theorem ppre (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ)
    {kcP : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} (hkc : 208 + kcP ≤ K)
    (hℓ : ℓ + 2 ^ 12 ≤ 2 ^ 16) {S2 : State} (hsp : S2.sp = BitVec.ofNat 64 sp) (h28 : S2.regs 28 = BitVec.ofNat 64 g)
    (hm : S2.mem = M) (h30 : S2.regs 30 = BitVec.ofNat 64 1795572) (hcost : P2Pre.cost sqC mlC ℓ 4 lm ≤ b1) :
    P2Pre.Pre R kcP sqC mlC b1 L1 st (sp + 320) 4 2 lm xp xl S2 := by
  have hce := h.cenv hP
  have hsN : S2.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; have := hce.2.2.1; omega
  have hgN : (S2.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; have := hce.2.2.2.2.1; omega
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hout := hP.win_rt
  have hsi := h.stkIn hP hsN hgN hm (stk := 208 + kcP) (above := 80) hkc (by omega)
  have hgl := h.globals hP (w := winA S2 (P2Pre.K kcP) P2Pre.A ++ [(sp + 320, sp + 320 + 24 * 4), (st, st + 24)])
    (fun a n ho => by
      simp only [winA, P2Pre.K, P2Pre.A, hsN, List.cons_append, List.nil_append, outside_cons, outside_nil,
        and_true] at ho ⊢
      omega)
  have hone := natOne_at hP h hsN (stk := 208 + kcP) (above := 80) (lo := sp + 320) (hi := sp + 320 + 24 * 4) hkc
    (by omega) (by omega) (by omega)
  have hxo := obj_at hP h hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun h0 => (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0).2.2.2.2.2.1) hsN hm (stk := 208 + kcP)
    (above := 80) hkc (by omega)
  have hlc := h.lc0
  have hlen := h.len
  have hlo := h.lo
  obtain ⟨he, hK20, -, hro, hty, hlm2, hlm, hyO, hya, hy48, hyN, hyl, hyl', hxO, hxa, hx48, hxN, hxl, hxp, hxc,
    hzp, hzc, hz, hgO, hsok, hstw, hstg, harr, hwbf, hwbA, hstf, hstnz, hl16, -, hinv⟩ := hP
  obtain ⟨-, -, -, -, -, hgo, hal, -, -, hsp2, hacc, -, -, -, hsv⟩ := he
  simp only [outside_cons] at hgo
  have hfa := free_apart' h (hout.of_sub (a := sp + 320) (n := 24 * 4) (by omega) (by omega))
  subst hm
  refine ⟨CallW.callEnv_of hce hsp h28 rfl (by simp only [P2Pre.K]; omega) (by simp only [P2Pre.A]; omega), hsv, ?_,
    Or.inl rfl, by decide, hlm2, hlm, by omega, by omega, ?_, hout.of_sub (by omega) (by omega), ?_, ?_, ?_, ?_,
    hxo.1, hxo.2.1, hxl, hxo.2.2.1, hsi, by rw [hlen]; omega, free_apart h hsok.2.1 hstf, ?_, by rw [hlen]; exact hcost,
    by rw [hgN]; exact h.inv, by rw [h30]; decide, by rw [h30]; decide, ?_, ?_, hstnz⟩
  · exact hgl
  · rw [h.fr.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega)
  · simp only [win, P2Pre.K, P2Pre.A, hsN, outside_cons, outside_nil, and_true]; omega
  · rw [hgN]; unfold Apart; omega
  · intro _
    refine ⟨by unfold Apart at hstw ⊢; omega, hfa fun hc0 => ?_⟩
    have := (harr hc0).1; unfold Apart at this ⊢; omega
  · intro _; have := hxO.2.1; unfold Apart at this ⊢; omega
  · exact hone
  · exact hgO.2.2.1.symm
  · exact (free_apart h hgO.1 hgO.2.2.2).symm
end

end FvModexp.Arm64.P2W2
