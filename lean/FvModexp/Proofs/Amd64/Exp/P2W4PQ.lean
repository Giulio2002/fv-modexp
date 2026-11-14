import FvModexp.Proofs.Amd64.Exp.P2W4PP
import FvModexp.Proofs.Amd64.Exp.P2PreDefs

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the callee facts at the table entry (agent divmc s68; amd64 twin of the second
half of agent infra's `Arm64.P2W4PP`)

`EX`: the three entry facts the amd64 table call `buildPrecomputationWindowModPower2` needs beyond `EPre` (its Q-form
`StkSep` asks for `x` and `natOne`'s word apart from the threshold globals, and its `mul` callee reads `X86.HasADX`).
`WC.freeW` (the stack's array/free part apart from a range outside the runtime once the level is positive),
`WC.stkPre` (`Q.NatSqr.StkPre` at a callee entry `RSP = sp - 0x8`), `obj_at`, `natOne_at`, `bu_after`, `scr_apart_bu`
(ISA-independent, as arm64).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

open FvModexp.Amd64.EvenHyp (NatOne natOneA RdIn)

/-- the entry facts beyond `EPre` used at the table call -/
@[reducible] def EX (xp xl : Nat) (s : State) : Prop :=
  (0 < xl → Apart xp (8 * xl) RunIface.gA 32) ∧ Apart (s.mem.readLE natOneA 8) 8 RunIface.gA 32 ∧
    s.mem.accessible Callees.adxAddr 1 false = true

section
variable {R : RtInv} {H : Nat} {L : List (Nat × Nat)} {K g sp st zp zc : Nat} {m0 M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

/-- a range outside the runtime (and apart from the entry array when there was one) is apart from the array and its
free part, once the level is positive -/
theorem WC.freeW (h : WC R H L K g sp st zp zc m0 M L1 b1 ℓ) (hl : 0 < ℓ) {a k : Nat} (hrt : Outside a k R.rt)
    (hf : 0 < stCap m0 st → Apart a k (stW m0 st) (8 * stCap m0 st)) :
    Apart a k (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st)) ∧ Apart a k (stW M st) (8 * stCap M st) := by
  have hc := h.sok.2.2.2.2.2.1
  have hlen := h.len
  rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
  · have := hf (by rw [← e2]; omega)
    rw [← e1, ← e2] at this; unfold Apart at this ⊢; omega
  · have := hin.apart hrt; unfold Apart at this ⊢; omega

end

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ H : Nat}

set_option maxRecDepth 20000 in
/-- `Q.NatSqr.StkPre` at a callee entry `RSP = sp - 0x8` (window `stk ≤ K` below, `above ≤ 0x360` above) -/
theorem WC.stkPre (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) (hl : 0 < ℓ) {stk above : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 0x360) {S : State} (hsp : (S.regs 4).toNat = sp - 0x8) (h14 : (S.regs 14).toNat = g)
    (hfsN : S.fsBase.toNat = fs) (hm : S.mem = M) : Q.NatSqr.StkPre R L1 S stk above st := by
  have hout := hP.win_rt
  obtain ⟨⟨-, -, -, -, -, -, -, -, ⟨-, hK0, hA0, -, -, -, -, -, -, hgrt, -, -, -, -, -, -, -, f5, -⟩, -⟩, ⟨-, -, -, -,
    -, -, -, -, g9, -, -, -, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgO, ⟨-, k2, -⟩, hstw, hstg,
    hstfs, harr, -, hwbA, hstf, hstnz, -⟩ := hP
  subst hm
  have wF := h.freeW hl (hout.of_sub (a := sp - 0x8 - K) (n := K + 0x360) (by omega) (by omega))
    fun hc => by have := (harr hc).1; unfold Apart at this ⊢; omega
  have gF := h.freeW hl hgrt fun hc => by have := (harr hc).2.1; unfold Apart at this ⊢; omega
  have tF := h.freeW hl f5 fun hc => by have := (harr hc).2.2; unfold Apart at this ⊢; omega
  have aF := free_apart h (Or.inr g9) hgO.2.2.2
  have sF := free_apart h k2 hstf
  have hc := h.sok.2.2.2.2.2.1
  have hlen := h.len
  have hnl := h.sok.2.2.2.2.1 (by omega)
  have hgst := hgO.2.2.1
  clear hgO harr hout hstf g9 hgrt f5 k2
  simp only [free] at aF sF
  have sy : ∀ {a n b k : Nat}, Apart a n b k → Apart b k a n := fun h => by unfold Apart at h ⊢; omega
  have eg : g + 16 = Q.NatSqr.guard S := by simp only [Q.NatSqr.guard, h14]
  have et : fs - 8 = Q.NatSqr.tls S := by simp only [Q.NatSqr.tls, hfsN]
  rw [eg] at hstg gF
  rw [et] at hstfs tF
  refine ⟨hstnz, h.sok, ?_, hstg, fun _ => ⟨?_, sy gF.2⟩, sy gF.1, ?_, sF, hwbA,
    (by simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]; exact hnl.2.1.sub (by omega) (by omega)), sy hgst, sy aF,
    hstfs, fun _ => sy tF.2, sy tF.1⟩
  · simp only [win, hsp, outside_cons, outside_nil, and_true]; unfold Apart at hstw; omega
  · have := wF.2; simp only [win, hsp, outside_cons, outside_nil, and_true]; unfold Apart at this; omega
  · have := wF.1
    simp only [win, hsp, outside_cons, outside_nil, and_true, Q.BasicSqr.freeP, Q.BasicSqr.freeN]
    unfold Apart at this; omega

set_option maxRecDepth 20000 in
/-- an entry input nat `(p, n)` (`OE`, readable, normalised, apart from `z`) as a callee at `RSP = sp - 0x8` reads it -/
theorem obj_at (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    {p n : Nat} (hoe : OE R L sp K st s.mem p (8 * n)) (hacc : s.mem.accessible p (8 * n) false = true)
    (h48 : p + 8 * n ≤ 2 ^ 48) (hN : NatNorm s.mem p n) (hn : n ≤ 2 ^ 12)
    (hza : 0 < zc → Apart zp (8 * zc) p (8 * n))
    {S' : State} (hsp : (S'.regs 4).toNat = sp - 0x8) (hm : S'.mem = M) {stk above : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 0x360) :
    RdIn R L1 S' stk above p n ∧ NatNorm M p n ∧ natVal M p n = natVal s.mem p n := by
  have hb := oe_bytes hoe hza
  have hoe' := hoe
  obtain ⟨o1, o2, o3, o4⟩ := hoe'
  subst hm
  have hv : natVal S'.mem p n = natVal s.mem p n := h.readB o1 hb
  refine ⟨⟨by omega, by rw [h.fr.accessible]; exact hacc, h48, h.le.held o1, ?_⟩, ?_, hv⟩
  · unfold Apart at o2
    simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  · rcases Nat.eq_zero_or_pos n with h0 | hn0
    · exact Or.inl h0
    · have hne := hN.resolve_left (by omega)
      right
      rw [h.readB (o1.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega)))
        fun i hi => by have := hb (8 * (n - 1) + i) (by omega); rwa [← Nat.add_assoc] at this]
      exact hne

theorem out_bytes {a k : Nat} {m0 : Memory}
    (ho : Outside a k ([(sp - 0x8 - K, sp + 0x358), (zp, zp + 8 * zc)] ++ stkWs m0 st)) :
    ∀ i, i < k → Outside (a + i) 1 (WN sp K) ∧ Outside (a + i) 1 (ZS zp zc st m0) := by
  intro i hi
  simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢
  omega

set_option maxRecDepth 20000 in
/-- `natOne` at `M`, outside a callee window at `RSP = sp - 0x8`, a window range `[lo, hi)` and the stack's writable
ranges; its word apart from the stack header, free part and the threshold globals -/
theorem natOne_at (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hX : Apart (s.mem.readLE natOneA 8) 8 RunIface.gA 32)
    (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    {S' : State} (hsp : (S'.regs 4).toNat = sp - 0x8) {stk above lo hi : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x360)
    (hlo : sp - 0x8 - K ≤ lo) (hhi : hi ≤ sp + 0x358) :
    ∃ op, NatOne R L1 M op (win S' stk above ++ ([(lo, hi)] ++ stkWs M st)) ∧
      Q.NatSqr.StkSep M st op 8 := by
  have hlc := h.lc0
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, ⟨op, ⟨n0, n8, n16, nw, na, nrt, nwin, oa, o48, oh, ow⟩, -⟩, -⟩ := hP
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
  rw [n0] at hX
  refine ⟨op, ⟨by rw [show natOneA = natOneA + 0 from rfl, hrd 0 (by omega)]; exact n0, by rw [hrd 8 (by omega)]; exact n8,
    by rw [hrd 16 (by omega)]; exact n16, by rw [hO]; exact nw, by rw [h.fr.accessible]; exact na, nrt, ?_,
    by rw [h.fr.accessible]; exact oa, o48, h.le.held oh, ?_⟩, ?_, ?_, hX⟩
  · rw [outside_append, outside_append]
    refine ⟨?_, ?_, sA⟩ <;> simp only [win, hsp, List.cons_append, outside_append, outside_cons, outside_nil, and_true] at nwin ⊢ <;> omega
  · rw [outside_append, outside_append]
    refine ⟨?_, ?_, sO⟩ <;> simp only [win, hsp, List.cons_append, outside_append, outside_cons, outside_nil, and_true] at ow ⊢ <;> omega
  · simp only [stkWs, outside_cons, outside_append] at sO; unfold Apart; omega
  · have := free_apart h oh (by
      simp only [free, stkWs, List.cons_append, List.nil_append, outside_cons, outside_append, outside_nil,
        and_true] at ow ⊢
      unfold Apart; omega)
    simp only [free] at this; simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]; exact this

set_option maxRecDepth 20000 in
/-- **`buildPrecomputationWindowModPower2(stk, powers[:], 2, logM, x)`'s precondition** at its entry `RSP = sp - 0x8`
(`powers` = the sixteen headers at `sp + 0x148`; `[RSP]` = the return address `< 2^47`) -/
theorem ppre (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hX : EX xp xl s)
    (h : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ) {kc : Nat} (hkc : P2Pre.K kc ≤ K)
    (hℓZ : ℓ = stLen s.mem st + 20 * W lm + StackNat.rnd (2 * W lm)) {S2 : State}
    (hsp : S2.regs 4 = BitVec.ofNat 64 (sp - 0x8)) (h14 : S2.regs 14 = BitVec.ofNat 64 g) (hfsN : S2.fsBase.toNat = fs)
    (hx15 : S2.xmm 15 = 0) (hdf : S2.df = false) (hm : S2.mem = M) (hra : M.readLE (sp - 0x8) 8 < 2 ^ 47)
    (hcost : P2Pre.cost 16 lm ≤ b1) :
    P2Pre.Pre R kc b1 L1 st (sp + 0x148) 16 4 lm xp xl S2 := by
  have hce := h.cenv hP
  have hout := hP.win_rt
  have hkc' : 184 + kc ≤ K := hkc
  have hK0 : K ≤ sp - 0x8 := hce.2.1
  have hA0 : sp - 0x8 + 0x360 ≤ 2 ^ 48 := hce.2.2.1
  have hsN : (S2.regs 4).toNat = sp - 0x8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have hgN : (S2.regs 14).toNat = g := by rw [h14, BitVec.toNat_ofNat]; have := hce.2.2.2.2.1; omega
  have hlen := h.len
  have hlm : lm ≤ 2 ^ 13 := hP.2.2.2.2.2.1
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hl0 : 0 < ℓ := by have : 0 < W lm := (by simp only [W]; have := hP.2.2.2.2.1; omega); omega
  have hsi := h.stkPre hP hl0 (stk := P2Pre.K kc) (above := P2Pre.A) hkc (by decide) hsN hgN hfsN hm
  have hgl := h.globals hP (w := win S2 (P2Pre.K kc) P2Pre.A ++ [(sp + 0x148, sp + 0x148 + 24 * 16), (st, st + 24)])
    (fun a n ho => by
      simp only [win, P2Pre.K, P2Pre.A, hsN, List.cons_append, List.nil_append, outside_cons, outside_nil,
        and_true] at ho ⊢
      omega)
  have hone := natOne_at hP hX.2.1 h hsN (stk := P2Pre.K kc) (above := P2Pre.A) (lo := sp + 0x148)
    (hi := sp + 0x148 + 24 * 16) hkc (by decide) (by omega) (by omega)
  have wF := h.freeW hl0 (hout.of_sub (a := sp + 0x148) (n := 24 * 16) (by omega) (by omega)) fun hc => by
    have := (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc).1; unfold Apart at this ⊢; omega
  have hHP : P2Pre.HP (stLen M st) 16 lm = HW (stLen s.mem st) lm := by
    simp only [P2Pre.HP, P2Pre.DPre, P2Pre.NB, HW, hlen, hℓZ]
  obtain ⟨⟨-, -, -, -, -, hal, -, -, ⟨-, -, -, hacc, -, -, -, -, hga, -, -, -, -, -, -, -, -, -, f6⟩, hsv⟩, ⟨-, -, -,
    -, -, -, -, -, -, g10, -, -, -⟩, -, hwt, hlm2, -, -, -, -, -, -, -, hxO, hxa, hx48, hxN, hxl, -, -, -, -, hz, -, -,
    hstw, -, -, -, -, -, -, -, hl16, -⟩ := hP
  have hxo := obj_at h hxO hxa hx48 hxN hxl (fun h0 => (hz h0).2.2.2.2.2.2.1) hsN hm (stk := P2Pre.K kc)
    (above := P2Pre.A) hkc (by decide)
  have sy : ∀ {a n b k : Nat}, Apart a n b k → Apart b k a n := fun h => by unfold Apart at h ⊢; omega
  have eg : g + 16 = Q.NatSqr.guard S2 := by simp only [Q.NatSqr.guard, hgN]
  have et : fs - 8 = Q.NatSqr.tls S2 := by simp only [Q.NatSqr.tls, hfsN]
  rw [eg] at hga
  rw [et] at f6
  have ewt : NatAdd.wordT = StackNat.wT := by decide
  subst hm
  refine ⟨CallW.callEnv_of hce hsN hgN hfsN rfl hkc (by decide) (by simp only [P2Pre.K] at hkc ⊢; omega), hsv, hgl,
    Or.inr rfl, by decide, hlm2, hlm, by omega, by omega, ?_, hout.of_sub (by omega) (by omega), ?_, ?_, ?_,
    ⟨?_, wF.1, ?_⟩, fun _ => ?_, hxo.1, hxo.2.1, hxl, fun h0 => ⟨sy hxO.2.2.1, free_apart h hxO.1 hxO.2.2.2, hX.1 h0⟩,
    hsi, ?_, hone, hcost, by rw [hgN, hHP]; exact h.inv, by rw [ewt]; exact hwt,
    by rw [h.fr.accessible]; exact hX.2.2, by rw [hsN]; exact hra, hx15, hdf⟩
  · exact Janus.Arm64.Memory.accessible_mono _ (hce.2.2.2.1) (by omega) (by omega)
  · simp only [win, P2Pre.K, P2Pre.A, hsN, outside_cons, outside_nil, and_true] at hkc ⊢; omega
  · unfold Apart at hga ⊢; omega
  · unfold Apart at f6 ⊢; omega
  · unfold Apart at hstw ⊢; omega
  · simp only [outside_cons, outside_nil, and_true] at g10; unfold Apart; omega
  · have := hxO.2.1; unfold Apart at this ⊢; omega
  · rw [hlen, hℓZ]; simp only [StackNat.rnd]; omega

end

/-- `BU` of a held object through a step that keeps the stack array (level not lower) or makes a fresh one -/
theorem bu_after {R : RtInv} {L1 : List (Nat × Nat)} {st t n : Nat} {M M' : Memory} (h : P2Pre.BU M st t n)
    (hh : Held R L1 t n) (hkf : ArrKF R L1 st M M') (hl : stLen M st ≤ stLen M' st) : P2Pre.BU M' st t n := by
  rcases hkf with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · simp only [P2Pre.BU, stW, stLen, stCap] at h e1 e2 hl ⊢
    rw [e1, e2]; rcases h with ⟨h1, h2⟩ | h
    · left; omega
    · right; exact h
  · right
    rcases hh with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart; omega
    · have := hin.apart hO; unfold Apart at this ⊢; omega

/-- a scratch nat made by a callee at `M` (relative to `M`) is apart from an object held before with `BU` -/
theorem scr_apart_bu {R : RtInv} {L1 L2 : List (Nat × Nat)} {st t n bp k : Nat} {M M' : Memory}
    (hs : Scr R L1 L2 M M' st bp k) (h : P2Pre.BU M st t n) (hh : Held R L1 t n) (hlc : stLen M st ≤ stCap M st) :
    Apart t n bp (8 * k) := by
  rcases hs.loc with ⟨-, l1, l2⟩ | ⟨hin, hap⟩
  · rcases h with ⟨h1, h2⟩ | h
    · unfold Apart; omega
    · unfold Apart at h ⊢; omega
  · rcases hh with hL | hO
    · have := hap.apart_of_inRanges hL; unfold Apart; omega
    · exact hin.apart hO

end FvModexp.Amd64.P2W4
