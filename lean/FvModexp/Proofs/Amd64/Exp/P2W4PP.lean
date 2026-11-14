import FvModexp.Proofs.Amd64.Exp.P2W4WC
import FvModexp.Proofs.Amd64.Exp.P2QG
import FvModexp.Proofs.Amd64.Nat.StackNatXDefs

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): `WC` at `rsE`, through `(*stack).nat`, and `(*stack).nat`'s precondition
(agent divmc s76, port of divmc s67; amd64 twin of the first half of agent infra's `Arm64.P2W4PP`)

`wc_rs`: the context after the inline `stk.reserve(8w)` from `ent`'s continuation facts (`RsK`); `WC.stkNat`: through
`(*stack).nat`'s Q-form post (`StackNatX.PostQ`; the new nat = a scratch nat relative to the entry); `snPre`:
`StackNatX.PreQ` at a callee entry `RSP = sp - 0x8` (the `CALL` at `RSP = sp` pushed the return address). The callee
window `[sp - 0x8 - stk, sp - 0x8 + above)` lies in `WN` for `stk ≤ K`, `above ≤ 0x300`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

/-- the context at `rsE` -/
theorem wc_rs (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat}
    (hF : MemFrame s.mem M (R.rt ++ [(sp - 0x8 - K, sp + 0x2f8), (sp + 0x318, sp + 0x358), (st, st + 24)]))
    (hLF : LiveFrame s.mem M L [(st, st + 24)]) (hrg : M.regions = s.mem.regions) (hx : LiveExt R L L1)
    (hkf : ArrKF R L st s.mem M) (hlen : stLen M st = stLen s.mem st + 20 * W lm) (hlc : stLen M st ≤ stCap M st)
    (hc40 : stCap M st < 2 ^ 40) (hnl : NatLive M R L1 (stW M st) (stCap M st))
    (hmem : ¬(stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st) → (stW M st, stW M st + 8 * stCap M st) ∈ L1)
    (hinv : R.inv (b1 + stkR (HW (stLen s.mem st) lm) M st) L1 g (view R.rt L1 M)) :
    WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 (stLen s.mem st + 20 * W lm) := by
  obtain ⟨k1, k2, k3, k4, -, k6, -⟩ := hP.stk0
  have hlm : lm ≤ 2 ^ 13 := hP.2.2.2.2.2.1
  have hlm2 : 2 ≤ lm := hP.2.2.2.2.1
  refine ⟨hF.mono fun a k ho => ?_, Expmc.liveFrame_widen hLF fun a k ho => ?_, hrg, hx, hinv,
    ⟨k1, hx.held k2, by rw [hF.accessible]; exact k3, k4, hnl, hlc, hc40⟩, hlen, by omega, k6, hkf,
    fun hn => ⟨hmem hn, by simp only [W] at hlen; omega⟩⟩
  · simp only [WN, ZS, stkWs, List.cons_append, List.nil_append, outside_append, outside_cons, outside_nil,
      and_true] at ho ⊢
    exact ⟨ho.1.1, ho.1.2.1, ho.1.2.2, ho.2.2.1⟩
  · simp only [ZS, stkWs, List.cons_append, List.nil_append, outside_cons, outside_nil, and_true] at ho ⊢
    all_goals exact ho.2.1

variable {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}

set_option maxRecDepth 20000 in
/-- `WC` through `(*stack).nat(n)` entered at `RSP = sp - 0x8` (window `stk ≤ K` below, `above ≤ 0x300` above) -/
theorem WC.stkNat (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ) {stk above n : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 0x300) {S1 s' : State} (hsp : (S1.regs 4).toNat = sp - 0x8) (h14 : (S1.regs 14).toNat = g)
    (hm : S1.mem = M) (hrg : s'.mem.regions = M.regions) (hn : 0 < n)
    (hpost : StackNatX.PostQ R (b1 + stkR (HW (stLen s.mem st) lm) M st) L1 (HW (stLen s.mem st) lm) stk above st n
      S1 s') :
    ∃ (L2 : List (Nat × Nat)) (b2 : Nat), b1 ≤ b2 ∧
      WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem s'.mem L2 b2 (ℓ + StackNat.rnd n) ∧
      Scr R L L2 s.mem s'.mem st (stW s'.mem st + 8 * ℓ) n ∧
      s'.regs 0 = BitVec.ofNat 64 (stW s'.mem st + 8 * ℓ) ∧ s'.regs 3 = BitVec.ofNat 64 n ∧
      s'.regs 1 = BitVec.ofNat 64 n ∧ s'.fsBase = S1.fsBase ∧ s'.df = S1.df ∧
      MemFrame M s'.mem (R.rt ++ [(sp - 0x8 - stk, sp - 0x8 + above)] ++ stkWs M st) := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := (h.cenv hP).2.1
  obtain ⟨hfs, hdf, h0, h3, h1, L2, b2', ⟨hx, hb', hinv'⟩, hok, hlen, hsame, hgrow, hF, hLF, hmemb⟩ := hpost
  subst hm
  rw [h14] at hinv'
  obtain ⟨b2, hinv, hb⟩ := P2Q.effN hinv' hb'
  rw [h.len] at hlen hsame hgrow h0
  have hF' : MemFrame S1.mem s'.mem (R.rt ++ [(sp - 0x8 - stk, sp - 0x8 + above)] ++ stkWs S1.mem st) := by
    simpa only [win, hsp] using hF
  have hsc : Scr R L1 L2 S1.mem s'.mem st (stW s'.mem st + 8 * ℓ) n :=
    Scr.of_post hok hlen hn hsame hgrow h.len.symm
  refine ⟨L2, b2, hb, ?_, Scr.rebase h hsc, h0 hn, h3, h1, hfs, hdf, hF'⟩
  refine h.call (ws := [(sp - 0x8 - stk, sp - 0x8 + above)] ++ stkWs S1.mem st)
    (by rwa [List.append_assoc] at hF')
    hLF hrg ?_ (fun a k hin ho => stk_out h (Or.inl hin) ho) hx hinv hok hlen (by omega) ?_ ?_
  · intro a k o1 o2 o3 o4
    rw [outside_append]
    refine ⟨?_, o3⟩
    simp only [WN, outside_cons, outside_nil, and_true] at o2 ⊢
    omega
  · by_cases hc : ℓ + StackNat.rnd n ≤ stCap S1.mem st
    · exact Or.inl (hsame hc)
    · exact Or.inr (hgrow (by omega))
  · exact ArrIn.of_nat hok.2.2.2.2.2.1 hlen hsame (fun hc => hmemb (by rw [h.len]; omega))

set_option maxRecDepth 20000 in
/-- `(*stack).nat(n)`'s Q-form precondition at its entry (`RSP = sp - 0x8`, `R14 = g`, `FS = fs`) -/
theorem snPre (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ)
    {stk above n : Nat} (hstk : stk ≤ K) (habove : above ≤ 0x360) {S1 : State}
    (hsp : (S1.regs 4).toNat = sp - 0x8) (h14 : (S1.regs 14).toNat = g) (hfsN : S1.fsBase.toNat = fs) (hm : S1.mem = M)
    (hn : n ≤ 2 ^ 16) (hl : ℓ + n + 3 ≤ 2 ^ 16) (hH : ℓ + n + 3 ≤ HW (stLen s.mem st) lm) :
    StackNatX.PreQ R (b1 + stkR (HW (stLen s.mem st) lm) M st) L1 (HW (stLen s.mem st) lm) stk above st n S1 := by
  have hce := h.cenv hP
  have hP' := hP
  have hstf := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, hsv⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsok,
    hstw, hstg, -, harr, hwbf, hwbA, -⟩ := hP'
  have hheld := hsok.2.1
  have hwin : (sp - 0x8) - stk = sp - 0x8 - stk := rfl
  subst hm
  have hK0 := hce.2.1
  unfold Apart at hstw
  refine ⟨CallW.callEnv_of hce hsp h14 hfsN rfl hstk habove (by omega), hsv, h.sok, ?_, ?_, hn,
    by rw [h.len]; omega, ⟨by rw [h.len]; exact hH, Nat.le_add_left _ _⟩, by rw [h14]; exact h.inv,
    by rw [h.fr.accessible]; exact hwbf, hwbA, free_apart h hheld hstf⟩
  · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
  · intro hc0
    rw [h14]
    rcases h.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e2] at hc0; rw [e1, e2]
      obtain ⟨o1, o2, -⟩ := harr hc0
      unfold Apart at o1
      refine ⟨?_, o2⟩
      simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
    · have a1 := hin.apart hP.win_rt
      have a2 := hin.apart hce.2.2.2.2.2.2.2.2.2.1
      unfold Apart at a1 a2 ⊢
      refine ⟨?_, by omega⟩
      simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

end

end FvModexp.Amd64.P2W4
