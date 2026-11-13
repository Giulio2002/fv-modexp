import FvModexp.Proofs.Arm64.Exp.P2W2BC

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): callee-precondition pieces at `SP = sp` inside the loop body (agent infra)

`bodyEnv` (callee environment, globals, the `*stack` facts `StkIn` / `StkX`), `BC.arg` (a buffer of either class as a
callee's output / input array), `tbl_arg` (a table entry `powers[j]` as an input), `bc_apart` (the two buffer
classes are apart), `ub_res` (a fresh callee result is a U-class buffer).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn WrOut)

theorem lL_bd (ℓ0 lm : Nat) : lvlL ℓ0 lm ≤ ℓ0 + 15 * W lm + 6 := by
  simp only [lvlL, lvlZ, lvlR, StackNat.rnd, P2Pre.NB, P2Pre.W, W]; omega

theorem ofNat_inj' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) :
    a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {ret : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 zzp bp : Nat}

set_option maxRecDepth 20000 in
/-- the environment of a callee at `SP = sp` (window `[sp - stk, sp + above)`) -/
theorem bodyEnv (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {S : State}
    (hsp : S.sp = BitVec.ofNat 64 sp) (h28 : S.regs 28 = BitVec.ofNat 64 g) (hm : S.mem = M) {stk above : Nat}
    (hstk : stk ≤ K) (habove : above ≤ 88) :
    CallEnv R L1 S stk above ∧ RunIface.Serves R ∧ RunIface.Globals R S.mem (win S stk above) ∧
      StkIn R L1 S stk above st ∧ StkX R L1 S stk above st ∧
      R.inv b1 L1 (S.regs 28).toNat (view R.rt L1 S.mem) ∧ S.sp.toNat = sp ∧ (S.regs 28).toNat = g := by
  have hce := hB.wc.cenv hP
  have hsN : S.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; have := hce.2.2.1; omega
  have hgN : (S.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; have := hce.2.2.2.2.1; omega
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hlp : 0 < lvlL (stLen s.mem st) lm := by have := hP.2.2.2.2.2.1; simp only [lvlL, lvlZ, lvlR, W]; omega
  have hwo := WC.win_out hP hB.wc hlp
  have hsi := hB.wc.stkIn hP hsN hgN hm hstk habove
  have hgl := hB.wc.globals hP (w := win S stk above) (fun a n ho => by
    simp only [win, hsN, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have hout := hP.win_rt
  have hsok := hB.wc.sok
  have hcl := hsok.2.2.2.2.2.1
  have hcap : 0 < stCap M st := by have := hB.wc.len; omega
  obtain ⟨he, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgO, hsok0, hstw, hstg, harr, -, hwbA,
    hstf, hstnz, -, -, -⟩ := hP
  obtain ⟨-, -, -, -, -, hgo, -, -, -, -, -, -, -, -, hsv⟩ := he
  simp only [outside_cons] at hgo
  subst hm
  refine ⟨CallW.callEnv_of hce hsp h28 rfl hstk (by omega), hsv, hgl, hsi, ⟨hstnz, hwbA, ?_, ?_, ?_,
    free_apart hB.wc hsok0.2.1 hstf, hgO.2.2.1.symm, (free_apart hB.wc hgO.1 hgO.2.2.2).symm⟩,
    by rw [hgN]; exact hB.wc.inv, hsN, hgN⟩
  · -- the free part is held (a part of the stack's array)
    exact ((hsok.2.2.2.2.1 hcap).2.1).sub (by simp only [frP]; omega) (by simp only [frP, frN]; omega)
  · have := hwo (sp - stk) (stk + above) (by omega) (by omega)
    rw [outside_append] at this
    simp only [stkWs, win, hsN, frP, frN, outside_cons, outside_nil, and_true] at this ⊢
    omega
  · rw [hgN]
    rcases hB.wc.kf with ⟨e1, e2⟩ | ⟨hin, -⟩
    · have h0 : 0 < stCap s.mem st := by rw [← e2]; exact hcap
      · have := (harr h0).2
        simp only [frP, frN, e1, e2]; unfold Apart at this ⊢
        have := hB.wc.len; have := hB.wc.lo; omega
    · have := hin.apart hgo.2
      simp only [frP, frN]; unfold Apart at this ⊢; omega

set_option maxRecDepth 20000 in
/-- the facts of a buffer of either class (positive cap) -/
theorem BC.facts (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {u : Bool} {q c : Nat}
    (h : BC R L K g sp st zp zc M L1 zzp bp lm u q c) (hc : 0 < c) :
    c < 2 ^ 40 ∧ NatLive M R L1 q c ∧ Apart q (8 * c) (sp - K) (K + 560) ∧ Apart q (8 * c) (g + 16) 8 ∧
      Apart q (8 * c) st 24 ∧ Apart q (8 * c) (free M st).1 (free M st).2 ∧ Apart q (8 * c) RunIface.gA 32 := by
  cases u
  · obtain ⟨rfl, rfl⟩ := h
    have hz := hB.tz.zscr
    have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.2.1; simp only [W]; omega
    have hgA : OE R L sp K st s.mem RunIface.gA 32 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hgrt := (hB.wc.cenv hP).2.2.2.2.2.2.2.2.2.1
    have harr := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨by omega, fun _ => ⟨hz.al, hz.held, hz.acc, hz.b48⟩, scr_win hP hz, ?_, scr_hdr hP hz, ?_,
      (held_scr_apart hgA.1 hgA.2.2.2 hz).symm⟩
    · rcases hz.loc with ⟨hc0, l1, l2⟩ | ⟨hin, -⟩
      · have := (harr hc0).2; unfold Apart at this ⊢; omega
      · exact (hin.apart hgrt).symm
    · show Apart _ _ (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
      rcases hB.tz.zbu with ⟨c1, c2⟩ | hap
      · unfold Apart; omega
      · unfold Apart at hap ⊢; have := hB.wc.sok.2.2.2.2.2.1; omega
  · obtain ⟨a1, a2, a3, a4, a5, -, -⟩ := h.ap hc
    exact ⟨h.c40, h.live, a1, a4, a2, a5, a3⟩

set_option maxRecDepth 20000 in
/-- a buffer of either class as a callee's output (`WrOut`) and input (`RdIn`, `CapIn`) array at `SP = sp` -/
theorem BC.arg (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {u : Bool} {q c : Nat}
    (h : BC R L K g sp st zp zc M L1 zzp bp lm u q c) (hc : 0 < c) {S : State} (hsN : S.sp.toNat = sp)
    (hgN : (S.regs 28).toNat = g) (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 88) :
    WrOut R L1 S stk above q c ∧ (∀ l, l ≤ c → RdIn R L1 S stk above q l ∧ CapIn R L1 q l c ∧
      StkApart M st q (8 * l) ∧ OpX M st q (8 * l)) := by
  obtain ⟨c40, hl, aW, aG, aS, aF, aA⟩ := BC.facts hP hB h hc
  obtain ⟨al, hh, acc, b48⟩ := hl hc
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  unfold Apart at aW aG aS aA
  simp only [Apart] at aF
  subst hm
  refine ⟨⟨c40, hl, fun _ => ⟨?_, by rw [hgN]; unfold Apart; omega⟩⟩, fun l hl => ⟨⟨by omega,
    Memory.accessible_weaken _ (Memory.accessible_mono _ acc (Nat.le_refl _) (by omega)), by omega,
    hh.sub (Nat.le_refl _) (by omega), ?_⟩, ⟨hl, c40, hh, b48⟩, fun _ => ⟨by unfold Apart; omega, fun _ => ?_⟩,
    fun _ => ⟨?_, by unfold Apart; omega⟩⟩⟩
  · simp only [win, hsN, outside_cons, outside_nil, and_true]; omega
  · simp only [win, hsN, outside_cons, outside_nil, and_true]; omega
  · unfold Apart; omega
  · simp only [frP, frN]; unfold Apart; omega

/-- a table entry `powers[j]` (`(bp + 8 j w, yl, w)`, `yl ≤ w`) as a callee's input array -/
theorem tbl_arg (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {j l : Nat} (hj : j < 4)
    (hl : l ≤ W lm) {S : State} (hsN : S.sp.toNat = sp) (hm : S.mem = M) {stk above : Nat}
    (hstk : stk ≤ K) (habove : above ≤ 88) :
    RdIn R L1 S stk above (bp + 8 * (j * W lm)) l ∧ CapIn R L1 (bp + 8 * (j * W lm)) l (W lm) ∧
      StkApart M st (bp + 8 * (j * W lm)) (8 * l) ∧ OpX M st (bp + 8 * (j * W lm)) (8 * l) := by
  have hbs := hB.tz.bscr
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.2.1; simp only [W]; omega
  have hjW : (j + 1) * W lm ≤ P2Pre.NB 4 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : j * W lm + W lm ≤ P2Pre.NB 4 lm := by rw [← Nat.succ_mul]; exact hjW
  have bW := scr_win hP hbs
  have bS := scr_hdr hP hbs
  have hgA : OE R L sp K st s.mem RunIface.gA 32 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have bA := held_scr_apart hgA.1 hgA.2.2.2 hbs
  unfold Apart at bW bS bA
  have hcl := hB.wc.sok.2.2.2.2.2.1
  subst hm
  refine ⟨⟨by omega, Memory.accessible_weaken _ (Memory.accessible_mono _ hbs.acc (by omega) (by omega)),
    by have := hbs.b48; omega, hbs.held.sub (by omega) (by omega), ?_⟩,
    ⟨hl, by omega, hbs.held.sub (by omega) (by omega), by have := hbs.b48; omega⟩,
    fun _ => ⟨by unfold Apart; omega, fun _ => ?_⟩, fun _ => ⟨?_, by unfold Apart; omega⟩⟩
  · simp only [win, hsN, outside_cons, outside_nil, and_true]; omega
  · rcases hB.tz.bbu with ⟨c1, c2⟩ | hap
    · unfold Apart; omega
    · unfold Apart at hap ⊢; omega
  · simp only [frP, frN]
    rcases hB.tz.bbu with ⟨c1, c2⟩ | hap
    · unfold Apart; omega
    · unfold Apart at hap ⊢; omega

/-- the two buffer classes are apart (positive caps) -/
theorem bc_apart (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {u : Bool} {p c q d : Nat}
    (h1 : BC R L K g sp st zp zc M L1 zzp bp lm u p c) (h2 : BC R L K g sp st zp zc M L1 zzp bp lm (!u) q d)
    (hc : 0 < c) (hd : 0 < d) : Apart p (8 * c) q (8 * d) := by
  cases u
  · obtain ⟨rfl, rfl⟩ := h1; exact (h2.ap hd).2.2.2.2.2.1.symm
  · obtain ⟨rfl, rfl⟩ := h2; exact (h1.ap hc).2.2.2.2.2.1

set_option maxRecDepth 20000 in
/-- a fresh callee result `(p, c)` (apart from `L1`, from a re-allocated stack array) is a U-class buffer -/
theorem ub_res (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {M' : Memory} {L2 : List (Nat × Nat)}
    {p c : Nat} (hc : 0 < c) (hc40 : c < 2 ^ 40) (hin : InRanges p (8 * c) R.rt) (hap : ApartAll p (8 * c) L1)
    (hlv : NatLive M' R L2 p c) (hx : LiveExt R L1 L2) (hb : StackBack R L1 L2 st M M')
    (hnew : 0 < stCap M' st → Apart p (8 * c) (stW M' st) (8 * stCap M' st)) :
    UB R L K g sp st zp zc M' L2 zzp bp lm p c := by
  have hgrt := (hB.wc.cenv hP).2.2.2.2.2.2.2.2.2.1
  have hgA : OE R L sp K st s.mem RunIface.gA 32 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcl := hb.1.2.2.2.2.2.1
  refine ⟨hc40, hlv, Or.inr ⟨hc, hin, fun r hr => hap r (hB.wc.le.mem_old hr)⟩, fun _ => ⟨(hin.apart hP.win_rt).symm,
    fresh_held_apart hin hap hB.wc.sok.2.1, fresh_held_apart hin hap (hB.wc.le.held hgA.1), (hin.apart hgrt).symm,
    ?_, fresh_held_apart hin hap hB.tz.zscr.held, fresh_held_apart hin hap hB.tz.bscr.held⟩,
    fun _ hcm => Or.inr (hnew hcm)⟩
  show Apart p (8 * c) (stW M' st + 8 * stLen M' st) (8 * (stCap M' st - stLen M' st))
  rcases Nat.eq_zero_or_pos (stCap M' st) with h0 | h0
  · have := hb.2.1; have := hB.wc.len
    have : 0 < lvlL (stLen s.mem st) lm := by have := hP.2.2.2.2.2.1; simp only [lvlL, lvlZ, lvlR, W]; omega
    omega
  · have := hnew h0; unfold Apart at this ⊢; omega

end

end FvModexp.Arm64.P2W2
