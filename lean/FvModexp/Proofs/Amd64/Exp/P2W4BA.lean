import FvModexp.Proofs.Amd64.Exp.P2W4BC

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the loop body's callee-argument facts (agent divmc s77, port of divmc s72; amd64 twin of agent
infra's `Arm64.P2W4BA`)

At a callee entry from the body (`RSP = sp - 0x8`, window `[sp - 0x8 - stk, sp - 0x8 + above)`, `stk ≤ K`, `above ≤ 88`):
* `bodyEnv`: `CallEnv`, `Serves`, `Globals`, `Q.NatSqr.StkPre`, the invariant, the register values.
* `BC.facts`: a buffer of either class (positive cap) is live, apart from the window, the guard word, the stack header,
  its free part, the threshold globals and the TLS word.
* `BC.arg`: such a buffer as an output (`WrOut`, `StkSep`) and an input array of any length `l ≤ cap`
  (`RdIn`, `StkSep`, held cap range) — the shapes of `Q.NatSqr.SPre`, `Q.NatMul.Ops` and `EvenHyp.TruncPre`.
* `tbl_arg`: a table entry `powers[j]` as an input array; `bc_apart`, `ub_res` as on arm64.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

open FvModexp.Amd64.EvenHyp (RdIn WrOut)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep)

theorem lL_bd (ℓ0 lm : Nat) : lvlL ℓ0 lm ≤ ℓ0 + 40 * W lm + 6 := by
  simp only [lvlL, lvlZ, lvlR, StackNat.rnd, P2Pre.NB, P2Pre.W, W]; omega

theorem ofNat_inj' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) :
    a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 zzp tp : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- the environment of a callee entered at `RSP = sp - 0x8` (window `[sp - 0x8 - stk, sp - 0x8 + above)`) -/
theorem bodyEnv (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) {S : State}
    (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 0x8)) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = s.fsBase)
    (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K) (habove : above ≤ 88) :
    CallEnv R L1 S stk above ∧ RunIface.Serves R ∧ RunIface.Globals R S.mem (win S stk above) ∧
      StkPre R L1 S stk above st ∧
      R.inv (b1 + stkR (HW (stLen s.mem st) lm) S.mem st) L1 (S.regs 14).toNat (view R.rt L1 S.mem) ∧
      (S.regs 4).toNat = sp - 0x8 ∧ (S.regs 14).toNat = g ∧ S.fsBase.toNat = fs := by
  have hce := hB.wc.cenv hP
  have hsN : (S.regs 4).toNat = sp - 0x8 := by rw [hsp, BitVec.toNat_ofNat]; have := hce.2.2.1; omega
  have hgN : (S.regs 14).toNat = g := by rw [h14, BitVec.toNat_ofNat]; have := hce.2.2.2.2.1; omega
  have hfsN : S.fsBase.toNat = fs := by rw [hfs]; exact hP.1.2.2.1
  have hK0 : K ≤ sp - 0x8 := hce.2.1
  have hlp : 0 < lvlL (stLen s.mem st) lm := by have := hP.2.2.2.2.1; simp only [lvlL, lvlZ, lvlR, W]; omega
  refine ⟨CallW.callEnv_of hce hsN hgN hfsN hm hstk (by omega) (by omega), hP.1.2.2.2.2.2.2.2.2.2,
    hm ▸ hB.wc.globals hP (w := win S stk above) (fun a n ho => by
      simp only [win, hsN, outside_cons, outside_nil, and_true] at ho ⊢; omega),
    hB.wc.stkPre hP hlp hstk (by omega) hsN hgN hfsN hm, by rw [hgN, hm]; exact hB.wc.inv, hsN, hgN, hfsN⟩

set_option maxRecDepth 20000 in
/-- the facts of a buffer of either class (positive cap) -/
theorem BC.facts (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) {u : Bool} {q c : Nat}
    (h : BC R L K g sp st zp zc M L1 zzp tp lm u q c) (hc : 0 < c) :
    c < 2 ^ 40 ∧ NatLive M R L1 q c ∧ Apart q (8 * c) (sp - 0x8 - K) (K + 0x360) ∧ Apart q (8 * c) (g + 16) 8 ∧
      Apart q (8 * c) st 24 ∧ Apart q (8 * c) (free M st).1 (free M st).2 ∧ Apart q (8 * c) RunIface.gA 32 ∧
      Apart q (8 * c) (fs - 8) 8 := by
  have hce := hB.wc.cenv hP
  obtain ⟨-, -, -, -, -, -, -, -, -, hgrt, -, -, -, -, -, -, -, hfrt, -⟩ := hce
  obtain ⟨-, -, -, -, -, hlm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hz, hgA, -, -, -, -, harr, -⟩ := id hP
  cases u
  · obtain ⟨rfl, rfl⟩ := h
    have hz := hB.tz.zscr
    have hW : W lm ≤ 128 := by simp only [W]; omega
    refine ⟨by omega, fun _ => ⟨hz.al, hz.held, hz.acc, hz.b48⟩, scr_win hP hz, ?_, scr_hdr hP hz, ?_,
      (held_scr_apart hgA.1 hgA.2.2.2 hz).symm, ?_⟩
    · rcases hz.loc with ⟨hc0, l1, l2⟩ | ⟨hin, -⟩
      · have := (harr hc0).2.1; unfold Apart at this ⊢; omega
      · exact (hin.apart hgrt).symm
    · show Apart _ _ (stW M st + 8 * stLen M st) (8 * (stCap M st - stLen M st))
      rcases hB.tz.zbu with ⟨c1, c2⟩ | hap
      · unfold Apart; omega
      · unfold Apart at hap ⊢; have := hB.wc.sok.2.2.2.2.2.1; omega
    · rcases hz.loc with ⟨hc0, l1, l2⟩ | ⟨hin, -⟩
      · have := (harr hc0).2.2; unfold Apart at this ⊢; omega
      · exact (hin.apart hfrt).symm
  · obtain ⟨a1, a2, a3, a4, a5, -, -⟩ := h.ap hc
    refine ⟨h.c40, h.live, a1, a4, a2, a5, a3, ?_⟩
    rcases h.org with ⟨rfl, rfl⟩ | ⟨-, hin, -⟩
    · exact (hz hc).2.2.2.2.2.1.symm
    · exact (hin.apart hfrt).symm

set_option maxRecDepth 20000 in
/-- a buffer of either class as a callee's output (`WrOut`, `StkSep`) and input array (`RdIn`, `StkSep`, the held cap
range) at a callee entry `RSP = sp - 0x8` -/
theorem BC.arg (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) {u : Bool} {q c : Nat}
    (h : BC R L K g sp st zp zc M L1 zzp tp lm u q c) (hc : 0 < c) {S : State} (hsN : (S.regs 4).toNat = sp - 0x8)
    (hgN : (S.regs 14).toNat = g) (hfsN : S.fsBase.toNat = fs) (hm : S.mem = M) {stk above : Nat} (hstk : stk ≤ K)
    (habove : above ≤ 88) :
    WrOut R L1 S stk above q c ∧ StkSep M st q (8 * c) ∧ Held R L1 q (8 * c) ∧ q + 8 * c ≤ 2 ^ 48 ∧
      (∀ l, l ≤ c → RdIn R L1 S stk above q l ∧ StkSep M st q (8 * l)) := by
  obtain ⟨c40, hl, aW, aG, aS, aF, aA, aT⟩ := BC.facts hP hB h hc
  obtain ⟨al, hh, acc, b48⟩ := hl hc
  have hK := hP.1.2.2.2.2.2.2.1
  unfold Apart at aW aG aS aA aT
  simp only [Apart] at aF
  subst hm
  refine ⟨⟨c40, hl, fun _ => ⟨?_, by rw [hgN]; unfold Apart; omega, by rw [hfsN]; unfold Apart; omega⟩⟩,
    ⟨by unfold Apart; omega, ?_, by unfold Apart; omega⟩, hh, b48, fun l hl => ⟨⟨by omega,
    Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ acc (Nat.le_refl _) (by omega)),
    by omega, hh.sub (Nat.le_refl _) (by omega), ?_⟩, ⟨by unfold Apart; omega, ?_, by unfold Apart; omega⟩⟩⟩
  · simp only [win, hsN, outside_cons, outside_nil, and_true]; omega
  · simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]; unfold Apart; omega
  · simp only [win, hsN, outside_cons, outside_nil, and_true]; omega
  · simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]; unfold Apart; omega

set_option maxRecDepth 20000 in
/-- a table entry `powers[j]` (`(tp + 8 j w, l, w)`, `l ≤ w`) as a callee's input array -/
theorem tbl_arg (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) {j l : Nat} (hj : j < 16)
    (hl : l ≤ W lm) {S : State} (hsN : (S.regs 4).toNat = sp - 0x8) (hm : S.mem = M) {stk above : Nat}
    (hstk : stk ≤ K) (habove : above ≤ 88) :
    RdIn R L1 S stk above (tp + 8 * (j * W lm)) l ∧ StkSep M st (tp + 8 * (j * W lm)) (8 * l) ∧
      Held R L1 (tp + 8 * (j * W lm)) (8 * W lm) ∧ tp + 8 * (j * W lm) + 8 * W lm ≤ 2 ^ 48 ∧ W lm < 2 ^ 40 := by
  have hbs := hB.tz.bscr
  have hK := hP.1.2.2.2.2.2.2.1
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.1; simp only [W]; omega
  have hjW : (j + 1) * W lm ≤ P2Pre.NB 16 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : j * W lm + W lm ≤ P2Pre.NB 16 lm := by rw [← Nat.succ_mul]; exact hjW
  have bW := scr_win hP hbs
  have bS := scr_hdr hP hbs
  have hgA : OE R L sp K st s.mem RunIface.gA 32 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have bA := held_scr_apart hgA.1 hgA.2.2.2 hbs
  unfold Apart at bW bS bA
  have hcl := hB.wc.sok.2.2.2.2.2.1
  subst hm
  refine ⟨⟨by omega, Janus.Arm64.Memory.accessible_weaken _
    (Janus.Arm64.Memory.accessible_mono _ hbs.acc (by omega) (by omega)),
    by have := hbs.b48; omega, hbs.held.sub (by omega) (by omega), ?_⟩,
    ⟨by unfold Apart; omega, ?_, by unfold Apart; omega⟩, hbs.held.sub (by omega) (by omega),
    by have := hbs.b48; omega, by omega⟩
  · simp only [win, hsN, outside_cons, outside_nil, and_true]; omega
  · simp only [Q.BasicSqr.freeP, Q.BasicSqr.freeN]
    rcases hB.tz.bbu with ⟨c1, c2⟩ | hap
    · unfold Apart; omega
    · unfold Apart at hap ⊢; omega

/-- the two buffer classes are apart (positive caps) -/
theorem bc_apart (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) {u : Bool} {p c q d : Nat}
    (h1 : BC R L K g sp st zp zc M L1 zzp tp lm u p c) (h2 : BC R L K g sp st zp zc M L1 zzp tp lm (!u) q d)
    (hc : 0 < c) (hd : 0 < d) : Apart p (8 * c) q (8 * d) := by
  cases u
  · obtain ⟨rfl, rfl⟩ := h1; exact (h2.ap hd).2.2.2.2.2.1.symm
  · obtain ⟨rfl, rfl⟩ := h2; exact (h1.ap hc).2.2.2.2.2.1

set_option maxRecDepth 20000 in
/-- a fresh callee result `(p, c)` (apart from `L1`, from a re-allocated stack array) is a U-class buffer -/
theorem ub_res (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) {M' : Memory} {L2 : List (Nat × Nat)}
    {p c : Nat} (hc : 0 < c) (hc40 : c < 2 ^ 40) (hin : InRanges p (8 * c) R.rt) (hap : ApartAll p (8 * c) L1)
    (hlv : NatLive M' R L2 p c) (hx : LiveExt R L1 L2) (hb : StackBack R L1 L2 st M M')
    (hnew : 0 < stCap M' st → Apart p (8 * c) (stW M' st) (8 * stCap M' st)) :
    UB R L K g sp st zp zc M' L2 zzp tp lm p c := by
  have hgrt := (hB.wc.cenv hP).2.2.2.2.2.2.2.2.2.1
  have hgA : OE R L sp K st s.mem RunIface.gA 32 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcl := hb.1.2.2.2.2.2.1
  refine ⟨hc40, hlv, Or.inr ⟨hc, hin, fun r hr => hap r (hB.wc.le.mem_old hr)⟩, fun _ => ⟨(hin.apart hP.win_rt).symm,
    fresh_held_apart hin hap hB.wc.sok.2.1, fresh_held_apart hin hap (hB.wc.le.held hgA.1), (hin.apart hgrt).symm,
    ?_, fresh_held_apart hin hap hB.tz.zscr.held, fresh_held_apart hin hap hB.tz.bscr.held⟩,
    fun _ hcm => Or.inr (hnew hcm)⟩
  show Apart p (8 * c) (stW M' st + 8 * stLen M' st) (8 * (stCap M' st - stLen M' st))
  rcases Nat.eq_zero_or_pos (stCap M' st) with h0 | h0
  · have := hb.2.1; have := hB.wc.len
    have : 0 < lvlL (stLen s.mem st) lm := by have := hP.2.2.2.2.1; simp only [lvlL, lvlZ, lvlR, W]; omega
    omega
  · have := hnew h0; unfold Apart at this ⊢; omega

end

end FvModexp.Amd64.P2W4
