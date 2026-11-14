import FvModexp.Proofs.Amd64.Exp.NDefs
import FvModexp.Proofs.Amd64.Exp.NHyp
import FvModexp.Proofs.Amd64.Exp.OddDefs
import FvModexp.Proofs.Common.StkFrame

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): a stack-taking callee's entry facts (`NHyp.CPre`) at its call (agent expmc s70; twin of
`Arm64.ExpN.cpre_at`)

`cpre_at`: at a callee entry `S` (`RSP = sp + 0x388` = `t - 0x110`, window `[sp + 0x388 - stk, sp + 0x388 + 112)`,
`stk ≤ K + 0x388`) whose memory is the entry memory changed only in the runtime ranges and expNN's window minus the
saved `BP` / return address (`R.rt ++ wN sp K`), live objects untouched, live set `L1 ⊇ L`, from `NPre` at the entry:
`NHyp.CPre` for the inputs among `x`, `y`, `m` and the `z` argument `(zq, zcq)` (`ZQ`: empty, or apart from the window,
the guard and TLS words, the stack and the operands).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- expNN's window without the return address `[sp + 0x498, sp + 0x4a0)` (the saved `BP` slot `[sp + 0x490, sp + 0x498)`
is written by the prologue's `PUSHQ BP`, so it is inside) -/
@[reducible] def wN (sp K : Nat) : List (Nat × Nat) := [(sp - K, sp + 0x498), (sp + 0x4a0, sp + 0x510)]

/-- the callee's `z` argument at the call (memory `M`, live set `L1`) -/
@[reducible] def ZQ (R : RtInv) (L1 : List (Nat × Nat)) (g fs sp K st xp xl yp yl mp n : Nat) (M : Memory)
    (zq zcq : Nat) : Prop :=
  zcq < 2 ^ 40 ∧ NatLive M R L1 zq zcq ∧
  (0 < zcq → Apart zq (8 * zcq) (sp - K) (K + 0x510) ∧ Apart zq (8 * zcq) (g + 16) 8 ∧
    Apart zq (8 * zcq) (fs - 8) 8 ∧ Apart zq (8 * zcq) st 24 ∧
    Apart zq (8 * zcq) (W4En.free M st).1 (W4En.free M st).2 ∧ Apart zq (8 * zcq) RunIface.gA 32 ∧
    Apart zq (8 * zcq) xp (8 * xl) ∧ Apart zq (8 * zcq) yp (8 * yl) ∧ Apart zq (8 * zcq) mp (8 * n))

/-- a held range keeps its bytes through a frame of the runtime ranges and `ws` -/
theorem rd_mk {R : RtInv} {L ws : List (Nat × Nat)} {a n : Nat} {M m : Memory}
    (hH : InRanges a n L ∨ Outside a n R.rt) (hLF : LiveFrame M m L []) (hMF : MemFrame M m (R.rt ++ ws))
    (hws : Outside a n ws) : m.readLE a n = M.readLE a n := by
  rcases hH with h | h
  · exact hLF.readLE a n h trivial
  · exact hMF.readLE a n (by rw [outside_append]; exact ⟨h, hws⟩)

/-- a held range apart from the window keeps its bytes -/
theorem rd_held {R : RtInv} {L : List (Nat × Nat)} {sp K a k : Nat} {M m : Memory}
    (hH : InRanges a k L ∨ Outside a k R.rt) (hLF : LiveFrame M m L []) (hMF : MemFrame M m (R.rt ++ wN sp K))
    (hw : Apart a k (sp - K) (K + 0x510)) : m.readLE a k = M.readLE a k :=
  rd_mk hH hLF hMF (by unfold Apart at hw; simp only [wN, outside_cons, outside_nil, and_true]; omega)

theorem held_sub {R : RtInv} {L : List (Nat × Nat)} {a k b n : Nat} (h : InRanges a k L ∨ Outside a k R.rt)
    (h1 : a ≤ b) (h2 : b + n ≤ a + k) : InRanges b n L ∨ Outside b n R.rt :=
  h.elim (fun h => Or.inl (h.sub h1 h2)) (fun h => Or.inr (h.of_sub h1 h2))

/-- `CEnv` with an extended live set -/
theorem cenv_ext {R : RtInv} {L L1 : List (Nat × Nat)} {g fs sp K A : Nat} {M : Memory}
    (h : CallW.CEnv R L g fs sp K A M) (hx : LiveExt R L L1) : CallW.CEnv R L1 g fs sp K A M := by
  obtain ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := h
  refine ⟨hal, hK0, hA0, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hx.liveSep hLs fun r hr => ?_, hd, hro, f1, f2, f3, f4,
    f5, f6⟩
  simp only [List.mem_singleton] at hr; subst hr; simp only
  rwa [show sp + A - (sp - K) = K + A by omega]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- an operand's input facts at the callee entry -/
theorem opnd_at {R : RtInv} {L L1 : List (Nat × Nat)} {sp K st stk p k c zq zcq : Nat} {s S : State}
    (hO : NE R L sp K st s.mem p (8 * c)) (hkc : k ≤ c) (hacc : s.mem.accessible p (8 * k) false = true)
    (h48 : p + 8 * k ≤ 2 ^ 48) (hN : NatNorm s.mem p k) (hk : k ≤ 2 ^ 9)
    (hF : MemFrame s.mem S.mem (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem S.mem L []) (hx : LiveExt R L L1)
    (hSsp : (S.regs 4).toNat = sp + 0x388) (hstk : stk ≤ K + 0x388) (hK : K ≤ sp)
    (ew : stW S.mem st = stW s.mem st) (el : stLen S.mem st = stLen s.mem st) (ec : stCap S.mem st = stCap s.mem st)
    (hz : 0 < zcq → Apart zq (8 * zcq) p (8 * k)) :
    EvenHyp.RdIn R L1 S stk 112 p k ∧ k ≤ 2 ^ 9 ∧ NatNorm S.mem p k ∧ Apart p (8 * k) st 24 ∧
      Apart p (8 * k) (NHyp.freeOf S.mem st).1 (NHyp.freeOf S.mem st).2 ∧
      (0 < zcq → Apart zq (8 * zcq) p (8 * k)) := by
  obtain ⟨hH0, hw0, hst0, hfr0⟩ := hO
  have hH : InRanges p (8 * k) L ∨ Outside p (8 * k) R.rt := held_sub hH0 (Nat.le_refl _) (by omega)
  have hw : Apart p (8 * k) (sp - K) (K + 0x510) := by unfold Apart at hw0 ⊢; omega
  have hst : Apart p (8 * k) st 24 := by unfold Apart at hst0 ⊢; omega
  have hfr : Apart p (8 * k) (W4En.free s.mem st).1 (W4En.free s.mem st).2 := by unfold Apart at hfr0 ⊢; omega
  refine ⟨⟨by omega, by rw [hF.accessible]; exact hacc, h48, hx.held hH, ?_⟩, hk, ?_, hst, ?_, hz⟩
  · simp only [win, hSsp, outside_cons, outside_nil, and_true]; unfold Apart at hw; omega
  · rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact Or.inl hk0
    rcases hN with h0 | h1
    · exact Or.inl h0
    · right
      rw [rd_held (held_sub hH (by omega) (by omega)) hLF hF (by unfold Apart at hw ⊢; omega)]; exact h1
  · show Apart p (8 * k) (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact hfr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `NHyp.CPre` at a callee entry -/
theorem cpre_at {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat}
    {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat}
    {costS costP : Nat → Nat → Nat → Nat → Nat}
    {g fs sp zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat} {s S : State}
    (hP : NPre R b L K costF costD needR costR needS needP costS costP g fs sp zp zl zc st xp xl xc yp yl yc mp n mc
      slow s)
    (hF : MemFrame s.mem S.mem (R.rt ++ wN sp K)) (hLF : LiveFrame s.mem S.mem L [])
    (hrg : S.mem.regions = s.mem.regions)
    {L1 : List (Nat × Nat)} {b1 : Nat} (hx : LiveExt R L L1) (hinv : R.inv b1 L1 g (view R.rt L1 S.mem))
    (hSsp : S.regs 4 = BitVec.ofNat 64 (sp + 0x388)) (h14 : S.regs 14 = BitVec.ofNat 64 g)
    (hfs : S.fsBase.toNat = fs) {stk : Nat} (hstk : stk ≤ K + 0x388)
    {zq zl' zcq : Nat} (hzq : ZQ R L1 g fs sp K st xp xl yp yl mp n S.mem zq zcq) (hzl : zl' ≤ zcq)
    {ins : List (Nat × Nat)} (hins : ∀ p k, (p, k) ∈ ins → (p = xp ∧ k = xl) ∨ (p = yp ∧ k = yl) ∨ (p = mp ∧ k = n))
    {need cst : Nat} (hneed : stLen s.mem st + need ≤ 2 ^ 16) (hcst : cst ≤ b1) :
    NHyp.CPre R b1 L1 stk 112 zq zl' zcq st ins need cst S := by
  obtain ⟨⟨-, -, -, -, -, hK1, -, hce, hsv⟩, hgl, hty, -, hadx, -, -, -, -, -, -, -, -, hn128, -, -,
    hmO, hma, hm48, hmN, hyO, hya, hy48, hyN, hyl, -, hxO, hxa, hx48, hxN, hxl, hxlc, -, -, -, -, -,
    hgO, -, -, -, hsok, hstw, hstg, hstf, harr, hc0, hwbf, hwbA, hstfr, hfrg, hfrf, -⟩ := hP
  have hce0 := hce
  obtain ⟨-, hK0, hA0, hacc, -, -, -, -, hga, hgrt, -, -, hro, -, -, -, -, f5, f6⟩ := hce0
  have hSs : (S.regs 4).toNat = sp + 0x388 := by rw [hSsp, BitVec.toNat_ofNat]; omega
  have hSg : (S.regs 14).toNat = g := by
    rw [h14, BitVec.toNat_ofNat]; unfold Apart at hga; omega
  -- the call environment
  have hws : ∀ r ∈ wN sp K, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr _
    simp only [wN, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have ce1 := CallW.CEnv.frame hce hF hrg hws
    (by unfold Apart at hga; simp only [wN, outside_cons, outside_nil, and_true]; omega)
    (by unfold Apart at f6; simp only [wN, outside_cons, outside_nil, and_true]; omega)
  have ce2 := cenv_ext (ExpOdd.cenv_rebase ce1 (x' := sp + 0x388) (K' := K + 0x388) (A' := 0x188) (by omega)
    (by omega) (by omega) (by obtain ⟨hal, -⟩ := hce; omega)) hx
  have hcall := CallW.callEnv_of ce2 hSs hSg hfs rfl hstk (by omega : 112 ≤ 0x188) (by omega)
  -- the stack header
  have hH := hsok.2.1
  have rdh : ∀ o, o + 8 ≤ 24 → S.mem.readLE (st + o) 8 = s.mem.readLE (st + o) 8 := fun o ho =>
    rd_held (held_sub hH (by omega) (by omega)) hLF hF (by unfold Apart at hstw ⊢; omega)
  have ew : stW S.mem st = stW s.mem st := by have := rdh 0 (by omega); simpa using this
  have el : stLen S.mem st = stLen s.mem st := rdh 8 (by omega)
  have ec : stCap S.mem st = stCap s.mem st := rdh 16 (by omega)
  obtain ⟨hzq40, hzqL, hzqA⟩ := hzq
  have hwin : ∀ {a k : Nat}, Apart a k (sp - K) (K + 0x510) → Outside a k (win S stk 112) := fun h => by
    unfold Apart at h; simp only [win, hSs, outside_cons, outside_nil, and_true]; omega
  -- the globals
  have hgl' : RunIface.Globals R S.mem (win S stk 112) := by
    obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt', hgw', hwbacc, hwbrt, hwbw⟩ := hgl
    have hgA : Outside RunIface.gA 32 (R.rt ++ wN sp K) := by
      simp only [wN, outside_append, outside_cons, outside_nil, and_true] at hgw' ⊢
      exact ⟨hgrt', by omega, by omega⟩
    have hrd : ∀ k, k + 8 ≤ 32 → S.mem.readLE (RunIface.gA + k) 8 = s.mem.readLE (RunIface.gA + k) 8 :=
      fun k hk => hF.readLE _ _ (hgA.of_sub (by omega) (by omega))
    refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt', ?_,
      by rw [hF.accessible]; exact hwbacc, hwbrt, ?_⟩
    · rw [e8, hrd 8 (by omega), ← e8]; exact h40
    · rw [e16, hrd 16 (by omega), ← e16]; exact h12
    · rw [e24, hrd 24 (by omega), ← e24]; exact h80
    · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
      show S.mem.readLE RunIface.gA 8 = 40; rw [this]; exact h40'
    · simp only [win, hSs, outside_cons, outside_nil, and_true] at hgw' ⊢; omega
    · simp only [win, hSs, outside_cons, outside_nil, and_true] at hwbw ⊢; omega
  have hgOa := hgO.2.2.1
  refine ⟨hcall, hsv, hgl', hro, hty, hzl, ⟨hzq40, hzqL, fun hc => ?_⟩, fun p k hpk => ?_,
    stkOK_hdr hsok hF ew el ec hx, hwin hstw, by rw [hSg]; exact hstg, ?_, by rw [ec, ew]; exact hc0,
    by rw [el]; exact hneed, by rw [hF.accessible]; exact hwbf, hwbA, ?_, ?_, fun hc => ?_,
    by unfold Apart at hgOa ⊢; omega, ?_, hcst, by rw [hF.accessible]; exact hadx, ?_, by rw [hSg]; exact hinv⟩
  · obtain ⟨a1, a2, a3, -⟩ := hzqA hc
    exact ⟨hwin a1, by rw [hSg]; exact a2, by rw [hfs]; exact a3⟩
  · rcases hins p k hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact opnd_at hxO hxlc (Janus.Arm64.Memory.accessible_mono _ hxa (by omega) (by omega)) (by omega) hxN
        (by omega) hF hLF hx hSs hstk hK0 ew el ec fun hc => (hzqA hc).2.2.2.2.2.2.1
    · exact opnd_at hyO (Nat.le_refl _) hya hy48 hyN hyl hF hLF hx hSs hstk hK0 ew el ec
        fun hc => (hzqA hc).2.2.2.2.2.2.2.1
    · exact opnd_at hmO (Nat.le_refl _) hma hm48 hmN (by omega) hF hLF hx hSs hstk hK0 ew el ec
        fun hc => (hzqA hc).2.2.2.2.2.2.2.2
  · rw [ec, ew, hSg]; intro hc
    obtain ⟨a1, a2, -⟩ := harr hc
    exact ⟨hwin a1, a2⟩
  · show Apart st 24 (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st))
    rw [ew, el, ec]; exact hstfr
  · refine ⟨by rw [hfs]; exact hstf, ?_⟩
    show Apart (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st)) (S.fsBase.toNat - 8) 8
    rw [ew, el, ec, hfs]; exact hfrf
  · obtain ⟨-, -, -, a4, a5, a6, -⟩ := hzqA hc
    exact ⟨a4, a5, a6⟩
  · show Apart (stW S.mem st + 8 * stLen S.mem st) (8 * (stCap S.mem st - stLen S.mem st)) RunIface.gA 32
    rw [ew, el, ec]; exact hfrg
  · rw [ec, ew, hfs]; intro hc
    exact (harr hc).2.2

end FvModexp.Amd64.ExpN
