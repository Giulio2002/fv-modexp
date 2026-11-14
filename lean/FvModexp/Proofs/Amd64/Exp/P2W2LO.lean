import FvModexp.Proofs.Amd64.Exp.P2W2BJ
import FvModexp.Proofs.Amd64.Exp.P2W2Cp5

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the loop's outer step (agent divmc s73; amd64 twin of agent infra's
`Arm64.P2W2LO`)

`outerStep`: at `LT` with `c = 0` windows left in the current word and `i + 1` words left: the test's stores
`0x118 := z.ptr`, `0x68 := z.len`, `TESTQ R10` / `JGE` (not taken: `c - 1 < 0`), `TESTQ R11` / `JE` (not taken),
`R10 := i` (fn+0x7ee), the bounds check `len y > i` (`JA` fn+0x627), `yi = y[i]`, `R11 := i`, `R10 := 31`,
`0xc8 := i`, back to `LT` with `c = 32` (nat.go:1249-1253).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `LI` through the outer step's stores `0x118`, `0x68`, `0xc8` -/
theorem LI.out (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 zzp tp kk i : Nat} {u : Bool} {pA lA cA pB lB cB Z : Nat}
    (h : LI R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp kk i u pA lA cA pB lB cB Z)
    {M' : Memory} (hF : MemFrame M M' [(sp + 280, sp + 288), (sp + 104, sp + 112), (sp + 200, sp + 208)])
    (hrg : M'.regions = M.regions) {i' : Nat} (r0c8 : M'.readLE (sp + 0xc8) 8 = i') :
    LI R L K g sp st bp r zp zc xp xl xc yp yl lm s M' L1 b1 zzp tp kk i' u pA lA cA pB lB cB Z := by
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hstw : Apart st 24 (sp - 8 - K) (K + 0x238) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hrd : ∀ a k, (a + k ≤ sp + 104 ∨ (sp + 112 ≤ a ∧ a + k ≤ sp + 200) ∨ (sp + 208 ≤ a ∧ a + k ≤ sp + 280) ∨
      sp + 288 ≤ a) → M'.readLE a k = M.readLE a k := fun a k ha =>
    hF.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w := hF.accessible
  have e0 : stW M' st = stW M st := hrd _ _ (by omega)
  have e1 : stLen M' st = stLen M st := hrd _ _ (by omega)
  have e2 : stCap M' st = stCap M st := hrd _ _ (by omega)
  have hbW := scr_win hP h.tz.bscr
  unfold Apart at hbW
  have hBF : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp := ⟨h.wc, h.esl, h.tz⟩
  have hlA := len_pos h.va h.zo
  have hAW := (BC.facts hP hBF h.ca (by have := h.lac; omega)).2.2.1
  unfold Apart at hAW
  obtain ⟨v1, v2⟩ := nv_keep (M := M) (M' := M') (p := pA) (l := lA) fun a k h1 h2 => hrd a k (by
    have := h.lac; omega)
  have hBC : ∀ (w : Bool) (q d : Nat), BC R L K g sp st zp zc M L1 zzp tp lm w q d →
      BC R L K g sp st zp zc M' L1 zzp tp lm w q d := fun w q d hq => by
    cases w
    · exact hq
    · exact UB.keep hq hacc (LiveExt.refl R L1) e0 e1 e2
  exact ⟨WC.win hP h.wc hF hrg (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp only [InWN] <;> omega),
    ESl.keep h.esl (fun a k ha => hrd a k (by omega)), by rw [hrd _ _ (by omega)]; exact h.sc0, r0c8,
    h.tz.keep hacc (LiveExt.refl R L1) e0 e1 e2 (fun a k ha => hrd a k (by omega)), h.la, h.lac, h.lbc,
    v1.trans h.va, v2 h.na, hBC _ _ _ h.ca, hBC _ _ _ h.cb, h.zo, h.cb0⟩

end

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the outer step** (premise `hout` of `loopKL`) -/
theorem outerStep (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (i : Nat)
    (KN : KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i 32) :
    KI impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV (i + 1) 0 := by
  intro S M L1 b1 yi Z pA lA cA pB lB cB u h
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hce := h.li.wc.cenv hP
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hsp48 : sp - 8 + 0x238 ≤ 2 ^ 48 := hce.2.2.1
  have hwacc : M.accessible (sp - 8 - K) (K + 0x238) true = true := hce.2.2.2.1
  have hwaccF : M.accessible (sp - 8 - K) (K + 0x238) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have hyl : yl ≤ 2 ^ 12 := hP.2.2.2.2.2.2.2.2.2.2.2.1
  have hi := h.hi
  have hyw := y_words hP h.li.wc i (by omega)
  have hya : M.accessible yp (8 * yl) false = true := by
    rw [h.li.wc.fr.accessible]; exact hP.2.2.2.2.2.2.2.1
  have hy48 : yp + 8 * yl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.1
  have ya1 : M.accessible (yp + 8 * i) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hya (by omega) (by omega)
  have hyw' : M.readLE (yp + (i + 1) * 8 - 8) 8 = Exp.wd (natVal s.mem yp yl) i := by
    rw [show yp + (i + 1) * 8 - 8 = yp + 8 * i by omega]; exact hyw
  have hLH : HdM (LI R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp kk (i + 1) u pA lA cA pB lB cB Z) :=
    ⟨h.li⟩
  have hb := h.hb
  have hfv := h.hfv
  have hu := h.hu
  have hcA : 0 < cA := by have := len_pos h.li.va h.li.zo; have := h.li.lac; omega
  have hAf := BC.facts hP (⟨h.li.wc, h.li.esl, h.li.tz⟩ : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp
    tp) h.li.ca hcA
  have hcA40 : cA < 2 ^ 40 := hAf.1
  have hpA : pA + 8 * cA ≤ 2 ^ 48 := (hAf.2.1 hcA).2.2.2
  have hlac : lA ≤ cA := h.li.lac
  clear hAf
  have e10 : S.regs 10 = 18446744073709551615#64 := by rw [h.e10]; decide
  have hm1 : (18446744073709551615#64).msb = true := by decide
  have hm1' : (18446744073709551615#64).getLsbD 63 = true := by decide
  obtain ⟨epc, esp, e14, e5, efs, ex, edf, em, e9, e6, e12, e8, e1, e15, e3, -, e13, e7, e11, e2, e0, -, -, -, -, -,
    -, -⟩ := h
  have hyA : Apart yp (8 * yl) (sp - 8 - K) (K + 0x238) := hP.2.2.2.2.2.2.1.2.1
  unfold Apart at hyA
  have hPH : HdM (EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) := ⟨hP⟩
  clear hP hce hyw
  subst em
  janus64_run [hm1, hm1', sub1c i, hyw', ya1, hwacc, hwaccF] until [LT]
  refine KN _ _ L1 b1 (Exp.wd (natVal s.mem yp yl) i) Z pA lA cA pB lB cB u
    ⟨?_, ?_, ?_, ?_, ?efs, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      LI.out hPH.h hLH.h ?F ?rg ?r0c8, by omega,
      by have := Exp.wd_lt (natVal s.mem yp yl) i; simp only [Exp.B] at this; exact this, by omega,
      by rw [hu]; omega, ?bud, ?fv⟩
  case F => janus_frame
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case r0c8 => rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
  case bud => rw [show 32 + 32 * i = 0 + 32 * (i + 1) by omega]; exact hb
  case fv => rw [← hfv]; rfl
  case efs => exact efs
  all_goals (janus64_simp; done)

end

end FvModexp.Amd64.P2W2
