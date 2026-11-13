import FvModexp.Proofs.Arm64.NatQ.MulLoopEnv

/-!
# [Q-form copy of Arm64/Nat/MulLoopT.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), chunk loop: the scratch `t` and the inner `t.mul(stk, x[i:i+c], y)` precondition

`TOK … Mi tp tc`: the array `(tp, ·, tc)` of `t` (first `stk.nat(2n)`'s words, later possibly a fresh array from an inner
`nat.mul` whose `z.make` could not reuse `t`): cap `0 < tc < 2^40`, live in `Lk`, inside `M`'s free part or fresh
(inside `R.rt`, apart from `L1`), apart from the stack's current header and free part. `LB.tsep*`: its separation
facts; `LB.mpreT`: `MPre` of the chunk product one frame down.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep)

/-- see the module doc -/
@[reducible] def TOK (R : RtInv) (L1 Lk : List (Nat × Nat)) (M Mi : Memory) (st tp tc : Nat) : Prop :=
  0 < tc ∧ tc < 2 ^ 40 ∧ NatLive Mi R Lk tp tc ∧
    ((stW M st + 8 * stLen M st ≤ tp ∧ tp + 8 * tc ≤ stW M st + 8 * stCap M st) ∨
      (InRanges tp (8 * tc) R.rt ∧ ApartAll tp (8 * tc) L1)) ∧ StkSep Mi st tp (8 * tc)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
  {Mi : Memory} {tp tc : Nat}

/-- `t`'s array is a classified write range -/
theorem TOK.cls (ht : TOK R L1 Lk M Mi st tp tc) (N : Nat) : LCls R L1 M st p N [(tp, tp + 8 * tc)] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
  obtain ⟨-, -, -, hloc, -⟩ := ht
  refine ⟨by simp only; omega, ?_⟩
  rcases hloc with ⟨h1, h2⟩ | ⟨hin, hap⟩
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by simpa using hin, by simpa using hap⟩))

/-- `t`'s separation facts: outside the window, apart from the NatSqr.guard word, the result `p` and every operand range held
in `L` and `StkSep` at the entry -/
theorem LB.tsep (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi)
    (ht : TOK R L1 Lk M Mi st tp tc) :
    Outside tp (8 * tc) (win s W 88) ∧ Apart tp (8 * tc) (NatSqr.guard s) 8 ∧ Apart tp (8 * tc) p (8 * c) ∧
      ∀ a n, Held R L a n → StkSep s.mem st a n → Apart tp (8 * tc) a n := by
  obtain ⟨hW, hWs, -, -, hout, hgr, hga, hcap, -⟩ := h.lay
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, hfg, hfw, -, -, hfh, -⟩ := hsp
  simp only [NatSqr.guard, BasicSqr.freeP, BasicSqr.freeN] at hfg hfw hfh ⊢
  obtain ⟨-, -, -, hloc, -⟩ := ht
  have h40 := h.h40
  rcases hloc with ⟨h1, h2⟩ | ⟨hin, hap⟩
  · rw [eW, eL] at h1; rw [eW, eC] at h2
    have hpf := h.core.pfree (by omega)
    simp only [BasicSqr.freeP, BasicSqr.freeN] at hpf
    refine ⟨hfw.of_sub (by omega) (by omega), by unfold Apart at hfg ⊢; omega, by unfold Apart at hpf ⊢; omega,
      fun a n _ hs => ?_⟩
    have := hs.2.1; simp only [BasicSqr.freeP, BasicSqr.freeN] at this; unfold Apart at this ⊢; omega
  · have hw := NatSub.outside_of_inRanges hout hin
    have hg := NatSub.outside_of_inRanges hgr hin
    refine ⟨by simp only [win, outside_cons, outside_nil, and_true]; omega, by unfold Apart; omega, ?_,
      fun a n hh _ => apart_of_held (h.core.ext.held hh) hin hap⟩
    rcases h.core.kind with ⟨hpz, hcz⟩ | ⟨-, -, hin1⟩
    · have hzl : NatLive s.mem R L zp zc := h.core.pre.2.2.2.2.2.1.2.2.1.2.1
      rw [← hpz, ← hcz] at hzl
      exact apart_of_held (h.core.ext.held (hzl (by omega)).2.1) hin hap
    · exact apart_of_apartAll hap hin1

theorem stkSep_sub {m : Memory} {st a n a' n' : Nat} (h : StkSep m st a n) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) :
    StkSep m st a' n' := by
  obtain ⟨q1, q2, q3⟩ := h; unfold Apart at q1 q2 q3; exact ⟨by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega⟩

set_option maxRecDepth 20000 in
/-- **`MPre` of the chunk product** `t.mul(stk, x[i:i+cc], y)` one frame down (`SP - 256`, window `W - 256`) -/
theorem LB.mpreT (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi)
    (ht : TOK R L1 Lk M Mi st tp tc) {S1 : State} (hsp : S1.sp.toNat = s.sp.toNat - 256)
    (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = Mi) {i cc : Nat} (hi : yl ≤ i) (hc0 : 0 < cc) (hcn : cc ≤ yl)
    (hic : i + cc ≤ xl) (hcost : mulCQ cc yl + stkR H Mi st ≤ bk) :
    MPre R bk H Lk (W - 256) tp tc st (xp + 8 * i) cc (xc - i) yp yl yc S1 := by
  obtain ⟨hW, hWs, -, -, hout, hgr, hga, hcap, -, -, hx12, hy12, hxlc, hylc, hxc40, hyc40⟩ := h.lay
  have hpre := h.core.pre
  obtain ⟨-, hmw, hsv, -, hwt, ⟨⟨-, -, -, hxacc, hxh, hxw⟩, ⟨-, -, -, hyacc, hyh, hyw⟩, -, hlen⟩, -, ⟨hlvH, -⟩, -⟩ := hpre
  have h40 := h.h40
  obtain ⟨htw, htg, -, htop⟩ := h.tsep ht
  obtain ⟨ht0, ht40, htl, -, hts⟩ := ht
  have hwin : ∀ x k, Outside x k (win s W 88) → Outside x k (win S1 (W - 256) 88) := by
    intro x k hx; simp only [win, outside_cons, outside_nil, and_true] at hx ⊢; rw [hsp]; omega
  have hxH : Held R L xp (8 * xl) := (hxh (by omega)).1.sub (Nat.le_refl _) (by omega)
  have hyH : Held R L yp (8 * yl) := (hyh (by omega)).1.sub (Nat.le_refl _) (by omega)
  obtain ⟨hxo, hxs⟩ := hxw (by omega)
  obtain ⟨hyo, hys⟩ := hyw (by omega)
  have htx := htop _ _ hxH hxs
  have hty := htop _ _ hyH hys
  have hacc : ∀ a n w, Mi.accessible a n w = s.mem.accessible a n w := fun a n w => h.frE.accessible a n w
  have hsl := h.slen
  obtain ⟨-, eL, -⟩ := h.hdrM
  have hmc := mulW_chunk hc0 hcn (by omega : 2 * cc ≤ xl)
  subst hm
  refine ⟨h.callee hsp hg rfl (by omega) (by omega), by omega, hsv, h.glob hwin, hwt, ⟨⟨by omega, by omega, by omega,
    fun _ => by rw [hacc]; exact Memory.accessible_mono _ (hxacc (by omega)) (by omega) (by omega),
    fun _ => ⟨h.ext.held (h.core.ext.held ((hxh (by omega)).1.sub (by omega) (by omega))), by
      have := (hxh (by omega)).2; omega⟩,
    fun _ => ⟨hwin _ _ (hxo.of_sub (by omega) (by omega)), stkSep_sub (h.sep hxH hxs) (by omega) (by omega)⟩⟩,
    ⟨hylc, hyc40, hy12, fun h0 => by rw [hacc]; exact hyacc h0,
    fun hc => ⟨h.ext.held (h.core.ext.held (hyh hc).1), (hyh hc).2⟩, fun _ => ⟨hwin _ _ hyo, h.sep hyH hys⟩⟩,
    ⟨ht40, htl, hwin _ _ htw, fun _ => ⟨by simp only [NatSqr.guard] at htg; rw [hg]; exact htg, hts⟩,
      Or.inr fun _ _ => by unfold Apart at htx ⊢; omega, Or.inr fun _ _ => hty⟩, ?_⟩,
    h.stkPre hsp hg rfl (by omega) (by omega), ⟨by rw [hsl, eL]; simp only [rnd]; omega, hcost⟩,
    by rw [hg]; exact h.inv⟩
  rw [hsl, eL]; simp only [rnd]; omega

end

end FvModexp.Arm64.Q.NatMul
