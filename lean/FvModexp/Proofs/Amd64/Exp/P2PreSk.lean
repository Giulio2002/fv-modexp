import FvModexp.Proofs.Amd64.Exp.P2PreLD
import FvModexp.Proofs.Amd64.Exp.P2PreTrC

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the stack object's `StkPre` at a loop callee (`sqr`, `mul`) (agent divmc
s65)

`stkPre_ctx`: at a call (`RSP_c = RSP - 184`, window `W' ≤ kc`, above `≤ 88`) after `stk.nat`, the stack object's facts
`Q.NatSqr.StkPre` from the entry's `StkPre` (in `Pre`) and the context: the stack's array is the entry's (its length
grown, so the free part shrank) or a fresh runtime array (outside the window, apart from the guard word and the TLS
slot, which `CallEnv` keeps out of `R.rt`). Adapted from divmc's `Amd64/NatQ/KSqrRel` (`KM.stk`, `KM.stkT`,
`KM.stkPre`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

theorem apart_of_held' {R : RtInv} {L : List (Nat × Nat)} {w n p k : Nat} (hh : Held R L w n)
    (hin : InRanges p k R.rt) (hap : ApartAll p k L) : Apart p k w n := by
  rcases hh with h | h
  · obtain ⟨r, hr, h1, h2⟩ := h
    have := hap r hr; unfold Apart at this ⊢; omega
  · have := NatSub.outside_of_inRanges h hin; unfold Apart; omega

section
variable {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- **`StkPre` at a loop callee** -/
theorem stkPre_ctx (hpre : Pre R kc b L st pw pl ws lm x xl s) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) {S' : State}
    (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 184) (h14 : S'.regs 14 = s.regs 14) (hfs : S'.fsBase = s.fsBase)
    (hm : S'.mem = M) {W' a : Nat} (hW : W' ≤ kc) (ha : a ≤ 88) : StkPre R L1 S' W' a st := by
  have hK : 184 + kc ≤ (s.regs 4).toNat := by have := hpre.1.2.1.1; simp only [K, regSP] at this; omega
  obtain ⟨⟨-, -, -, -, hout, -, hgr, -, -, -, htrt, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsp0, -⟩ := id hpre
  obtain ⟨hst0, ⟨-, hsth, -, -, -, hlc0, -⟩, hstw, hstg, hsarr, hfg, hfw, hstf, hstwb, hfh, hsgA, hfgA, hsttl, hsatl,
    hftl⟩ := hsp0
  have hgrt : Outside RunIface.gA 32 R.rt := hpre.2.2.1.2.2.2.2.2.2.2.2.1
  have hwin : ∀ y k, Outside y k (win s (K kc) A) → Outside y k (win S' W' a) := by
    intro y k hy; simp only [win, K, A, outside_cons, outside_nil, and_true] at hy ⊢; rw [hsp]; omega
  obtain ⟨hok, hlen, harr⟩ := hc.sa
  have hlc := hok.2.2.2.2.2.1
  have hnl := hok.2.2.2.2.1
  subst hm
  simp only [StkPre, Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hfg hfw hstf hfh hfgA hftl ⊢
  simp only [Q.NatSqr.guard, tls, h14, hfs] at hstg hsarr hfg hsttl hsatl hftl ⊢
  refine ⟨hst0, hok, hwin _ _ hstw, hstg, ?_⟩
  rcases harr with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · rw [e1, e2] at hnl ⊢; rw [e2] at hlc
    refine ⟨fun h => ⟨hwin _ _ (hsarr h).1, (hsarr h).2⟩, ?_, hwin _ _ (hfw.of_sub (by omega) (by omega)), ?_, hstwb,
      hc.le.held (hfh.sub (by omega) (by omega)), hsgA, ?_, hsttl, hsatl, ?_⟩
    · unfold Apart at hfg ⊢; omega
    · unfold Apart at hstf ⊢; omega
    · unfold Apart at hfgA ⊢; omega
    · unfold Apart at hftl ⊢; omega
  · have hgo := NatSub.outside_of_inRanges hgr hin
    have hto := NatSub.outside_of_inRanges htrt hin
    have hga := NatSub.outside_of_inRanges hgrt hin
    have hst := apart_of_held' hsth hin hap
    have hwo := NatSub.outside_of_inRanges (hout.of_sub (a := (s.regs 4).toNat - K kc) (n := K kc + A)
      (by omega) (by omega)) hin
    simp only [K, A] at hwo
    have hw : ∀ y k, stW S'.mem st ≤ y → y + k ≤ stW S'.mem st + 8 * stCap S'.mem st → Outside y k (win S' W' a) := by
      intro y k h1 h2
      simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
    have hcap : 0 < stCap S'.mem st := by
      have := nb_pos (pl := pl) (lm := lm) (by have := pl_facts hpre; omega) (w_facts hpre).1
      simp only [StackNat.rnd] at hlen; omega
    refine ⟨fun _ => ⟨hw _ _ (by omega) (by omega), by unfold Apart; omega⟩, by unfold Apart; omega,
      hw _ _ (by omega) (by omega), by unfold Apart at hst ⊢; omega, hstwb, ?_, hsgA, by unfold Apart; omega, hsttl,
      fun _ => by unfold Apart; omega, by unfold Apart; omega⟩
    obtain ⟨-, hh, -, -⟩ := hnl hcap
    exact hh.sub (by omega) (by omega)

end

end FvModexp.Amd64.P2Pre
