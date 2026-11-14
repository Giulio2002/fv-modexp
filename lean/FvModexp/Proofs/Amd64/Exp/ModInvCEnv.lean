import FvModexp.Proofs.Amd64.Exp.ModInvRnd
import FvModexp.Proofs.Amd64.Exp.ModInvSt
import FvModexp.Proofs.Amd64.Exp.CallW

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the callee environment inside a round (agent infra s57; amd64 twin of
`Arm64/Exp/ModInvPre`'s `cenv_at` / `globals_at` / `stkIn_at`)

At a callee entry `S'` of a round (`RSP_c = RSP - 232`, `R14` / `fsBase` the entry's, memory `M` with the runtime facts
`RtM`): `cenv_mi` (the caller environment `CallW.CEnv` at `RSP_c` with window `[RSP_c - kc, RSP_c + 304)` = the
entry window), `globals_mi` (`Globals` outside the callee's window), `stkPre_mi` (the stack object, `StkPre` at the
callee's window). Pure lemmas.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

section
variable {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the TLS slot keeps `g` at a memory the runtime facts describe -/
theorem tls_rt (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) :
    M.accessible (s.fsBase.toNat - 8) 8 false = true ∧ M.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
  obtain ⟨⟨-, ⟨hb', -, -⟩, -, -, -, -, -, -, -, ⟨⟨-, htacc, htg⟩, htrt, htap⟩⟩, -, -, -, -, -, -, hzc0, ⟨-, -, hzw⟩,
    -, -, -, -, -, -, -, -, -, ⟨-, ⟨-, -, -, -, -, hlc, -⟩, -, -, -, -, -, -, -, -, -, -, hsttl, -, hftl⟩, -⟩ := hpre
  obtain ⟨-, hF, -⟩ := hrt
  obtain ⟨-, -, hzt⟩ := hzw hzc0
  simp only [K, A, regSP] at htap hb'
  simp only [Q.NatSqr.tls, Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hsttl hftl
  unfold Apart at htap hzt hsttl hftl
  refine ⟨by rw [hF.accessible]; exact htacc, ?_⟩
  rw [← htg]
  refine frame_bytes hF fun i hi => ?_
  simp only [outside_append, stkWs, win, K, A, outside_cons, outside_nil, and_true]
  exact ⟨⟨⟨htrt.of_sub (by omega) (by omega), by omega⟩, by omega⟩, by omega, by omega⟩

set_option maxRecDepth 20000 in
/-- **the caller environment at a round's callee entry** (`RSP_c = RSP - 232`; window `[RSP_c - kc, RSP_c + 304)`
= the entry window `[RSP - (232 + kc), RSP + 72)`) -/
theorem cenv_mi (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) :
    CallW.CEnv R L1 (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 232) kc 304 M := by
  have hK := sp_K hpre
  obtain ⟨e1, e2, e3, e4⟩ := env_rt hpre hrt
  have hd := dl_rt hpre hrt
  obtain ⟨t1, t2⟩ := tls_rt hpre hrt
  obtain ⟨⟨⟨g1, -, g3⟩, ⟨-, ha, -⟩, hal, -, hout, hga, hgrt, -, hro, ⟨⟨f1, -, -⟩, f5, f6⟩⟩, -⟩ := hpre
  simp only [K, A, regSP, regG, stackguard0Offset, stackguard0] at ha hout hga g1 g3 f6
  have w1 : (s.regs 4).toNat - 232 - kc = (s.regs 4).toNat - (232 + kc) := by omega
  have w2 : kc + 304 = 232 + kc + 72 := by omega
  have w3 : (s.regs 4).toNat - 232 + 304 = (s.regs 4).toNat + 72 := by omega
  refine ⟨by omega, by omega, by omega, by rw [w1, w2]; exact e1, by omega, e2, by rw [e3]; omega,
    by rw [w1, w2]; exact hout, by rw [w1, w2]; exact hga, hgrt, by rw [w1, w3]; exact e4, hd, hro, f1.1, f1.2, t1,
    t2, f5, by rw [w1, w2]; exact f6⟩

/-- the callee's window lies in the entry window below the loop slots -/
theorem win_mi {S' : State} (hK : 232 + kc ≤ (s.regs 4).toNat) (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 304) {a k : Nat} (h : Outside a k (win s (K kc) A)) :
    Outside a k (win S' stk above) := by
  simp only [win, K, A, hsp, outside_cons, outside_nil, and_true] at h ⊢; omega

/-- `Globals` through a frame (adapted from fv-modexp divmc's `Q.NatSqr.globals_frame`, Proofs/Amd64/NatQ/SqrKPre.lean) -/
theorem globals_frameMI {m m' : Memory} {w w' ws : List (Nat × Nat)} (h : RunIface.Globals R m w)
    (hF : MemFrame m m' (R.rt ++ ws)) (hg : Outside RunIface.gA 32 ws) (hw : ∀ a n, Outside a n w → Outside a n w') :
    RunIface.Globals R m' w' := by
  obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := h
  have hrd : ∀ k, k + 8 ≤ 32 → m'.readLE (RunIface.gA + k) 8 = m.readLE (RunIface.gA + k) 8 := fun k hk =>
    hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt.of_sub (by omega) (by omega), hg.of_sub (by omega) (by omega)⟩)
  refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt, hw _ _ hgw,
    by rw [hF.accessible]; exact hwbacc, hwbrt, hw _ _ hwbw⟩
  · rw [e8, hrd 8 (by omega), ← e8]; exact h40
  · rw [e16, hrd 16 (by omega), ← e16]; exact h12
  · rw [e24, hrd 24 (by omega), ← e24]; exact h80
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
    show m'.readLE RunIface.gA 8 = 40; rw [this]; exact h40'

set_option maxRecDepth 20000 in
/-- `Globals` outside a round callee's window -/
theorem globals_mi (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State} (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 304) : RunIface.Globals R M (win S' stk above) := by
  have hK := sp_K hpre
  obtain ⟨-, -, ⟨hgl, gz⟩, -⟩ := hpre
  obtain ⟨-, hF, -⟩ := hrt
  rw [List.append_assoc, List.append_assoc] at hF
  refine globals_frameMI hgl hF ?_ (fun a k h => win_mi hK hsp hstk habove h)
  have hgw := hgl.2.2.2.2.2.2.2.2.2.1
  simp only [outside_append] at gz ⊢
  exact ⟨hgw, gz⟩

/-- the free part of an array apart from a range is apart from it -/
theorem apart_free {w c l a k : Nat} (h : Apart w (8 * c) a k) (hlc : l ≤ c) : Apart (w + 8 * l) (8 * (c - l)) a k := by
  unfold Apart at h ⊢; omega

set_option maxRecDepth 20000 in
/-- **the stack object at a round callee's entry** (`StkPre` at the callee's window) -/
theorem stkPre_mi (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 : Nat} (hrt : RtM R kc L s zp zc st M L1 b1) {S' : State} (hsp : (S'.regs 4).toNat = (s.regs 4).toNat - 232)
    (h14 : S'.regs 14 = s.regs 14) (hfs : S'.fsBase = s.fsBase) (hm : S'.mem = M)
    {stk above : Nat} (hstk : stk ≤ kc) (habove : above ≤ 304) : StkPre R L1 S' stk above st := by
  have hK := sp_K hpre
  obtain ⟨⟨-, -, -, -, hout, -, hgrt, -, -, ⟨-, htrt, -⟩⟩, -, ⟨⟨-, -, -, -, -, -, -, -, hgArt, -, -, -, -⟩, -⟩, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, ⟨h0, hok0, hstw, hstg, harr, hfg, hfw, hsf, hswb, hfh, hsgA, hfgA, hsttl, hsatl,
    hftl⟩, -⟩ := hpre
  obtain ⟨-, -, -, hLE, -, hok, hlen, hor, hain⟩ := hrt
  simp only [K, A] at hout
  have hsub : ∀ a k, Outside a k (win s (K kc) A) → Outside a k (win S' stk above) :=
    fun a k h => win_mi hK hsp hstk habove h
  have hlc : stLen M st ≤ stCap M st := hok.2.2.2.2.2.1
  subst hm
  unfold StkPre
  simp only [Q.NatSqr.guard, Q.NatSqr.tls, Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hfg hfw hsf hfh hfgA hftl
  simp only [Q.NatSqr.guard, Q.NatSqr.tls, h14, hfs, Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hstg hsttl harr hsatl ⊢
  by_cases hold : stW S'.mem st = stW s.mem st ∧ stCap S'.mem st = stCap s.mem st
  · obtain ⟨e0, e2⟩ := hold
    rw [e0, e2, hlen]
    exact ⟨h0, hok, hsub _ _ hstw, hstg, fun hc => ⟨hsub _ _ (harr hc).1, (harr hc).2⟩,
      hfg, hsub _ _ hfw, hsf, hswb, hLE.held hfh, hsgA, hfgA, hsttl, hsatl, hftl⟩
  · obtain ⟨hmem, hc0⟩ := hain hold
    obtain ⟨hIn, hAp⟩ := hor.resolve_left hold
    have hwo : Outside ((s.regs 4).toNat - (232 + kc)) (232 + kc + 72) R.rt := hout
    have a1 := fresh_out hIn hwo
    have a2 := fresh_out hIn hgrt
    have a3 := fresh_apart hIn hAp hok0.2.1
    have a4 := fresh_out hIn hgArt
    have a5 := fresh_out hIn htrt
    have hfr : ∀ {a k : Nat}, Apart (stW S'.mem st) (8 * stCap S'.mem st) a k →
        Apart (stW S'.mem st + 8 * stLen S'.mem st) (8 * (stCap S'.mem st - stLen S'.mem st)) a k :=
      fun h => apart_free h hlc
    have hwo' : ∀ {a k : Nat}, Apart a k ((s.regs 4).toNat - (232 + kc)) (232 + kc + 72) →
        Outside a k (win S' stk above) := fun h => by
      unfold Apart at h; simp only [win, hsp, outside_cons, outside_nil, and_true]; omega
    exact ⟨h0, hok, hsub _ _ hstw, hstg, fun _ => ⟨hwo' a1, a2⟩, hfr a2, hwo' (hfr a1), (hfr a3).symm, hswb,
      Or.inl ⟨_, hmem, by omega, by omega⟩, hsgA, hfr a4, hsttl, fun _ => a5, hfr a5⟩

end

end FvModexp.Amd64.ModInv
