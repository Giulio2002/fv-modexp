import FvModexp.Proofs.Arm64.Exp.P2PreXc

/-!
# `buildPrecomputationWindowModPower2` (arm64): `*p = p.sqr(stk, *p2)` (nat.go:892) → `JA` (agent infra)

At the `nat.sqr` entry with `z = powers[i] = (bp + 8 i w, w, 2 w)` (the fill loop's header), `x = powers[i/2]`
(computed, cap `w`): the callee precondition from `RS`, and the continuation into `JA i` (the result REUSES `z`:
`2 len x ≤ 2 w` and the cap ends differ).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

theorem sqr_addr : segAddr Extracted.program fnSqr = 1815584 := by decide

theorem sa_sub {M : Memory} {st p c k : Nat} (h : StkApart M st p c) (hk : k ≤ c) : StkApart M st p k := by
  intro hk0
  obtain ⟨h1, h2⟩ := h (by omega)
  exact ⟨by unfold Apart at h1 ⊢; omega, fun hlt => by have := h2 hlt; unfold Apart at this ⊢; omega⟩

theorem ofNat_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) :
    a = b := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- the callee-written ranges of a `sqr` / `mul` into `buf` are `WOK` -/
theorem wok_zs {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm : Nat} {s : State} {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 zp zn : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) (h1 : bp ≤ zp)
    (h2 : zp + zn ≤ bp + 8 * NB pl lm) : ∀ r ∈ [(zp, zp + zn)] ++ stWs M st, WOK R L s st r := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · simp only [List.mem_singleton] at hr; subst hr; exact wok_buf hc.scr h1 h2
  · exact wok_stk hc.sa r hr

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callSqrH (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC) (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a') (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {i : Nat}
    (kA : JA impl R kc sqC mlC b L st pw pl lm x xl s i) {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hrs : RS R kc L st pw pl lm s (natVal s.mem x xl) bp M L1 b1 i i)
    (hi2 : i % 2 = 0) (hi : 2 ≤ i) (hip : i + 2 ≤ pl)
    (hb : b - (c0 (stLen s.mem st) pl lm + (i / 2 - 1) * rc sqC mlC (stLen s.mem st) pl lm) ≤ b1)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 208)) (h28 : S'.regs 28 = s.regs 28)
    (h29 : S'.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216)) (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1815584) (h30 : S'.regs 30 = BitVec.ofNat 64 1791732)
    (h0 : S'.regs 0 = BitVec.ofNat 64 (bp + 8 * (i * W lm))) (h1 : S'.regs 1 = BitVec.ofNat 64 (W lm))
    (h2 : S'.regs 2 = BitVec.ofNat 64 (2 * W lm)) (h3 : S'.regs 3 = BitVec.ofNat 64 st)
    (h4 : S'.regs 4 = BitVec.ofNat 64 (bp + 8 * (i / 2 * W lm)))
    {xl' : Nat} (hxl : M.readLE (pw + 24 * (i / 2) + 8) 8 = xl') (h5 : S'.regs 5 = BitVec.ofNat 64 xl')
    (h6 : S'.regs 6 = BitVec.ofNat 64 (W lm)) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S' (GoalQ R kc sqC mlC b L st pw pl lm x xl s) := by
  subst hxl
  have hf := pf_of hpre (by omega)
  have hspN : S'.sp.toNat = s.sp.toNat - 208 := by
    rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨-, hsv, -, -, -, -, -, -, -, -, -, -, -, hsapw, -, -, -, -, -, -, hlen, -, -, hcost, -⟩ := id hpre
  have hc := hrs.c
  obtain ⟨-, -, d1, dv, -⟩ := hrs.d (i / 2) (by omega)
  have hal : bp % 8 = 0 := hc.scr.al
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hst : stLen M st = ℓ1 (stLen s.mem st) pl lm := hc.sa.2.1
  have hsep := pw_sep (lm := lm) (j := i / 2) (k := i) (by omega)
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i) (by omega)
  have hroom := bud_room hcost hip hi hb
  have hz := bufArr hpre hc hf hspN h28 hm hkS haS (a := bp + 8 * (i * W lm)) (c := 2 * W lm) (by omega) hin
    (by omega) (by omega) (by omega)
  have hx := bufArr hpre hc hf hspN h28 hm hkS haS (a := bp + 8 * (i / 2 * W lm)) (c := W lm) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have hmono := hsm (ℓ1 (stLen s.mem st) pl lm) _ _ d1
  have hrnd := rnd_le (NB pl lm)
  refine LibCalls.sqrCallX hap hns hsq (b := b1) (L := L1) (ra_bp hap hnf 201 (by decide)) (by rw [hpc, sqr_addr]) h30 h0 h1 h2 h3 h4
    h5 h6 (by omega) (by omega) (by omega) (by have := hc.sa.1.2.2.2.1; omega) (by omega) (by omega) (by omega)
    (by decide) ⟨callEnv_ctx hpre hc hsp h28 hm hkS haS, hsv, by rw [hm]; exact globals_ctx hpre hc hspN hkS haS,
      by omega, hz.1, hx.2.1 _ d1, by omega, Or.inr fun _ _ => by unfold Apart; omega,
      stkIn_ctx hpre hc hf hspN h28 hm hkS haS, by rw [hm, hst]; simp only [ℓ1]; omega,
      by rw [hm]; exact hz.2.2.2, by rw [hm]; exact sa_sub hx.2.2.2 (by omega),
      by rw [hm, hst]; simp only [rc] at hroom; omega, by rw [hm, h28]; exact hc.inv⟩ (hx.2.2.1 _ d1)
    ⟨stkX_ctx hpre hc hf hspN h28 hm hkS haS, (hz.1.2.2 (by omega)).1, fun he => absurd he (by omega),
      by rw [hm]; exact bufOp hpre hc (by omega) hin, by rw [hm]; exact bufOp hpre hc (by omega) (by omega)⟩
    fun s' hpc' hsp' h28' h29' h18' hrg hpost hreu => ?_
  obtain ⟨p', l', c', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', -⟩, ⟨hLE, hbud', hinv'⟩, hsb, -, hF',
    hLF'⟩ := hpost
  obtain ⟨r0, r2⟩ := hreu (by omega) (by
    intro o ho; simp only [List.mem_singleton] at ho; subst ho; simp only; omega)
  have hc' : c' = 2 * W lm := ofNat_inj (by omega) (by omega) (e2.symm.trans r2)
  have hp' : p' = bp + 8 * (i * W lm) := ofNat_inj (by have := (hlive' (by omega)).2.2.2; omega) (by omega)
    (e0.symm.trans r0)
  subst hc' hp'
  rw [hm] at hF' hLF' hrg hsb hbud' hv'
  rw [h28] at hinv'
  rw [hst] at hbud'
  have hwok := wok_zs (zn := 8 * (2 * W lm)) hc (by omega) hin
  have hsa' := sa_back hc.sa hsb.1 hc.le
  have hsap' := sap_back hc.sap hc.scr.held hsb.1
  have hF2 : MemFrame M s'.mem (R.rt ++ winA S' stkS aboveS ++ ([(bp + 8 * (i * W lm),
      bp + 8 * (i * W lm) + 8 * (2 * W lm))] ++ stWs M st)) := by rw [List.append_assoc] at hF'; exact hF'
  have hc2 := keepC hc hf.w hspN hkS haS hwok hF2 hLF' hrg hLE hinv' hsa' hsap' (hc.ain.trans hsb.2 hLE)
    (bu_back hc.bu hc.scr.held hsb.1)
  have hrs2 := rs_call hrs hf hsapw (by omega) hspN hkS haS (fun r hr => hr) hwok (Nat.le_refl _) (by omega) hF2
    hLF' hc2
  refine kA s' bp L' b' l' hpc' (hsp'.trans hsp) (h28'.trans h28) (h29'.trans h29) (h18'.trans h18) r0 e1 r2 hrs2
    trivial hlc' (hv'.trans (by rw [dv])) hn' hi2 hi hip ?_
  simp only [rc] at hroom hb ⊢
  omega

end

end FvModexp.Arm64.P2Pre
