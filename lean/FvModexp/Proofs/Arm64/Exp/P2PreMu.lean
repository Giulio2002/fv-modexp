import FvModexp.Proofs.Arm64.Exp.P2PreTr

/-!
# `buildPrecomputationWindowModPower2` (arm64): `*p1 = p1.mul(stk, *p, powers[1])` (nat.go:895) → `JC` (agent infra)

At the `nat.mul` entry with `z = powers[i+1] = (bp + 8 (i+1) w, w, 2 w)` (the fill loop's header), `x = powers[i]`
and `y = powers[1]` (computed, cap `w`): the callee precondition from `RS`, and the continuation into `JC i` (the result
REUSES `z`: `len x + len y ≤ 2 w` and the cap ends differ).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

theorem mul_addr : segAddr Extracted.program fnMul = 1814128 := by decide

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callMulH (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkM aboveM : Nat} (hmu : MulHypX impl R ns stkM aboveM mlC) (hkM : stkM ≤ kc) (haM : aboveM ≤ 88)
    (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c') (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {i : Nat}
    (kC : JC impl R kc sqC mlC b L st pw pl lm x xl s i) {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hrs : RS R kc L st pw pl lm s (natVal s.mem x xl) bp M L1 b1 i (i + 1)) (hlo2 : Lo2 s pw i M)
    (hi2 : i % 2 = 0) (hi : 2 ≤ i) (hip : i + 2 ≤ pl)
    (hb : b - (c0 (stLen s.mem st) pl lm + (i / 2 - 1) * rc sqC mlC (stLen s.mem st) pl lm +
      (sqC (ℓ1 (stLen s.mem st) pl lm) (W lm) + tC lm)) ≤ b1)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 208)) (h28 : S'.regs 28 = s.regs 28)
    (h29 : S'.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216)) (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1814128) (h30 : S'.regs 30 = BitVec.ofNat 64 1791948)
    (h0 : S'.regs 0 = BitVec.ofNat 64 (bp + 8 * ((i + 1) * W lm))) (h1 : S'.regs 1 = BitVec.ofNat 64 (W lm))
    (h2 : S'.regs 2 = BitVec.ofNat 64 (2 * W lm)) (h3 : S'.regs 3 = BitVec.ofNat 64 st)
    (h4 : S'.regs 4 = BitVec.ofNat 64 (bp + 8 * (i * W lm)))
    {xl' : Nat} (hxl : M.readLE (pw + 24 * i + 8) 8 = xl') (h5 : S'.regs 5 = BitVec.ofNat 64 xl') (h6 : S'.regs 6 = BitVec.ofNat 64 (W lm))
    (h7 : S'.regs 7 = BitVec.ofNat 64 (bp + 8 * (1 * W lm)))
    {yl' : Nat} (hyl : M.readLE (pw + 24 * 1 + 8) 8 = yl') (h8 : S'.regs 8 = BitVec.ofNat 64 yl') (h9 : S'.regs 9 = BitVec.ofNat 64 (W lm)) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S' (GoalQ R kc sqC mlC b L st pw pl lm x xl s) := by
  subst hxl hyl
  have hf := pf_of hpre (by omega)
  have hspN : S'.sp.toNat = s.sp.toNat - 208 := by
    rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨-, hsv, -, -, -, -, -, -, -, -, -, -, -, hsapw, -, -, -, -, -, -, hlen, -, -, hcost, -⟩ := id hpre
  have hc := hrs.c
  obtain ⟨-, -, d1, dv, -⟩ := hrs.d i (by omega)
  obtain ⟨-, -, e1', ev, -⟩ := hrs.d 1 (by omega)
  have hal : bp % 8 = 0 := hc.scr.al
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hst : stLen M st = ℓ1 (stLen s.mem st) pl lm := hc.sa.2.1
  have hsep := pw_sep (lm := lm) (j := i) (k := i + 1) (by omega)
  have hsep1 := pw_sep (lm := lm) (j := 1) (k := i) (by omega)
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i + 1) (by omega)
  have hroom := bud_room2 hcost hip hi hb (t := mlC (ℓ1 (stLen s.mem st) pl lm) (W lm) (W lm))
    (by simp only [rc]; omega)
  have hz := bufArr hpre hc hf hspN h28 hm hkM haM (a := bp + 8 * ((i + 1) * W lm)) (c := 2 * W lm) (by omega) hin
    (by omega) (by omega) (by omega)
  have hx := bufArr hpre hc hf hspN h28 hm hkM haM (a := bp + 8 * (i * W lm)) (c := W lm) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have hy := bufArr hpre hc hf hspN h28 hm hkM haM (a := bp + 8 * (1 * W lm)) (c := W lm) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have hmono := hmm (ℓ1 (stLen s.mem st) pl lm) _ _ _ _ d1 e1'
  have hrnd := rnd_le (NB pl lm)
  refine LibCalls.mulCallX hap hns hmu (b := b1) (L := L1) (ra_bp hap hnf 255 (by decide)) (by rw [hpc, mul_addr])
    h30 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by omega) (by omega) (by omega) (by have := hc.sa.1.2.2.2.1; omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by decide)
    ⟨callEnv_ctx hpre hc hsp h28 hm hkM haM, hsv, by rw [hm]; exact globals_ctx hpre hc hspN hkM haM,
      by omega, hz.1, hx.2.1 _ d1, hy.2.1 _ e1', by omega, by omega, Or.inr fun _ _ => by unfold Apart; omega,
      Or.inr fun _ _ => by unfold Apart; omega,
      stkIn_ctx hpre hc hf hspN h28 hm hkM haM, by rw [hm, hst]; simp only [ℓ1]; omega,
      by rw [hm]; exact hz.2.2.2, by rw [hm]; exact sa_sub hx.2.2.2 (by omega),
      by rw [hm]; exact sa_sub hy.2.2.2 (by omega),
      by rw [hm, hst]; omega, by rw [hm, h28]; exact hc.inv⟩ (hx.2.2.1 _ d1) (hy.2.2.1 _ e1')
    ⟨stkX_ctx hpre hc hf hspN h28 hm hkM haM, (hz.1.2.2 (by omega)).1, fun he => absurd he (by omega),
      fun he => absurd he (by omega), by rw [hm]; exact bufOp hpre hc (by omega) hin,
      by rw [hm]; exact bufOp hpre hc (by omega) (by omega), by rw [hm]; exact bufOp hpre hc (by omega) (by omega)⟩
    fun s' hpc' hsp' h28' h29' h18' hrg hpost hreu => ?_
  obtain ⟨p', l', c', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', -⟩, ⟨hLE, hbud', hinv'⟩, hsb, -, hF',
    hLF'⟩ := hpost
  obtain ⟨r0, r2⟩ := hreu (by omega) (by
    intro o ho; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp only <;> omega)
  have hc' : c' = 2 * W lm := ofNat_inj (by omega) (by omega) (e2.symm.trans r2)
  have hp' : p' = bp + 8 * ((i + 1) * W lm) := ofNat_inj (by have := (hlive' (by omega)).2.2.2; omega) (by omega)
    (e0.symm.trans r0)
  subst hc' hp'
  rw [hm] at hF' hLF' hrg hsb hbud' hv'
  rw [h28] at hinv'
  rw [hst] at hbud'
  have hwok := wok_zs (zn := 8 * (2 * W lm)) hc (by omega) hin
  have hsa' := sa_back hc.sa hsb.1 hc.le
  have hsap' := sap_back hc.sap hc.scr.held hsb.1
  have hF2 : MemFrame M s'.mem (R.rt ++ winA S' stkM aboveM ++ ([(bp + 8 * ((i + 1) * W lm),
      bp + 8 * ((i + 1) * W lm) + 8 * (2 * W lm))] ++ stWs M st)) := by rw [List.append_assoc] at hF'; exact hF'
  have hc2 := keepC hc hf.w hspN hkM haM hwok hF2 hLF' hrg hLE hinv' hsa' hsap' (hc.ain.trans hsb.2 hLE)
    (bu_back hc.bu hc.scr.held hsb.1)
  have hrs2 := rs_call hrs hf hsapw (by omega) hspN hkM haM (fun r hr => hr) hwok (Nat.le_refl _) (by omega) hF2
    hLF' hc2
  have hlo2' := lo2_keep hf.w hspN hkM haM hwok hF2 hlo2
  refine kC s' bp L' b' l' hpc' (hsp'.trans hsp) (h28'.trans h28) (h29'.trans h29) (h18'.trans h18) r0 e1 r2 hrs2
    hlo2' hlc' (hv'.trans (by rw [dv, ev])) hn' hi2 hi hip ?_
  rw [← Nat.add_assoc]
  exact bud_step hb hbud' hmono

end

end FvModexp.Arm64.P2Pre
