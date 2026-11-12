import FvModexp.Proofs.Arm64.Exp.P2PreX0
import FvModexp.Proofs.Arm64.Exp.P2PreTr

/-!
# `buildPrecomputationWindowModPower2` (arm64): `powers[1] = powers[1].trunc(x, logM)` (nat.go:883) → `JT` (agent infra)

At the `nat.trunc` entry with `z = powers[1] = (bp + 8 w, w, 2 w)` (the fill loop's header), the caller's `x`, `n = logM`:
the callee precondition from the context and `Pre`, and the continuation into `JT` (the result reuses `z`; its length is
at most `w`; its value is `X mod 2^logM = p2Pow 1`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

theorem p2_one {lm X : Nat} : Exp.p2Pow lm X 1 = X % 2 ^ lm := by rw [Exp.p2Pow]; simp

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callTrX (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hkc : 4608 ≤ kc) (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s)
    (kT : JT impl R kc sqC mlC b L st pw pl lm x xl s)
    {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 xc : Nat}
    (hrs : RS0 R kc L st pw pl lm s (natVal s.mem x xl) bp M L1 b1 1)
    (hb : b - stackNatCost (stLen s.mem st) (NB pl lm) ≤ b1)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 208)) (h28 : S'.regs 28 = s.regs 28)
    (h29 : S'.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216)) (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1786000) (h30 : S'.regs 30 = BitVec.ofNat 64 pcT)
    (h0 : S'.regs 0 = BitVec.ofNat 64 (bp + 8 * (1 * W lm))) (h1 : S'.regs 1 = BitVec.ofNat 64 (W lm))
    (h2 : S'.regs 2 = BitVec.ofNat 64 (2 * W lm)) (h3 : S'.regs 3 = BitVec.ofNat 64 x)
    (h4 : S'.regs 4 = BitVec.ofNat 64 xl) (h5 : S'.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S'.regs 6 = BitVec.ofNat 64 lm) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S' (GoalQ R kc sqC mlC b L st pw pl lm x xl s) := by
  have hf := pf_of hpre (by omega)
  have hspN : S'.sp.toNat = s.sp.toNat - 208 := by
    rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨-, hsv, -, -, -, -, hlm, -, -, -, -, -, -, hsapw, -, ⟨hx40, -, hx48, -, hxw⟩, -, hxl, -, -, -, -, -, hcost,
    -⟩ := id hpre
  have hc := hrs.c
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := 1) (by omega)
  have hz := bufArr hpre hc hf hspN h28 hm hkT haT (a := bp + 8 * (1 * W lm)) (c := 2 * W lm) (by omega) hin
    (by omega) (by have := hc.scr.al; omega) (by omega)
  obtain ⟨xv, xn, xacc, xh, xap⟩ := x_ctx hpre hc
  have hmk : makeCost (truncNeed xl lm) ≤ tC lm :=
    makeCost_le (b := W lm + 4) (by simp only [truncNeed, W]; omega) (by omega)
  have hroom : tC lm ≤ b1 := by
    have h2 : stackNatCost (stLen s.mem st) (NB pl lm) + tC lm ≤ b := Nat.le_trans (Nat.le_add_right _ _) hcost
    omega
  have hK := hf.w.sp
  simp only [K] at hK
  have hrdin : RdIn R L1 S' stkT aboveT x xl := by
    refine ⟨by omega, by rw [hm]; exact xacc, hx48, xh, ?_⟩
    simp only [win, K, A, outside_cons, outside_nil, and_true] at hxw ⊢
    rw [hspN]; omega
  refine LibCalls.truncCall hap hns htr (b := b1) (L := L1) (ra_bp hap hnf 147 (by decide)) (by rw [hpc, trunc_addr])
    h30 h0 h1 h2 h3 h4 h5 h6 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by decide)
    ⟨callEnv_ctx hpre hc hsp h28 hm hkT haT, hsv, by omega, hz.1, hrdin, by omega, by omega,
      Or.inr fun _ h => by have := xap h; unfold Apart at this ⊢; omega,
      Nat.le_trans hmk hroom, by rw [hm, h28]; exact hc.inv⟩ (Or.inl (by rw [hm]; exact xn)) (Or.inr (Or.inl (by omega)))
    fun s' hpc' hsp' h28' h29' h18' hrg hpost => ?_
  obtain ⟨p', l', c', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', hre, -⟩, -, ⟨hLE, hbud', hinv'⟩, hF',
    hLF'⟩ := hpost
  obtain ⟨rfl, rfl⟩ := hre (by simp only [truncNeed, W]; omega)
  rw [hm] at hF' hLF' hrg hv'
  rw [h28] at hinv'
  have hws : ∀ r ∈ [(bp + 8 * (1 * W lm), bp + 8 * (1 * W lm) + 8 * (2 * W lm))], WOK R L s st r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact wok_buf hc.scr (by omega) hin
  have hsah := sa_hdr' hc.ain hc.bu hc.sa hc.sap hLE (fun b n h1 h2 => by
      have hd := hf.w.hd
      have hzs := (hz.2.2.2 (by omega)).1
      simp only [win, K, A, outside_cons, outside_nil, and_true] at hd
      unfold Apart at hzs
      exact rd_keep hf.w hspN hkT haT hF' hLF' (hc.sa.1.2.1.sub h1 h2) (by simp only [K, A]; omega)
        fun r hr hr' => by simp only [List.mem_singleton] at hr; subst hr; simp only at hr' ⊢; omega)
    hF'.accessible
  have hc2 := keepC hc hf.w hspN hkT haT hws hF' hLF' hrg hLE hinv' hsah.1 hsah.2.1 hsah.2.2.1 hsah.2.2.2
  have hrs2 := rs0_call hrs hf hsapw (by omega) hspN hkT haT (fun r hr => List.mem_append_left _ hr) hws
    (Nat.le_refl _) (by omega) hF' hLF' hc2
  have hlW : l' ≤ W lm := len_le_w hn' (by rw [hv']; exact Nat.mod_lt _ (Nat.two_pow_pos _))
  refine kT s' bp L' b' l' hpc' (hsp'.trans hsp) (h28'.trans h28) (h29'.trans h29) (h18'.trans h18) e0 e1 e2 hrs2
    hlW (hv'.trans (by rw [xv, PV, p2_one])) hn' ?_
  exact bud_step hb hbud' hmk

end

end FvModexp.Arm64.P2Pre
