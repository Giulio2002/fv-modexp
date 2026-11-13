import FvModexp.Proofs.Arm64.Exp.P2PreSq
import FvModexp.Proofs.Common.SubMod2NMath

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (arm64): `*p = p.trunc(*p, logM)` (nat.go:893 / 896) → `JB` / `JD` (agent infra)

At the `nat.trunc` entry with `z = x = (bp + 8 k w, l, 2 w)` (the result of the round's `sqr` / `mul`, `k = kf i`),
`n = logM`: the callee precondition from `RS`, and the continuation into the target join (the result reuses `z`; its
length is at most `w` because the value is below `2^logM`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs RdIn WrOut)

theorem trunc_addr : segAddr Extracted.program fnTrunc = 1786000 := by decide

theorem makeCost_le {a b : Nat} (h : a ≤ b) (hb : 2 ≤ b) : makeCost a ≤ makeCost b := by
  unfold makeCost makeCap allocCost
  split <;> split <;> omega

/-- a normalised nat below `2^lm` has at most `w = ⌈lm/64⌉` words -/
theorem len_le_w {m : Memory} {p l lm : Nat} (hn : NatNorm m p l) (hv : natVal m p l < 2 ^ lm) : l ≤ W lm := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · omega
  have h1 := SubMod2N.natVal_lower m p l hn h0
  have : 64 * (l - 1) < lm := (Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt h1 hv)
  simp only [W]; omega

theorem bud_room2 {c0 rc pl i b b1 cs t : Nat} (hc : c0 + (pl / 2 - 1) * rc ≤ b) (hi : i + 2 ≤ pl) (h2 : 2 ≤ i)
    (hb : b - (c0 + (i / 2 - 1) * rc + cs) ≤ b1) (hct : cs + t ≤ rc) : t ≤ b1 := by
  have : (i / 2 - 1) * rc + rc ≤ (pl / 2 - 1) * rc := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  omega

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat} {mlC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callTr (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hkc : 4608 ≤ kc) (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {i : Nat} {pcT ri : Nat}
    (hri : ri < 300) (hpcT : pcT = 1790928 + 4 * ri) {kf vT : Nat → Nat} {cstS cstT : Nat}
    (kT : JX impl R kc sqC mlC b L st pw pl lm x xl s pcT (fun i M => Lo2 s pw i M) kf vT (W lm) cstT i)
    (hk1 : i ≤ kf i) (hk2 : kf i ≤ i + 1) (hcst : cstT = cstS + tC lm) (hct : cstT ≤ rc sqC mlC (stLen s.mem st) pl lm)
    {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 l v : Nat}
    (hrs : RS R kc L st pw pl lm s (natVal s.mem x xl) bp M L1 b1 i (kf i)) (hlo2 : Lo2 s pw i M)
    (hi2 : i % 2 = 0) (hi : 2 ≤ i) (hip : i + 2 ≤ pl)
    (hb : b - (c0 (stLen s.mem st) pl lm + (i / 2 - 1) * rc sqC mlC (stLen s.mem st) pl lm + cstS) ≤ b1)
    (hl : l ≤ 2 * W lm) (hnorm : NatNorm M (bp + 8 * (kf i * W lm)) l) (hv : natVal M (bp + 8 * (kf i * W lm)) l = v) (hvT : vT i = v % 2 ^ lm)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 208)) (h28 : S'.regs 28 = s.regs 28)
    (h29 : S'.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216)) (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1786000) (h30 : S'.regs 30 = BitVec.ofNat 64 pcT)
    (h0 : S'.regs 0 = BitVec.ofNat 64 (bp + 8 * (kf i * W lm))) (h1 : S'.regs 1 = BitVec.ofNat 64 l)
    (h2 : S'.regs 2 = BitVec.ofNat 64 (2 * W lm)) (h3 : S'.regs 3 = BitVec.ofNat 64 (bp + 8 * (kf i * W lm)))
    (h4 : S'.regs 4 = BitVec.ofNat 64 l) (h5 : S'.regs 5 = BitVec.ofNat 64 (2 * W lm))
    (h6 : S'.regs 6 = BitVec.ofNat 64 lm) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S' (GoalQ R kc sqC mlC b L st pw pl lm x xl s) := by
  subst hpcT
  have hf := pf_of hpre (by omega)
  have hspN : S'.sp.toNat = s.sp.toNat - 208 := by
    rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨-, hsv, -, -, -, -, hlm, -, -, -, -, -, -, hsapw, -, -, -, -, -, -, -, -, -, hcost, -⟩ := id hpre
  have hc := hrs.c
  have hal : bp % 8 = 0 := hc.scr.al
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := kf i) (by omega)
  have hroom := bud_room2 hcost hip hi hb (by rw [← hcst]; exact hct)
  have hz := bufArr hpre hc hf hspN h28 hm hkT haT (a := bp + 8 * (kf i * W lm)) (c := 2 * W lm) (by omega) hin
    (by omega) (by omega) (by omega)
  have hmk : makeCost (truncNeed l lm) ≤ tC lm := makeCost_le (b := W lm + 4) (by simp only [truncNeed, W]; omega) (by omega)
  refine LibCalls.truncCall hap hns htr (b := b1 + stkR (HP (stLen s.mem st) pl lm) M st) (L := L1) (ra_bp hap hnf ri hri) (by rw [hpc, trunc_addr]) h30
    h0 h1 h2 h3 h4 h5 h6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by have := Nat.lt_of_lt_of_le hri (by decide : 300 ≤ 1000); omega)
    ⟨callEnv_ctx hpre hc hsp h28 hm hkT haT, hsv, hl, hz.1, hz.2.1 _ hl, by omega, by omega, Or.inl rfl,
      by omega, by rw [hm, h28]; exact hc.inv⟩ (Or.inl (by rw [hm]; exact hnorm)) (Or.inl rfl)
    fun s' hpc' hsp' h28' h29' h18' hrg hpost => ?_
  obtain ⟨p', l', c', e0, e1, e2, L', b', ⟨hv', hn', hlc', hc40', hlive', hre, -⟩, -, ⟨hLE, hbud', hinv'⟩, hF',
    hLF'⟩ := hpost
  obtain ⟨rfl, rfl⟩ := hre (by simp only [truncNeed]; omega)
  rw [hm] at hF' hLF' hrg hv'
  rw [h28] at hinv'
  have hws : ∀ r ∈ [(bp + 8 * (kf i * W lm), bp + 8 * (kf i * W lm) + 8 * (2 * W lm))], WOK R L s st r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact wok_buf hc.scr (by omega) hin
  have hhdr : ∀ b n, st ≤ b → b + n ≤ st + 24 → s'.mem.readLE b n = M.readLE b n := fun b n h1 h2 => by
      have hd := hf.w.hd
      have hzs := (hz.2.2.2 (by omega)).1
      simp only [win, K, A, outside_cons, outside_nil, and_true] at hd
      unfold Apart at hzs
      exact rd_keep hf.w hspN hkT haT hF' hLF' (hc.sa.1.2.1.sub h1 h2) (by simp only [K, A]; omega)
        fun r hr hr' => by simp only [List.mem_singleton] at hr; subst hr; simp only at hr' ⊢; omega
  have hsah := sa_hdr' hc.ain hc.bu hc.sa hc.sap hLE hhdr hF'.accessible
  obtain ⟨b2, hinv2, hbud2⟩ := P2Q.effL (r' := stkR (HP (stLen s.mem st) pl lm) s'.mem st) hinv' hbud' (by omega)
    (stkR_congr (hhdr _ _ (by omega) (by omega)))
  have hc2 := keepC hc hf.w hspN hkT haT hws hF' hLF' hrg hLE hinv2 hsah.1 hsah.2.1 hsah.2.2.1 hsah.2.2.2
  have hrs2 := rs_call hrs hf hsapw (by omega) hspN hkT haT (fun r hr => List.mem_append_left _ hr) hws
    (Nat.le_refl _) (by omega) hF' hLF' hc2
  have hlW : l' ≤ W lm := len_le_w hn' (by rw [hv']; exact Nat.mod_lt _ (Nat.two_pow_pos _))
  refine kT s' bp L' b2 l' hpc' (hsp'.trans hsp) (h28'.trans h28) (h29'.trans h29) (h18'.trans h18) e0 e1 e2 hrs2
    (lo2_keep hf.w hspN hkT haT hws hF' hlo2) hlW (hv'.trans (by rw [hv, hvT])) hn' hi2 hi hip ?_
  rw [hcst, ← Nat.add_assoc]
  exact bud_step hb hbud2 hmk

end

end FvModexp.Arm64.P2Pre
