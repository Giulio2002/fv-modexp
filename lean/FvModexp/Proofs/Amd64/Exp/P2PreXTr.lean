import FvModexp.Proofs.Amd64.Exp.P2PreTrC

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): `powers[1] = powers[1].trunc(x, logM)` (nat.go:883) → `JT` (agent divmc
s64; twin of infra's `Arm64/Exp/P2PreXTr`)

At the `nat.trunc` entry (call `+0x316`) with `z = powers[1] = (bp + 8 w, w, 2 w)` (the fill loop's header), the
caller's `x`, `n = logM`: the callee precondition from the context and `Pre`, and the continuation into `JT` (the
result reuses `z`; its length is at most `w`; its value is `X mod 2^logM = p2Pow 1`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkSep)

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem callTrX (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hkc : 4608 ≤ kc) (hpre : Pre R kc b L st pw pl ws lm x xl s)
    (kT : JT impl R kc b L st pw pl ws lm x xl s)
    {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 xc : Nat}
    (hrs : RS0 R kc L st pw pl lm x xl s (natVal s.mem x xl) bp M L1 b1 1) (hb : b ≤ b1)
    (S' : State) (hpc : S'.rip = BitVec.ofNat 64 6188320) (hfr : Frm s S' 184) (hm : S'.mem = M)
    (hra : M.readLE ((s.regs 4).toNat - 184) 8 = pcT)
    (h0 : S'.regs 0 = BitVec.ofNat 64 (bp + 8 * (1 * W lm))) (h3 : S'.regs 3 = BitVec.ofNat 64 (W lm))
    (h1 : S'.regs 1 = BitVec.ofNat 64 (2 * W lm)) (h7 : S'.regs 7 = BitVec.ofNat 64 x)
    (h6 : S'.regs 6 = BitVec.ofNat 64 xl) (h8 : S'.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S'.regs 9 = BitVec.ofNat 64 lm) :
    ReachesRet (LibW.program.link impl) (retAddrOf s) S' (GoalQ R kc b L st pw pl lm x xl s) := by
  have hf := pf_of hpre (by omega)
  have hR64 := (s.regs 4).isLt
  have hK := hf.w.sp
  simp only [K] at hK
  obtain ⟨hsp, h5, h14, hfs, hx15, hdf⟩ := hfr
  have hspN : (S'.regs 4).toNat = (s.regs 4).toNat - 184 := by rw [hsp]; exact tN (by omega)
  have hadd8 : BitVec.ofNat 64 ((s.regs 4).toNat - 184) + 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 176) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  obtain ⟨-, hsv, -, -, -, -, hlm, -, -, -, -, -, -, -, -, -, ⟨hx40, -, hx48, -, hxw⟩, -, hxl, -, -, -, -, hcost, -,
    -, -, -, hx15s, hdfs⟩ := id hpre
  have hc := hrs.c
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := 1) (by omega)
  have hz := bufArr hpre hc hf hspN h14 hfs hm hkT haT (a := bp + 8 * (1 * W lm)) (c := 2 * W lm) (by omega) hin
    (by omega) (by have := hc.scr.al; omega) (by omega)
  obtain ⟨xv, xn, xacc, xh, xap⟩ := x_ctx hpre hc
  have hmk : makeCost (truncNeed xl lm) ≤ tC lm :=
    makeCost_le (b := W lm + 4) (by simp only [truncNeed, W]; omega) (by omega)
  have hroom : tC lm ≤ b1 := by
    have h2 : tC lm ≤ b := Nat.le_trans (Nat.le_add_right _ _) hcost
    omega
  have hrdin : RdIn R L1 S' stkT aboveT x xl := by
    refine ⟨by omega, by rw [hm]; exact xacc, hx48, xh, ?_⟩
    simp only [win, K, A, outside_cons, outside_nil, and_true] at hxw ⊢
    rw [hspN]; omega

  refine truncCallP hap hns htr (b := b1 + stkR (HP (stLen s.mem st) pl lm) M st) (L := L1) (xc := xc)
    (ra_bp hap hnf 0x31b (by decide)) hpc (by rw [hspN, hm]; exact hra) h0 h3 h1 h7 h6 h8 h9
    (by rw [hx15, hx15s]) (by rw [hdf, hdfs]) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨callEnv_ctx hpre hc hspN h14 hfs hm hkT haT, hsv, by omega, hz.1, hrdin, by omega, by omega,
      Or.inr fun _ h => by have := xap h; unfold Apart at this ⊢; omega,
      by omega, by rw [hm, h14]; exact hc.inv⟩ (Or.inl (by rw [hm]; exact xn)) (Or.inr (Or.inl (by omega)))
    fun s' hpc' hsp' h5' h14' hx15' hrg hpost => ?_
  obtain ⟨hfs', hdf', p', l', c', e0, e3, e1, L', b', ⟨hv', hn', -, -, -, hre, -⟩, -, ⟨hLE, hbud', hinv'⟩, hF',
    hLF'⟩ := hpost
  obtain ⟨rfl, rfl⟩ := hre (by simp only [truncNeed, W]; omega)
  rw [hm] at hF' hLF' hrg hv'
  rw [h14] at hinv'
  have hws : ∀ r ∈ [(bp + 8 * (1 * W lm), bp + 8 * (1 * W lm) + 8 * (2 * W lm))], WOK R L s st r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact wok_buf hc.scr (by omega) hin
  have hhdr : ∀ c n, st ≤ c → c + n ≤ st + 24 → s'.mem.readLE c n = M.readLE c n := fun c n e1 e2 => by
    have hd := hf.w.hd
    simp only [win, K, A, outside_cons, outside_nil, and_true] at hd
    have hs1 := hc.sap.1
    unfold Apart at hs1
    refine rd_keep hf.w hspN hkT haT hF' hLF' (hc.sa.1.2.1.sub e1 e2) (by simp only [K, A]; omega)
      fun r hr hr' => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only at hr' ⊢
    simp only [NB] at hs1 hin
    omega
  have hsah := sa_hdr' hc.ain hc.bu hc.sa hc.sap hLE hhdr hF'.accessible
  obtain ⟨b2, hinv2, hbud2⟩ := effL (r' := stkR (HP (stLen s.mem st) pl lm) s'.mem st) hinv' hbud' (by omega)
    (stkR_congr (hhdr _ _ (by omega) (by omega)))
  have hc2 := keepC hc hf.w hspN hkT haT hws hF' hLF' hrg hLE hinv2 hsah.1 hsah.2.1 hsah.2.2.1 hsah.2.2.2
  have hrs2 := rs0_call hrs hf (pw_sep_stk hpre) hspN hkT haT (fun r hr => List.mem_append_left _ hr) hws
    (Nat.le_refl _) (by omega) hF' hLF' hc2
  have hlW : l' ≤ W lm := len_le_w hn' (by rw [hv']; exact Nat.mod_lt _ (Nat.two_pow_pos _))
  have hsp2 : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 176) := by
    rw [hsp', hsp]; exact hadd8
  refine kT s' bp L' b2 l' hpre hpc' ⟨hsp2, h5'.trans h5, h14'.trans h14, hfs'.trans hfs, hx15'.trans hx15,
    hdf'.trans hdf⟩ e0 e3 e1 hrs2 hlW (hv'.trans (by rw [xv, PV, p2_one])) hn' ?_
  omega

end

end FvModexp.Amd64.P2Pre
