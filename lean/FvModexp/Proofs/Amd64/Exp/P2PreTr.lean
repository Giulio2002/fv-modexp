import FvModexp.Proofs.Amd64.Exp.P2PreRS

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): a loop `z = z.trunc(z, logM)` call (nat.go:893 / :896) → `JX` (agent
divmc s65; twin of infra's `Arm64/Exp/P2PreTr`)

`callTr`: at the `nat.trunc` entry (calls `+0x460`, `+0x54f`; return `0x5e8900 + pcR`) with `z = x = powers[k]`
(`k = kf i`, `(bp + 8 k w, l, 2 w)`, `l ≤ 2 w`, value `v`), `n = logM`: the callee precondition from `RS` and `Pre`, and
the continuation into the join `JX … pcR kf vT (W lm) cstT i` (the result reuses `z`; its length is at most `w`; its
value is `v mod 2^logM`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkSep)

/-- a round step's costs fit in what is left at round `i` -/
theorem bud_room2 {c0 r pl i b b1 cs t : Nat} (hc : c0 + (pl / 2 - 1) * r ≤ b) (hi : i + 2 ≤ pl) (h2 : 2 ≤ i)
    (hi2 : i % 2 = 0) (hb : b - (c0 + (i / 2 - 1) * r + cs) ≤ b1) (ht : cs + t ≤ r) : t ≤ b1 := by
  have : (i / 2 - 1) * r + r ≤ (pl / 2 - 1) * r := by
    have := Nat.mul_le_mul_right r (show i / 2 - 1 + 1 ≤ pl / 2 - 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  omega

/-- **`RS` through a step that keeps the reads of `powers`, `buf` and the frame** -/
theorem rs_rd {R : RtInv} {kc : Nat} {L : List (Nat × Nat)} {st pw pl lm x xl : Nat} {s : State} {X bp : Nat}
    {M0 M : Memory} {L1 L2 : List (Nat × Nat)} {b1 b2 i k : Nat} (h : RS R kc L st pw pl lm x xl s X bp M0 L1 b1 i k)
    (hc' : Ctx R kc L st pw pl lm x xl s bp M L2 b2) (hk : k ≤ pl) (hR : 184 ≤ (s.regs 4).toNat)
    (hrd : ∀ a n, 0 < n → RdR s pw pl lm bp a n → M.readLE a n = M0.readLE a n) :
    RS R kc L st pw pl lm x xl s X bp M L2 b2 i k ∧ KeepB bp (NB pl lm) M0 M := by
  obtain ⟨h0, hkb⟩ := rs0_of_rdr h.to0 hc' hk hrd
  refine ⟨⟨h0.c, h0.d, h0.t, ?_, ?_⟩, hkb⟩
  · exact (hrd _ 8 (by decide) (Or.inr (Or.inr ⟨by omega, by omega⟩))).trans h.lo.1
  · exact (hrd _ 8 (by decide) (Or.inr (Or.inr ⟨by omega, by omega⟩))).trans h.lo.2

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem callTr (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hkc : 4608 ≤ kc) (hpre : Pre R kc b L st pw pl ws lm x xl s) {i pcR : Nat} (hpcR : pcR < 0x68a)
    {kf vT : Nat → Nat} {cstS cstT : Nat}
    (kT : JX impl R kc b L st pw pl ws lm x xl s (0x5e8900 + pcR) kf vT (W lm) cstT i)
    (hk1 : i ≤ kf i) (hk2 : kf i ≤ i + 1) (hcst : cstT = cstS + tC lm) (hct : cstT ≤ rc lm)
    {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 l v : Nat}
    (hrs : RS R kc L st pw pl lm x xl s (natVal s.mem x xl) bp M L1 b1 i (kf i))
    (hi2 : i % 2 = 0) (hi : 2 ≤ i) (hip : i + 2 ≤ pl) (hb : b - (tC lm + (i / 2 - 1) * rc lm + cstS) ≤ b1)
    (hl : l ≤ 2 * W lm) (hnorm : NatNorm M (bp + 8 * (kf i * W lm)) l)
    (hv : natVal M (bp + 8 * (kf i * W lm)) l = v) (hvT : vT i = v % 2 ^ lm)
    (S' : State) (hpc : S'.rip = BitVec.ofNat 64 6188320) (hfr : Frm s S' 184)
    (hm : S'.mem = M.writeLE ((s.regs 4).toNat - 176 - 8) 8 (0x5e8900 + pcR))
    (h0 : S'.regs 0 = BitVec.ofNat 64 (bp + 8 * (kf i * W lm))) (h3 : S'.regs 3 = BitVec.ofNat 64 l)
    (h1 : S'.regs 1 = BitVec.ofNat 64 (2 * W lm)) (h7 : S'.regs 7 = BitVec.ofNat 64 (bp + 8 * (kf i * W lm)))
    (h6 : S'.regs 6 = BitVec.ofNat 64 l) (h8 : S'.regs 8 = BitVec.ofNat 64 (2 * W lm))
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
  obtain ⟨-, hsv, -, -, -, -, hlm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcost, -, -, -, -, hx15s,
    hdfs⟩ := id hpre
  have hin := pw_in (pl := pl) (lm := lm) (bp := bp) (j := kf i) (by omega)
  have hboF : bp + 8 * NB pl lm ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ bp := by
    have := wok_win (wok_buf (zp := bp) (zn := 8 * NB pl lm) hrs.c.scr (Nat.le_refl _) (Nat.le_refl _)) hf.w
      (by have := nb_pos (pl := pl) (lm := lm) (by omega) hw1; simp only; omega)
    simp only [K, A] at this; omega
  obtain ⟨ev0, en0⟩ := nat_keepB (M := M) (M' := S'.mem) (bp := bp) (nb := NB pl lm)
    (fun c n h0 h1 h2 => by rw [hm]; exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega))
    (p := bp + 8 * (kf i * W lm)) (l := l) (by omega) (by omega)
  have hrs' := rs_own hpre hkc hrs (by omega) (0x5e8900 + pcR) (a0 := (s.regs 4).toNat - 176 - 8) (by omega)
    (by omega)
  rw [← hm] at hrs'
  have hc := hrs'.c
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hz := bufArr hpre hc hf hspN h14 hfs rfl hkT haT (a := bp + 8 * (kf i * W lm)) (c := 2 * W lm) (by omega)
    hin (by omega) (by have := hc.scr.al; omega) (by omega)
  have hmk : makeCost (truncNeed l lm) ≤ tC lm :=
    makeCost_le (b := W lm + 4) (by simp only [truncNeed, W]; omega) (by omega)
  have hroom : tC lm ≤ b1 := bud_room2 hcost hip hi hi2 hb (by rw [← hcst]; exact hct)
  have hra : S'.mem.readLE (S'.regs 4).toNat 8 = 0x5e8900 + pcR := by
    rw [hspN, hm, (show (s.regs 4).toNat - 184 = (s.regs 4).toNat - 176 - 8 by omega),
      Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  refine truncCallP hap hns htr (b := b1 + stkR (HP (stLen s.mem st) pl lm) S'.mem st) (L := L1)
    (xc := 2 * W lm) (ra_bp hap hnf pcR hpcR) hpc hra h0 h3 h1 h7 h6 h8 h9
    (by rw [hx15, hx15s]) (by rw [hdf, hdfs]) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨callEnv_ctx hpre hc hspN h14 hfs rfl hkT haT, hsv, hl, hz.1, hz.2 l hl, by omega, by omega, Or.inl rfl,
      by omega, by rw [h14]; exact hc.inv⟩ (Or.inl (en0 hnorm)) (Or.inl rfl)
    fun s' hpc' hsp' h5' h14' hx15' hrg hpost => ?_
  obtain ⟨hfs', hdf', p', l', c', e0, e3, e1, L', b', ⟨hv', hn', -, -, -, hre, -⟩, -, ⟨hLE, hbud', hinv'⟩, hF',
    hLF'⟩ := hpost
  obtain ⟨rfl, rfl⟩ := hre (by simp only [truncNeed, W]; omega)
  rw [h14] at hinv'
  have hws : ∀ r ∈ [(bp + 8 * (kf i * W lm), bp + 8 * (kf i * W lm) + 8 * (2 * W lm))], WOK R L s st r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact wok_buf hc.scr (by omega) hin
  have hhdr : ∀ c n, st ≤ c → c + n ≤ st + 24 → s'.mem.readLE c n = S'.mem.readLE c n := fun c n e1 e2 => by
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
  have hrs2 := rs_call hrs' hf (pw_sep_stk hpre) hspN hkT haT (fun r hr => List.mem_append_left _ hr) hws
    (Nat.le_refl _) (by omega) hF' hLF' hc2
  have hlW : l' ≤ W lm := len_le_w hn' (by rw [hv']; exact Nat.mod_lt _ (Nat.two_pow_pos _))
  have hsp2 : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 176) := by
    rw [hsp', hsp]; exact hadd8
  refine kT s' bp L' b2 l' hpre hpc' ⟨hsp2, h5'.trans h5, h14'.trans h14, hfs'.trans hfs, hx15'.trans hx15,
    hdf'.trans hdf⟩ e0 e3 e1 hrs2 hlW (hv'.trans (by rw [ev0, hv, hvT])) hn' hi2 hi hip ?_
  rw [hcst]
  omega

end

end FvModexp.Amd64.P2Pre
