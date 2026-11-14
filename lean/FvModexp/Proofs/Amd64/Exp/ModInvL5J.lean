import FvModexp.Proofs.Amd64.Exp.ModInvL5

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): `S5 → J2` at the next round (agent infra s58; twin of
`Arm64/Exp/ModInvL5`'s `retL5` / `contL5` / `segL5`)

`retL5`: after `subMod2N` returns (`0x5ead65`), `runL5b` and the loop head at `j + 1`; `contL5`: the value / length /
budget facts (small context); `segL5`: `runL5a`, the round facts at `subMod2N`'s entry memory, `callSub`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem cost_mono {e n : Nat} (h : e ≤ n) : SubMod2N.cost e ≤ SubMod2N.cost n := by
  simp only [SubMod2N.cost, SubMod2N.wCost, SubMod2N.W, allocCost]; omega

theorem zB_succ (n : Nat) {j : Nat} (hj : 1 ≤ j) : zB n (j + 1) = 2 ^ j := by
  simp only [zB, if_neg (show ¬ j + 1 = 1 by omega), Nat.add_sub_cancel]

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `subMod2N` returns (`0x5ead65`): reload, the loop head at `j + 1` -/
theorem retL5 {j : Nat} (kJ : J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s (j + 1))
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 : Nat} (s' : State)
    (hmid : Mid R kc L s zp zc st xp xl xc n s'.mem L1 b1 p l c q ql qc)
    (hj1 : 1 ≤ j) (hjlt : 2 ^ j < NW n) (hl : l ≤ 2 ^ j)
    (hb : b - spent sqrC mulC xl n (j + 1) + stkR H s'.mem st ≤ b1)
    (hcong : natVal s.mem xp xl * natVal s'.mem p l % 2 ^ (2 ^ (j + 1) * 32) = 1 % 2 ^ (2 ^ (j + 1) * 32))
    (hi : s'.mem.readLE ((s.regs 4).toNat - 72) 8 = 2 ^ (j + 1)) (hqs : QS s s'.mem q ql qc)
    (hpc : s'.rip = BitVec.ofNat 64 6204773) (hsp : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224))
    (h5 : s'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8)) (habi : Abi s s')
    (h0 : s'.regs 0 = BitVec.ofNat 64 p) (h3 : s'.regs 3 = BitVec.ofNat 64 l) (h1 : s'.regs 1 = BitVec.ofNat 64 c) :
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s s' := by
  have hK := sp_K hpre
  obtain ⟨-, hsp2, hw⟩ := hpre.1.2.1
  simp only [regSP, K, A] at hsp2 hw
  have hacc : s'.mem.accessible ((s.regs 4).toNat - 232) (232 + 72) true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hfw := hmid.1
  obtain ⟨-, f32, f40, f48, f56, f64, f104⟩ := hfw
  have sp' : ∀ d, (s.regs 4).toNat - 224 + (224 + d) = (s.regs 4).toNat + d := fun d => by omega
  obtain ⟨q1, q2, q3⟩ := hqs
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  unfold Goal
  refine runL5b impl _ _ (s.regs 4).toNat st xp xl xc n (2 ^ (j + 1)) q ql qc (NW n) (by omega) (by omega) s' hpc
    hsp hacc (by rw [sp' 40]; exact f40) (by rw [sp' 32]; exact f32) (by rw [sp' 48]; exact f48)
    (by rw [sp' 56]; exact f56) (by rw [sp' 64]; exact f64)
    (by rw [show (s.regs 4).toNat - 224 + 152 = (s.regs 4).toNat - 72 by omega]; exact hi)
    (by rw [show (s.regs 4).toNat - 224 + 104 = (s.regs 4).toNat - 120 by omega]; exact q2)
    (by rw [show (s.regs 4).toNat - 224 + 112 = (s.regs 4).toNat - 112 by omega]; exact q3)
    (by rw [show (s.regs 4).toNat - 224 + 200 = (s.regs 4).toNat - 24 by omega]; exact q1)
    (by rw [show (s.regs 4).toNat - 224 + 120 = (s.regs 4).toNat - 104 by omega]; exact f104) ?_
  intro S e0 e4 e5 e14 efs ex edf r12 r0 r2 r1 r15 r13 r11 r3 r7 r6 r8 r9 r10 em
  obtain ⟨hfw', hrt, hz, hzz, hap, hlc, hqlc, hnc, hqc⟩ := hmid
  rw [← em] at hfw' hrt hz hzz hb hcong
  exact kJ S p l c q ql qc L1 b1 hpre hn e0 (e4.trans hsp) (e5.trans h5)
    ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩ r12 (r0.trans h0) (r2.trans h3) (r1.trans h1)
    r15 r13 r11 r3 r7 r6 r8 r9 r10 hfw' hrt hb hz hzz hnc (by rw [zB_succ n hj1]; exact hl) hlc hqlc hqc
    (by omega) (by simpa using hjlt) hap hcong

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the continuation after `subMod2N` (small context): value / length / budget facts, then `retL5` -/
theorem contL5 {J : Nat} {j : Nat} (kJ : J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s (J + 1))
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {M : Memory} {p l c q ql qc Zv b1 : Nat}
    (hj1 : 1 ≤ j) (hex : ExL3 s n J j M) (hqs : QS s M q ql qc)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hv : natVal M p l = Zv * 2)
    (hvq : natVal M q ql = Zv * Zv % 2 ^ eL j * natVal s.mem xp (min (kL j) xl) % 2 ^ eL j)
    (hb : b - spent sqrC mulC xl n j - P5 sqrC mulC xl n j (2 ^ j) + stkR H M st ≤ b1)
    (hbud : spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (2 ^ j) ≤ b)
    (hcm : SubMod2N.cost (2 ^ j * 64) ≤ SubMod2N.cost n)
    (s' : State) (l' : Nat) (L' : List (Nat × Nat)) (b' : Nat) (f0 : s'.rip = BitVec.ofNat 64 6204773)
    (f1 : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224)) (f2 : s'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8))
    (habi : Abi s s')
    (g0 : s'.regs 0 = BitVec.ofNat 64 p) (g1 : s'.regs 3 = BitVec.ofNat 64 l') (g2 : s'.regs 1 = BitVec.ofNat 64 c)
    (mid2 : Mid R kc L s zp zc st xp xl xc n s'.mem L' b' p l' c q ql qc)
    (hv' : natVal s'.mem p l' = Exp.subMod2N (natVal M p l) (natVal M q ql) (2 ^ j * 64))
    (hn' : NatNorm s'.mem p l') (hbud' : b1 - SubMod2N.cost (2 ^ j * 64) ≤ b') (hsl : SlotsKept s M s'.mem)
    (hcap : stCap s'.mem st = stCap M st) :
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s s' := by
  have hK : 232 + kc ≤ (s.regs 4).toNat := sp_K hpre
  have hsp0 : 232 ≤ (s.regs 4).toNat := by omega
  have hex1 := hex.1
  obtain ⟨-, -, hjlt, hJ⟩ := hex
  subst hJ
  have hcong' := round_step hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hcong
  simp only [eL, kL] at hvq
  rw [← hv, ← hvq, ← hv'] at hcong'
  have hvj : natVal s'.mem p l' < 2 ^ (64 * 2 ^ j) := by
    rw [hv', show 64 * 2 ^ j = 2 ^ j * 64 by omega]; exact (Exp.subMod2N_spec _ _ _).1
  refine retL5 kJ hpre hn s' mid2 hj1 hjlt (len_le hn' hvj) ?_ hcong'
    (slot_keep hsl hsp0 (by decide) (by decide) hex1) (qs_keep hsl hsp0 hqs) f0 f1 f2 habi g0 g1 g2
  rw [spent_succ _ _ _ _ _ hj1, stkR_congr hcap]; simp only [roundCost, P5, P4, P3, P2, P1] at hb hbud ⊢; omega


set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segL5 {J : Nat} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains SubMod2N.fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    (hkc : SubMod2N.K ≤ kc) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (kJ : J2j impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s (J + 1)) :
    S5 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6204729 (ExL3 s n J) eL kL := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hqs h0 h3 h1 hv hnz hl hvq hnq hql hb
  have hrc' := hrc
  obtain ⟨⟨hpre⟩, hn, h4, h5, habi, ⟨hmid⟩, hj1, hjn, hbud, hcong⟩ := hrc'
  have hK : 232 + kc ≤ (s.regs 4).toNat := sp_K hpre
  obtain ⟨-, hsp2, hw⟩ := hpre.1.2.1
  simp only [regSP, K, A] at hsp2 hw
  have hacc : S.mem.accessible ((s.regs 4).toNat - 232) 232 true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hex' := hex
  obtain ⟨hi, hi64, hr, hJ⟩ := hex'
  have hen : 2 ^ j * 64 ≤ n := by simp only [NW] at hr; omega
  have hcm := cost_mono hen
  have hbo : SubMod2N.cost (2 ^ j * 64) ≤ b1 :=
    bud_okP hb hbud (m := SubMod2N.cost n) (by simp only [roundCost, P5, P4, P3, P2, P1]; omega) hcm
  have hqs' := hqs
  obtain ⟨q1, q2, q3⟩ := hqs'
  have hK' := contL5 (c := c) kJ hpre hn hj1 hex hqs hcong hv hvq hb hbud hcm
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  refine runL5a impl _ _ (s.regs 4).toNat (2 ^ j * 64) p l c q ql qc (by omega) (by omega) (by omega) S hpc h4 hacc
    (by rw [show (s.regs 4).toNat - 224 + 168 = (s.regs 4).toNat - 56 by omega]; exact hi64)
    (by rw [show (s.regs 4).toNat - 224 + 200 = (s.regs 4).toNat - 24 by omega]; exact q1)
    (by rw [show (s.regs 4).toNat - 224 + 104 = (s.regs 4).toNat - 120 by omega]; exact q2)
    (by rw [show (s.regs 4).toNat - 224 + 112 = (s.regs 4).toNat - 112 by omega]; exact q3) h0 h3 h1 ?_
  intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 r10 r11 em
  obtain ⟨m1, v1, w1, n1, n1', c1⟩ := mid_st hpre hmid (a := (s.regs 4).toNat - 224) (2 ^ j * 64) (by omega)
    (by omega)
  obtain ⟨m2, v2, w2, n2, n2', c2⟩ := mid_st hpre m1 (a := (s.regs 4).toNat - 224 - 8) 6204773 (by omega) (by omega)
  rw [← em] at m2 v2 w2 n2 n2' c2
  have ex2 : ExL3 s n J j S'.mem := by
    rw [em]; exact ⟨(slot_other (by omega)).trans ((slot_other (by omega)).trans hi),
      (slot_other (by omega)).trans ((slot_other (by omega)).trans hi64), hr, hJ⟩
  have qs2 : QS s S'.mem q ql qc := by
    rw [em]; exact qs_store _ (qs_store _ hqs (by omega) (by omega)) (by omega) (by omega)
  have rd : S'.mem.readLE (S'.regs 4).toNat 8 = 6204773 := by
    rw [e4, toNat_232 (by omega) (by omega), em, slot_self (by decide)]
  have rn : S'.mem.readLE ((S'.regs 4).toNat + 8) 8 = 2 ^ j * 64 := by
    rw [e4, toNat_232 (by omega) (by omega), sp8 (by omega), em, slot_other (by omega), slot_self (by omega)]
  refine callSub hap hns hnf hkT haT htr hsub hadd hgr hkc hpre hx0 hdf0 m2 (e := 2 ^ j * 64)
    (by have := Nat.one_le_two_pow (n := j); omega) hen hl hql (n2 (n1 hnz)) (n2' (n1' hnq)) hbo (by decide) e4
    (e5.trans h5) ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩ e0 rd rn r0 r3 r1 r7 r6 r8 r9 r10 r11 ?_
  intro s' l' L' b' f0 f1 f2 habi' g0 g1 g2 mid2 hv' hn' _ _ hbud' hsl hcap
  rw [v2, v1, w2, w1] at hv'
  rw [c2, c1] at hcap
  refine hK' s' l' L' b' f0 f1 f2 habi' g0 g1 g2 mid2 hv' hn' hbud' ?_ hcap
  intro a h1 h2
  rw [hsl a h1 h2, em, slot_other (by omega), slot_other (by omega)]

end

end FvModexp.Amd64.ModInv
