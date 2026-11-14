import FvModexp.Proofs.Amd64.Exp.ModInvF5

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the final round's `subMod2N` and the return (agent infra s58; twin of
`Arm64/Exp/ModInvF5`)

`post_mid` (the post from the round facts), `bud_final`, `retF5` (`0x5eaec5`: `ADDQ $0xd8, SP; POPQ BP; RET`),
`contF5` (value: `final_step`; budget), `segF5` (`runF5s`, the round facts at `subMod2N`'s entry, `callSub`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

section
variable {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the post from the round facts at the final memory -/
theorem post_mid (s' : State) {L' : List (Nat × Nat)} {b' p l c q ql qc : Nat}
    (mid : Mid R kc L s zp zc st xp xl xc n s'.mem L' b' p l c q ql qc)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (e0 : (s'.regs 0).toNat = p) (e1 : (s'.regs 3).toNat = l) (e2 : (s'.regs 1).toNat = c)
    (hv : natVal s'.mem p l = val (natVal s.mem xp xl) n) (hn : NatNorm s'.mem p l)
    (hb : b - cost sqrC mulC xl n + stkR H s'.mem st ≤ b') (hzh : Held R L zp (8 * zc)) :
    Post R kc H sqrC mulC b L zp zc st xp xl n s s' := by
  obtain ⟨-, ⟨-, hF, hLF, hLE, hinv, hstk, hlen, hstw, hain⟩, ⟨hc40, -, hlive, hold, -, -, -, -, -, hwa⟩, -, -, hlc,
    -⟩ := mid
  refine ⟨hfs, hdf, p, l, c, e0, e1, e2, hv, hn, hlc, hc40, L', b', hLE, hb, hinv, hlive, hold,
    ⟨⟨hstk, hlen, hstw⟩, hain⟩, hF, hLF, fun hc hnk => ?_⟩
  by_cases hz : p = zp ∧ c = zc
  · obtain ⟨rfl, rfl⟩ := hz
    rcases hstw with h | ⟨hIn, hAp⟩
    · exact absurd h hnk
    · have := fresh_apart hIn hAp hzh; unfold Apart at this ⊢; omega
  · exact hwa hz hc (ArrIn.cap hain hnk)

/-- the final budget (per-round sizes, Q reserve) -/
theorem bud_final {j b b1 b' : Nat} {M M' : Memory} (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n)
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hbud : spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (NW n) ≤ b)
    (hb : b - spent sqrC mulC xl n j - P5 sqrC mulC xl n j (NW n) + stkR H M st ≤ b1)
    (hbud' : b1 - SubMod2N.cost n ≤ b') (hcap : stCap M' st = stCap M st) :
    b - cost sqrC mulC xl n + stkR H M' st ≤ b' := by
  have hNW0 : NW n ≠ 0 := by have := Nat.two_pow_pos (j - 1); omega
  have hjl : j - 1 ≤ Nat.log2 (NW n) := (Nat.le_log2 hNW0).2 (Nat.le_of_lt hjn)
  have hm := sumR_mono sqrC mulC xl n hjl
  have hs := hsm _ _ (zB_le hjn)
  rw [stkR_congr hcap]
  simp only [spent, cost, roundCost, P5, P4, P3, P2, P1] at hb hbud ⊢
  omega

end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `subMod2N` returns (`0x5eaec5`): restore `RSP` / `RBP`, return -/
theorem retF5 {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat}
    {mulC : Nat → Nat → Nat} {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {p l c q ql qc : Nat}
    {L1 : List (Nat × Nat)} {b1 : Nat} (s' : State)
    (hmid : Mid R kc L s zp zc st xp xl xc n s'.mem L1 b1 p l c q ql qc)
    (hv : natVal s'.mem p l = val (natVal s.mem xp xl) n) (hn : NatNorm s'.mem p l)
    (hb : b - cost sqrC mulC xl n + stkR H s'.mem st ≤ b1)
    (hpc : s'.rip = BitVec.ofNat 64 6205125) (hsp : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224))
    (habi : Abi s s')
    (h0 : s'.regs 0 = BitVec.ofNat 64 p) (h3 : s'.regs 3 = BitVec.ofNat 64 l) (h1 : s'.regs 1 = BitVec.ofNat 64 c) :
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s s' := by
  have hK := sp_K hpre
  obtain ⟨-, hsp2, hw⟩ := hpre.1.2.1
  simp only [regSP, K, A] at hsp2 hw
  have hacc : s'.mem.accessible ((s.regs 4).toNat - 232) (232 + 72) true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hra := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hzh : Held R L zp (8 * zc) := (hpre.2.2.2.2.2.2.2.2.1.2.1 hpre.2.2.2.2.2.2.2.1).2.1
  have hp64 : p < 2 ^ 64 := hmid.2.2.1.2.1
  have hc40 : c < 2 ^ 40 := hmid.2.2.1.1
  have hlc : l ≤ c := hmid.2.2.2.2.2.1
  obtain ⟨f1, f2⟩ := hmid.1.1
  have f2' : s'.mem.readLE ((s.regs 4).toNat - 224 + 216) 8 = (s.regs 5).toNat := by
    rw [show (s.regs 4).toNat - 224 + 216 = (s.regs 4).toNat - 8 by omega]; exact f2
  have f1' : s'.mem.readLE ((s.regs 4).toNat - 224 + 224) 8 < 140737488355328 := by
    rw [show (s.regs 4).toNat - 224 + 224 = (s.regs 4).toNat by omega, f1]; exact hra
  have f1r : s'.mem.readLE ((s.regs 4).toNat - 224 + 224) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [show (s.regs 4).toNat - 224 + 224 = (s.regs 4).toNat by omega, f1]
  have hmB : Box (Mid R kc L s zp zc st xp xl xc n s'.mem L1 b1 p l c q ql qc) := ⟨hmid⟩
  clear hmid
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  unfold Goal
  janus64_run [f1r, f2', f1']
  refine ⟨?_, post_mid _ hmB.h ?_ ?_ ?_ ?_ ?_ hv hn hb hzh⟩
  · apply BitVec.eq_of_toNat_eq
    have := (s.regs 4).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  all_goals try janus64_simp
  all_goals first | exact afs | exact adf | exact a14 | exact ax15 | omega | skip

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}

set_option maxHeartbeats 64000000 in
/-- the continuation after `subMod2N` (small context): value and budget, then `retF5` -/
theorem contF5 {j : Nat} (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) (hn : 64 < n) {M : Memory}
    {p l c q ql Zv b1 : Nat} (hj1 : 1 ≤ j) (hjn : 2 ^ (j - 1) < NW n) (hex : ExF n j M)
    (hcong : natVal s.mem xp xl * Zv % 2 ^ (2 ^ j * 32) = 1 % 2 ^ (2 ^ j * 32))
    (hv : natVal M p l = Zv * 2)
    (hvq : natVal M q ql = Zv * Zv % 2 ^ eF n j * natVal s.mem xp (min (kF n j) xl) % 2 ^ eF n j)
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hbud : spent sqrC mulC xl n j + roundCost sqrC mulC xl n j (NW n) ≤ b)
    (hb : b - spent sqrC mulC xl n j - P5 sqrC mulC xl n j (NW n) + stkR H M st ≤ b1) {qc : Nat}
    (s' : State) (l' : Nat) (L' : List (Nat × Nat)) (b' : Nat) (f0 : s'.rip = BitVec.ofNat 64 6205125)
    (f1 : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224)) (habi : Abi s s')
    (g0 : s'.regs 0 = BitVec.ofNat 64 p) (g1 : s'.regs 3 = BitVec.ofNat 64 l') (g2 : s'.regs 1 = BitVec.ofNat 64 c)
    (mid2 : Mid R kc L s zp zc st xp xl xc n s'.mem L' b' p l' c q ql qc)
    (hv' : natVal s'.mem p l' = Exp.subMod2N (natVal M p l) (natVal M q ql) n)
    (hn' : NatNorm s'.mem p l') (hbud' : b1 - SubMod2N.cost n ≤ b') (hcap : stCap s'.mem st = stCap M st) :
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s s' := by
  simp only [eF, kF] at hvq
  have hval : natVal s'.mem p l' = val (natVal s.mem xp xl) n := by
    rw [hv', hv, hvq]
    exact final_step hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hn hex hcong
  exact retF5 hpre s' mid2 hval hn' (bud_final hj1 hjn hsm hbud hb hbud' hcap) f0 f1 habi g0 g1 g2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem segF5 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains SubMod2N.fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    (hkc : SubMod2N.K ≤ kc) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (hsm : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a') :
    S5 impl R kc H sqrC mulC b L zp zl zc st xp xl xc n s 6205081 (ExF n) (eF n) (kF n) := by
  intro S j p l c q ql qc L1 b1 Zv hrc hpc hex hqs h0 h3 h1 hv hnz hl hvq hnq hql hb
  have hrc' := hrc
  obtain ⟨⟨hpre⟩, hn, h4, h5, habi, ⟨hmid⟩, hj1, hjn, hbud, hcong⟩ := hrc'
  have hK : 232 + kc ≤ (s.regs 4).toNat := sp_K hpre
  obtain ⟨-, hsp2, hw⟩ := hpre.1.2.1
  simp only [regSP, K, A] at hsp2 hw
  have hacc : S.mem.accessible ((s.regs 4).toNat - 232) (232 + 72) true = true := by
    rw [hmid.2.1.2.1.accessible]
    exact Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hn2 : n ≤ 2 ^ 15 := hpre.2.2.2.2.1
  have hbo : SubMod2N.cost n ≤ b1 :=
    bud_okP hb hbud (m := SubMod2N.cost n) (by simp only [roundCost, P5, P4, P3, P2, P1]; omega) (Nat.le_refl _)
  have hqs' := hqs
  obtain ⟨q1, q2, q3⟩ := hqs'
  have hrn : S.mem.readLE ((s.regs 4).toNat - 224 + 288) 8 = n := by
    rw [show (s.regs 4).toNat - 224 + 288 = (s.regs 4).toNat + 64 by omega]; exact hmid.1.2.2.2.2.2.1
  have hK' := contF5 (impl := impl) (c := c) (qc := qc) hpre hn hj1 hjn hex hcong hv hvq hsm hbud hb
  obtain ⟨a14, afs, ax15, adf⟩ := habi
  refine runF5s impl _ _ (s.regs 4).toNat n p l c q ql qc (by omega) (by omega) (by omega) S hpc h4 hacc hrn
    (by rw [show (s.regs 4).toNat - 224 + 200 = (s.regs 4).toNat - 24 by omega]; exact q1)
    (by rw [show (s.regs 4).toNat - 224 + 104 = (s.regs 4).toNat - 120 by omega]; exact q2)
    (by rw [show (s.regs 4).toNat - 224 + 112 = (s.regs 4).toNat - 112 by omega]; exact q3) h0 h3 h1 ?_
  intro S' e0 e4 e5 e14 efs ex edf r0 r3 r1 r7 r6 r8 r9 r10 r11 em
  obtain ⟨m1, v1, w1, n1, n1', c1⟩ := mid_st hpre hmid (a := (s.regs 4).toNat - 224) n (by omega) (by omega)
  obtain ⟨m2, v2, w2, n2, n2', c2⟩ := mid_st hpre m1 (a := (s.regs 4).toNat - 224 - 8) 6205125 (by omega) (by omega)
  rw [← em] at m2 v2 w2 n2 n2' c2
  have rd : S'.mem.readLE (S'.regs 4).toNat 8 = 6205125 := by
    rw [e4, toNat_232 (by omega) (by omega), em, slot_self (by decide)]
  have rn : S'.mem.readLE ((S'.regs 4).toNat + 8) 8 = n := by
    rw [e4, toNat_232 (by omega) (by omega), sp8 (by omega), em, slot_other (by omega), slot_self (by omega)]
  refine callSub hap hns hnf hkT haT htr hsub hadd hgr hkc hpre hx0 hdf0 m2 (e := n) (by omega) (Nat.le_refl _) hl
    hql (n2 (n1 hnz)) (n2' (n1' hnq)) hbo (by decide) e4 (e5.trans h5)
    ⟨e14.trans a14, efs.trans afs, ex.trans ax15, edf.trans adf⟩ e0 rd rn r0 r3 r1 r7 r6 r8 r9 r10 r11 ?_
  intro s' l' L' b' f0 f1 f2 habi' g0 g1 g2 mid2 hv' hn' _ _ hbud' _ hcap
  rw [v2, v1, w2, w1] at hv'
  rw [c2, c1] at hcap
  exact hK' s' l' L' b' f0 f1 habi' g0 g1 g2 mid2 hv' hn' hbud' hcap

end

end FvModexp.Amd64.ModInv
