import FvModexp.Proofs.Amd64.Exp.P2W2AT
import FvModexp.Proofs.Amd64.Exp.P2W2Ent
import FvModexp.Proofs.Amd64.Exp.P2W2N
import FvModexp.Proofs.Amd64.Exp.P2W2PC

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): from the entry to the return of the table call (agent divmc s68; amd64 twin of
agent infra's `Arm64.P2W2EP`)

`entP` = `ent` (prologue, `stk.reserve(8w)`) ∘ `wc_rs` ∘ `segN` (`zz = stk.nat(2w)`, `powers` zeroed) ∘ `segPC`
(`buildPrecomputationWindowModPower2`); the continuation gets `AT` at `ppRetC` and the budget `b - cost0`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

/-- the continuation at the table's return -/
@[reducible] def KAT (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State) (ret0 : W64) (Q : State → Prop) : Prop :=
  ∀ (s' : State) (L3 : List (Nat × Nat)) (b3 zzp tp : Nat), s'.rip = BitVec.ofNat 64 ppRetC →
    s'.regs 4 = BitVec.ofNat 64 sp → s'.regs 14 = BitVec.ofNat 64 g → s'.xmm 15 = 0 → s'.fsBase.toNat = fs →
    s'.df = false → AT R L K g sp st bp r zp zc xp xl xc yp yl lm s s'.mem L3 b3 zzp tp →
    b - cost0 lm ≤ b3 → ReachesRet (LibW.program.link impl) ret0 s' Q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **from the entry to the table's return** -/
theorem entP {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains fn = false) (hnfP : ns.contains P2Pre.fn = false)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) grE 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (LibW.program.link impl) mcE 4096 R)
    (hmv : MemmoveLive64 (LibW.program.link impl) P2Pre.mvE 4096 R)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 0x58)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (ret0 : W64) (Q : State → Prop)
    {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hX : EX xp xl s) (hKk : P2Pre.K kc ≤ K)
    (hbud : cost0 lm ≤ b) {zl : Nat} (hzl : zl < 2 ^ 64)
    (hpc : s.rip = BitVec.ofNat 64 fnE)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h3 : s.regs 3 = BitVec.ofNat 64 zl) (h1 : s.regs 1 = BitVec.ofNat 64 zc)
    (h7 : s.regs 7 = BitVec.ofNat 64 st) (h6 : s.regs 6 = BitVec.ofNat 64 xp) (h8 : s.regs 8 = BitVec.ofNat 64 xl)
    (h9 : s.regs 9 = BitVec.ofNat 64 xc) (h10 : s.regs 10 = BitVec.ofNat 64 lm)
    (KA : KAT impl R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s ret0 Q) :
    ReachesRet (LibW.program.link impl) ret0 s Q := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hfs0 : s.fsBase.toNat = fs := hP.1.2.2.1
  have hdf0 : s.df = false := hP.1.2.2.2.2.1
  have hlm2 : 2 ≤ lm := hP.2.2.2.2.1
  have hlm : lm ≤ 2 ^ 13 := hP.2.2.2.2.2.1
  have hl16 : stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 :=
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - 8 - K) (K + 0x238) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hW1 : 1 ≤ W lm := by simp only [W]; omega
  have hkK' : 184 + kc ≤ K := hKk
  refine ent hgr hmc hwb hP hzl hpc h0 h3 h1 h7 h6 h8 h9 h10 ?_
  intro M L1 b1 hFc hFf hLF hrg hx hkf hlen hlc hc40 hnl hmem hsl hb1 hinv S hpcS hspS h7S h3S h14S hfsS hx15S
    hdfS hmS
  have hw := wc_rs hP hFf hLF hrg hx hkf hlen hlc hc40 hnl hmem hinv
  have hB1 : LibCalls.Hide (b ≤ b1) := ⟨hb1⟩
  clear hb1 hFc hFf hLF hx hkf hlc hc40 hnl hmem hinv
  refine segN hap hns hnf hsn (by omega) haN hP hw (by omega) (by simp only [HW, StackNat.rnd]; omega)
    (by omega) hsl S hpcS hspS h7S h3S h14S (by rw [hfsS]; exact hfs0) hx15S (hdfS.trans hdf0) hmS ?_
  intro M2 L2 b2 hb2 hw2 hzs hsl2 S2 d_rip d4 d0 d3 d1 d7 d6 d8 d9 d10 d11 d14 dfs dx15 ddf hFS2 hrgS2 hra q118
    q68 q70
  have hw3 := hw2.win hP hFS2 hrgS2 (nseg_ws sp K (by omega))
  have hB2 : LibCalls.Hide (b1 ≤ b2) := ⟨hb2⟩
  clear hb2
  have hbu1 := (zz_post hw2.sok hw2.len (n := 2 * W lm) (by omega)
    (r := BitVec.ofNat 64 (stW M2 st + 8 * (stLen s.mem st + 8 * W lm))) rfl).2
  have hNW := hdr_nseg hstw (by omega)
  have hhd2 : ∀ a k, st ≤ a → a + k ≤ st + 24 → S2.mem.readLE a k = M2.readLE a k := fun a k q1 q2 =>
    hFS2.readLE a k (hNW.of_sub q1 q2)
  have hbu2 : P2Pre.BU S2.mem st (stW M2 st + 8 * (stLen s.mem st + 8 * W lm)) (8 * (2 * W lm)) :=
    P2Pre.bu_hdr hbu1 (hhd2 _ _ (Nat.le_refl _) (by omega)) (hhd2 _ _ (by omega) (by omega))
      (hhd2 _ _ (by omega) (by omega))
  refine segPC hap hns hnfP hmv hwb hkc hsn hkN (by omega) hsq hkS1 hkS hml hkM1 hkM htr hkT haT ret0 Q hP hX hw3
    hKk (Nat.le_trans hbud (Nat.le_trans hB1.h hB2.h)) rfl S2 d_rip d4 d14 dfs dx15 ddf rfl d0 d3 d1 d7 d6 d8 d9
    d10 d11 hra ?_
  intro s'' L3 b3 tp e0 e4 e14 e5 ex15 efs edf hw4 hb3 hpw hbs hbbu hkf3 hx3 hscr3 hF3
  have hlc3 := hw3.sok.2.2.2.2.2.1
  have hl3 := hw3.len
  have hl4 := hw4.len
  have hwo := hw3.win_out hP (by simp only [StackNat.rnd]; omega)
  have k3 : ∀ a k, sp + 0x57 ≤ a → a + k ≤ sp + 0x230 → Outside a k [(sp + 0x140, sp + 0x1a0)] →
      s''.mem.readLE a k = S2.mem.readLE a k := by
    intro a k q1 q2 q4
    refine hF3.readLE a k ?_
    have := hwo a k (by omega) q2
    rw [outside_append] at this; rw [outside_append, outside_append]
    refine ⟨⟨this.1, ?_⟩, this.2⟩
    simp only [P2Pre.K, outside_cons, outside_nil, and_true] at q4 ⊢; omega
  have hsl3 : ESl s''.mem sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st) :=
    ESl.keep (ESl.keep hsl2 fun a k ha => hFS2.readLE a k (slot_n ha))
      fun a k ha => k3 a k (slot_in ha).1 (slot_in ha).2 (slot_pw ha)
  have hzr : ∀ o, o = 0x118 ∨ o = 0x68 ∨ o = 0x70 → s''.mem.readLE (sp + o) 8 = S2.mem.readLE (sp + o) 8 := by
    intro o ho
    refine k3 _ _ (by omega) (by omega) ?_; simp only [outside_cons, outside_nil, and_true]; omega
  have hzh : Held R L2 (stW M2 st + 8 * (stLen s.mem st + 8 * W lm)) (8 * (2 * W lm)) := hzs.held
  refine KA s'' L3 b3 (stW M2 st + 8 * (stLen s.mem st + 8 * W lm)) tp e0 e4 e14 ex15
    (by rw [efs]; exact dfs) edf ⟨hw4, hsl3, ?_, ?_, ?_,
      Scr.mono (Scr.mono hzs hFS2.accessible (LiveExt.refl R L2)) hF3.accessible hx3,
      bu_after hbu2 hzh hkf3 (by rw [hl3, hl4]; omega), hpw, hbs, hbbu, scr_apart_bu hscr3 hbu2 hzh hlc3⟩
    (Nat.le_trans (Nat.sub_le_sub_right (Nat.le_trans hB1.h hB2.h) _) hb3)
  · rw [hzr 0x118 (Or.inl rfl), q118]
  · rw [hzr 0x68 (Or.inr (Or.inl rfl)), q68]
  · rw [hzr 0x70 (Or.inr (Or.inr rfl)), q70]

end FvModexp.Amd64.P2W2
