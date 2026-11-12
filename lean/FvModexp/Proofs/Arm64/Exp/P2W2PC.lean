import FvModexp.Proofs.Arm64.Exp.P2W2PP
import FvModexp.Proofs.Arm64.Exp.P2Pre

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the call of `buildPrecomputationWindowModPower2(stk, powers[:], 2, logM, x)`
(nat.go:1153; entry `1790928`, return `0x1b65f4 = 1795572`) (agent infra)

`segPC`: from the callee entry state `S2` (`ppre`'s precondition) through `P2Pre.full` to the return; the continuation
`KT` gets `WC` at the return memory (level `ℓ + rnd(5w)`), the table `powers[j] = X^j mod 2^logM` (`P2Pre.PwD`,
`j < 4`), `buf` as a scratch nat relative to the entry with `BU`, the stack array relative to the call (`ArrKF`), and
the callee's frame (for the slots).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.EvenHyp

/-- the continuation after the table -/
@[reducible] def KT (impl : List Segment) (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc : Nat) (m0 M : Memory)
    (L2 : List (Nat × Nat)) (kcP : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat) (b2 ℓ lm X : Nat)
    (r18 r29 : BitVec 64) (ret0 : BitVec 64) (Q : State → Prop) : Prop :=
  ∀ (s' : State) (L3 : List (Nat × Nat)) (b3 bp : Nat),
    s'.pc = BitVec.ofNat 64 1795572 → s'.sp = BitVec.ofNat 64 sp → s'.regs 28 = BitVec.ofNat 64 g →
    s'.regs 29 = r29 → s'.regs 18 = r18 →
    WC R L K g sp st zp zc m0 s'.mem L3 b3 (ℓ + StackNat.rnd (P2Pre.NB 4 lm)) →
    b2 - P2Pre.cost sqC mlC ℓ 4 lm ≤ b3 →
    (∀ j, j < 4 → P2Pre.PwD s'.mem (sp + 320) bp lm X j) →
    Scr R L L3 m0 s'.mem st bp (P2Pre.NB 4 lm) → P2Pre.BU s'.mem st bp (8 * P2Pre.NB 4 lm) →
    ArrKF R L2 st M s'.mem → LiveExt R L2 L3 → Scr R L2 L3 M s'.mem st bp (P2Pre.NB 4 lm) →
    MemFrame M s'.mem (R.rt ++ [(sp - (208 + kcP), sp - 8), (sp + 8, sp + 80), (sp + 320, sp + 416)] ++ stkWs M st) →
    ReachesRet (LibW.program.link impl) ret0 s' Q

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **the table call** -/
theorem segPC {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains P2Pre.fn = false)
    (hmv : MemmoveLive (LibW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (LibW.program.link impl) wbE 4096 R 2)
    {kcP : Nat} (hkc : 4608 ≤ kcP)
    {stkN aboveN : Nat} (hsn : StackNat.HypL impl R ns stkN aboveN) (hkN : stkN ≤ kcP) (haN : aboveN ≤ 88)
    {stkS aboveS : Nat} {sqC : Nat → Nat → Nat} (hsq : SqrHypX impl R ns stkS aboveS sqC)
    (hkS : stkS ≤ kcP) (haS : aboveS ≤ 88) (hsm : ∀ ℓ a a', a ≤ a' → sqC ℓ a ≤ sqC ℓ a')
    {stkM aboveM : Nat} {mlC : Nat → Nat → Nat → Nat} (hmu : MulHypX impl R ns stkM aboveM mlC)
    (hkM : stkM ≤ kcP) (haM : aboveM ≤ 88) (hmm : ∀ ℓ a a' c c', a ≤ a' → c ≤ c' → mlC ℓ a c ≤ mlC ℓ a' c')
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kcP) (haT : aboveT ≤ 88)
    (ret0 : BitVec 64) (Q : State → Prop)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L2 : List (Nat × Nat)} {b2 ℓ : Nat}
    (h : WC R L K g sp st zp zc s.mem M L2 b2 ℓ) (hkK : 208 + kcP ≤ K) (hℓ : ℓ + 2 ^ 12 ≤ 2 ^ 16)
    (hcost : P2Pre.cost sqC mlC ℓ 4 lm ≤ b2)
    (S2 : State) (hpc : S2.pc = BitVec.ofNat 64 1790928) (hsp : S2.sp = BitVec.ofNat 64 sp)
    (h28 : S2.regs 28 = BitVec.ofNat 64 g) (hm : S2.mem = M)
    (h0 : S2.regs 0 = BitVec.ofNat 64 st) (h1 : S2.regs 1 = BitVec.ofNat 64 (sp + 320)) (h2 : S2.regs 2 = 4#64)
    (h3 : S2.regs 3 = 4#64) (h4 : S2.regs 4 = 2#64) (h5 : S2.regs 5 = BitVec.ofNat 64 lm)
    (h6 : S2.regs 6 = BitVec.ofNat 64 xp) (h7 : S2.regs 7 = BitVec.ofNat 64 xl) (h8 : S2.regs 8 = BitVec.ofNat 64 xc)
    (h30 : S2.regs 30 = BitVec.ofNat 64 1795572)
    (KT' : KT impl R L K g sp st zp zc s.mem M L2 kcP sqC mlC b2 ℓ lm (natVal s.mem xp xl) (S2.regs 18) (S2.regs 29)
      ret0 Q) :
    ReachesRet (LibW.program.link impl) ret0 S2 Q := by
  have hpre := ppre hP h (kcP := kcP) (sqC := sqC) (mlC := mlC) hkK hℓ hsp h28 hm h30 hcost
  have hce := h.cenv hP
  have hsN : S2.sp.toNat = sp := by rw [hsp, BitVec.toNat_ofNat]; have := hce.2.2.1; omega
  have hgN : (S2.regs 28).toNat = g := by rw [h28, BitVec.toNat_ofNat]; have := hce.2.2.2.2.1; omega
  have hxv := (obj_at hP h hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun h0 => (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0).2.2.2.2.2.1) hsN hm (stk := 208 + kcP)
    (above := 80) hkK (by omega)).2.2.2
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hLs := hP.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlen := h.len
  have hlo := h.lo
  have r18 := S2.regs 18
  refine ReachesRet.call_regions (P2Pre.full hap hns hnf hmv hwb hkc hsn hkN haN hsq hkS haS hsm hmu hkM haM hmm htr
    hkT haT b2 L2 st (sp + 320) 4 4 2 lm xp xl xc) hpc ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hpre⟩
    fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  obtain ⟨bp, hd, L3, b3, hx, hb, hinv, hscr, hsap, hsa, hF, hLF, hain, hbu⟩ := hq
  subst hm
  rw [hgN] at hinv
  rw [hlen] at hb hsa
  have hF' : MemFrame S2.mem s'.mem (R.rt ++ ([(sp - (208 + kcP), sp - 8), (sp + 8, sp + 80)] ++
      ([(sp + 320, sp + 320 + 24 * 4)] ++ stkWs S2.mem st))) := by
    have := hF; simp only [P2Pre.AW, P2Pre.LW, winA, P2Pre.K, P2Pre.A, hsN, ExpHyp.stWs] at this
    rwa [List.append_assoc] at this
  have hw : WC R L K g sp st zp zc s.mem s'.mem L3 b3 (ℓ + StackNat.rnd (P2Pre.NB 4 lm)) := by
    refine h.call hF' hLF hrg ?_ ?_ hx hinv hsa.1 hsa.2.1 (by omega) hsa.2.2 hain
    · intro a k o1 o2 o3 o4
      rw [outside_append, outside_append]
      refine ⟨?_, ?_, o3⟩ <;> simp only [WN, outside_cons, outside_nil, and_true] at o2 ⊢ <;> omega
    · intro a k hin ho
      show Outside a k ([(sp + 320, sp + 320 + 24 * 4)] ++ stkWs S2.mem st)
      rw [outside_append]
      refine ⟨?_, stk_out h (Or.inl hin) ho⟩
      obtain ⟨r, hr, q1, q2⟩ := hin
      have := hLs r hr
      simp only [outside_cons, outside_nil, and_true] at this ⊢
      omega
  refine KT' s' L3 b3 bp (hr.trans h30) (e1.trans hsp) (e2.trans h28) e3 e4 hw hb (fun j hj => ?_)
    (Scr.rebase h hscr) hbu hsa.2.2 hx hscr (hF'.mono fun a k ho => ?_)
  · have := hd j hj; rwa [hxv] at this
  · rw [outside_append, outside_append] at ho
    rw [outside_append, outside_append, outside_append]
    refine ⟨ho.1.1, ?_, ?_, ho.2⟩
    · have := ho.1.2; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    · have := ho.1.2; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega

end

end FvModexp.Arm64.P2W2
