import FvModexp.Proofs.Amd64.Exp.P2W2PQ
import FvModexp.Proofs.Amd64.Exp.P2Pre

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the call of `buildPrecomputationWindowModPower2(stk, powers[:], 2, logM, x)`
(nat.go:1151; entry `0x5e8900`, return `ppRet` = fn+0x289) (agent divmc s68; amd64 twin of agent infra's
`Arm64.P2W2PC`)

`segPC`: from the callee entry state `S2` (`ppre`'s precondition) through `P2Pre.full` (the Summary on `LibW`, which
contains this function, so no return-address condition) to the return; the continuation `KT` gets `WC` at the return
memory (level `ℓ + rnd(5w)`), the table `powers[j] = X^j mod 2^logM` (`P2Pre.PwD`, `j < 4`), `buf` as a scratch nat
relative to the entry with `BU`, the stack array relative to the call (`ArrKF`), and the callee's frame (for the slots).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

/-- the table call's return (fn+0x289) -/
abbrev ppRetC : Nat := 6201513

/-- the continuation after the table -/
@[reducible] def KT (impl : List Amd64.Segment) (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc : Nat)
    (m0 M : Memory) (L2 : List (Nat × Nat)) (kc : Nat) (b2 ℓ lm X : Nat) (r5 : W64) (fsB : W64) (ret0 : W64)
    (Q : State → Prop) : Prop :=
  ∀ (s' : State) (L3 : List (Nat × Nat)) (b3 tp : Nat),
    s'.rip = BitVec.ofNat 64 ppRetC → s'.regs 4 = BitVec.ofNat 64 sp → s'.regs 14 = BitVec.ofNat 64 g →
    s'.regs 5 = r5 → s'.xmm 15 = 0 → s'.fsBase = fsB → s'.df = false →
    WC R (HW (stLen m0 st) lm) L K g sp st zp zc m0 s'.mem L3 b3 (ℓ + StackNat.rnd (P2Pre.NB 4 lm)) →
    b2 - P2Pre.cost 4 lm ≤ b3 →
    (∀ j, j < 4 → P2Pre.PwD s'.mem (sp + 0x140) tp lm X j) →
    Scr R L L3 m0 s'.mem st tp (P2Pre.NB 4 lm) → P2Pre.BU s'.mem st tp (8 * P2Pre.NB 4 lm) →
    ArrKF R L2 st M s'.mem → LiveExt R L2 L3 → Scr R L2 L3 M s'.mem st tp (P2Pre.NB 4 lm) →
    MemFrame M s'.mem (R.rt ++ [(sp - 8 - P2Pre.K kc, sp + 72), (sp + 0x140, sp + 0x1a0)] ++ stkWs M st) →
    ReachesRet (LibW.program.link impl) ret0 s' Q

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **the table call** -/
theorem segPC {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains P2Pre.fn = false)
    (hmv : MemmoveLive64 (LibW.program.link impl) P2Pre.mvE 4096 R)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2)
    {kc : Nat} (hkc : 4608 ≤ kc)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ kc) (haN : aboveN ≤ 88)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS1 : sqrW 128 ≤ kS) (hkS : kS ≤ kc)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM1 : mulWX64 ≤ kM) (hkM : kM ≤ kc)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (ret0 : W64) (Q : State → Prop)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hX : EX xp xl s) {M : Memory}
    {L2 : List (Nat × Nat)} {b2 ℓ : Nat}
    (h : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L2 b2 ℓ) (hkK : P2Pre.K kc ≤ K)
    (hcost : P2Pre.cost 4 lm ≤ b2) (hℓZ : ℓ = stLen s.mem st + 8 * W lm + StackNat.rnd (2 * W lm))
    (S2 : State) (hpc : S2.rip = BitVec.ofNat 64 0x5e8900) (hsp : S2.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : S2.regs 14 = BitVec.ofNat 64 g) (hfsN : S2.fsBase.toNat = fs) (hx15 : S2.xmm 15 = 0)
    (hdf : S2.df = false) (hm : S2.mem = M)
    (h0 : S2.regs 0 = BitVec.ofNat 64 st) (h3 : S2.regs 3 = BitVec.ofNat 64 (sp + 0x140)) (h1 : S2.regs 1 = 4#64)
    (h7 : S2.regs 7 = 4#64) (h6 : S2.regs 6 = 2#64) (h8 : S2.regs 8 = BitVec.ofNat 64 lm)
    (h9 : S2.regs 9 = BitVec.ofNat 64 xp) (h10 : S2.regs 10 = BitVec.ofNat 64 xl)
    (h11 : S2.regs 11 = BitVec.ofNat 64 xc) (hra : M.readLE (sp - 8) 8 = ppRetC)
    (KT' : KT impl R L K g sp st zp zc s.mem M L2 kc b2 ℓ lm (natVal s.mem xp xl) (S2.regs 5) S2.fsBase ret0 Q) :
    ReachesRet (LibW.program.link impl) ret0 S2 Q := by
  have hpre := ppre hP hX h hkK hℓZ hsp h14 hfsN hx15 hdf hm (by rw [hra]; decide) hcost
  have hce := h.cenv hP
  have hK0 : K ≤ sp - 8 := hce.2.1
  have hA0 : sp - 8 + 0x238 ≤ 2 ^ 48 := hce.2.2.1
  have hkK' : 184 + kc ≤ K := hkK
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hsN : (S2.regs 4).toNat = sp - 8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have hgN : (S2.regs 14).toNat = g := by rw [h14, BitVec.toNat_ofNat]; have := hce.2.2.2.2.1; omega
  have hxv := (obj_at h hP.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun h0 => (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0).2.2.2.2.2.2.1) hsN hm (stk := P2Pre.K kc)
    (above := P2Pre.A) hkK (by decide)).2.2
  have hLs := hP.cenv0.2.2.2.2.2.2.2.2.2.2.1
  have hlen := h.len
  have hlo := h.lo
  refine ReachesRet.call_regions (P2Pre.full hap hns hnf hmv hwb hkc hsn hkN haN hsq hkS1 hkS hml hkM1 hkM htr
    hkT haT b2 L2 st (sp + 0x140) 4 4 2 lm xp xl xc) hpc ⟨h0, h3, h1, h7, h6, h8, h9, h10, h11, hpre⟩
    fun s' hr ⟨⟨e4, e5, e14, ex15⟩, efs, edf, tp, hd, L3, b3', hx, hb', hinv', hscr, hsap, hsa, hF, hLF, hain, hbu⟩
      hrg => ?_
  subst hm
  rw [hgN] at hinv'
  rw [hlen] at hb' hsa
  obtain ⟨b3, hinv, hb⟩ := P2Q.effP hinv' hb'
  rw [hℓZ] at hinv
  have hF' : MemFrame S2.mem s'.mem (R.rt ++ ([(sp - 8 - P2Pre.K kc, sp - 8 + 80)] ++
      ([(sp + 0x140, sp + 0x140 + 24 * 4)] ++ stkWs S2.mem st))) := by
    have := hF; simp only [P2Pre.AW, P2Pre.LW, win, P2Pre.A, hsN] at this
    rwa [List.append_assoc] at this
  have hw : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem s'.mem L3 b3
      (ℓ + StackNat.rnd (P2Pre.NB 4 lm)) := by
    refine h.call hF' hLF hrg ?_ ?_ hx hinv hsa.1 hsa.2.1 (by omega) hsa.2.2 hain
    · intro a k o1 o2 o3 o4
      rw [outside_append, outside_append]
      refine ⟨?_, ?_, o3⟩ <;> simp only [WN, outside_cons, outside_nil, and_true] at o2 ⊢ <;> omega
    · intro a k hin ho
      show Outside a k ([(sp + 0x140, sp + 0x140 + 24 * 4)] ++ stkWs S2.mem st)
      rw [outside_append]
      refine ⟨?_, stk_out h (Or.inl hin) ho⟩
      obtain ⟨r, hr, q1, q2⟩ := hin
      have := hLs r hr
      simp only [outside_cons, outside_nil, and_true] at this ⊢
      omega
  have hs4 : s'.regs 4 = BitVec.ofNat 64 sp := by
    have e : BitVec.ofNat 64 sp = BitVec.ofNat 64 (sp - 8) + BitVec.ofNat 64 8 := by
      rw [← BitVec.ofNat_add]; congr 1; omega
    rw [e4, hsp, e]; rfl
  refine KT' s' L3 b3 tp (hr.trans (by rw [retAddrOf, hsN, hra])) hs4 (e14.trans h14) e5 (ex15.trans hx15)
    efs (edf.trans hdf) hw hb (fun j hj => ?_) (Scr.rebase h hscr) hbu hsa.2.2 hx hscr (hF'.mono fun a k ho => ?_)
  · have := hd j hj; rwa [hxv] at this
  · rw [outside_append, outside_append] at ho
    rw [outside_append, outside_append, outside_append]
    refine ⟨ho.1.1, ?_, ?_, ho.2⟩
    · have := ho.1.2; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    · have := ho.1.2; simp only [outside_cons, outside_nil, and_true] at this ⊢; omega

end

end FvModexp.Amd64.P2W2
