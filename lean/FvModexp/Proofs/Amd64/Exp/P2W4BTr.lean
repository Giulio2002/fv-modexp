import FvModexp.Proofs.Amd64.Exp.P2W4BSq

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): a loop-body `z = z.trunc(z, logM)` call (agent divmc s77, port of divmc s72; amd64 twin of agent
infra's `Arm64.P2W4BTr`)

`trB`: at the `nat.trunc` entry (`RSP = sp - 0x8`, `[sp - 0x8]` = the return address `fn + idx`) with `z = x = (p, l, c)`
a buffer of either class holding the odd `X'` and `n = logM`: `Trunc.Hyp2` (in place: `truncNeed l lm ≤ l ≤ c`) and
the continuation with `BF` at the result memory, `(p, l', c)` holding `X' mod 2^logM` (`l' ≤ w`, same class), every
other buffer kept, the slots `[sp + 0x50, sp + 0x358)` and the budget.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

open FvModexp.Amd64.EvenHyp

theorem makeCost_mono {a b : Nat} (h : a ≤ b) (hb : 2 ≤ b) : makeCost a ≤ makeCost b := by
  unfold makeCost makeCap allocCost
  split <;> split <;> omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem trB {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp tp : Nat} (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp)
    {v : Bool} {p l c X' : Nat} (hd : BC R L K g sp st zp zc M L1 zzp tp lm v p c) (hxv : NV M p l c X')
    (hl : l ≤ 2 ^ 16) (hcost : P2Pre.tC lm ≤ b1)
    {ret0 : W64} {Q : State → Prop} {idx : Nat} (hidx : idx < 0xb11)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6188320) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 0x8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0) (hdf : T.df = false)
    (hm : T.mem = M) (hra : M.readLE (sp - 0x8) 8 = 6197952 + idx)
    (h0 : T.regs 0 = BitVec.ofNat 64 p) (h3 : T.regs 3 = BitVec.ofNat 64 l) (h1 : T.regs 1 = BitVec.ofNat 64 c)
    (h7 : T.regs 7 = BitVec.ofNat 64 p) (h6 : T.regs 6 = BitVec.ofNat 64 l) (h8 : T.regs 8 = BitVec.ofNat 64 c)
    (h9 : T.regs 9 = BitVec.ofNat 64 lm)
    (KC : ∀ (s' : State) (L2 : List (Nat × Nat)) (b2 l' : Nat), s'.rip = BitVec.ofNat 64 (6197952 + idx) →
      s'.regs 4 = BitVec.ofNat 64 sp → s'.regs 5 = T.regs 5 → s'.regs 14 = T.regs 14 → s'.xmm 15 = 0 →
      s'.fsBase = s.fsBase → s'.df = false →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 3 = BitVec.ofNat 64 l' → s'.regs 1 = BitVec.ofNat 64 c →
      BF R L K g sp st bp r zp zc xp xl xc yp yl lm s s'.mem L2 b2 zzp tp →
      (∀ a k, sp + 0x50 ≤ a → a + k ≤ sp + 0x358 → s'.mem.readLE a k = M.readLE a k) →
      BC R L K g sp st zp zc s'.mem L2 zzp tp lm v p c → NV s'.mem p l' c (X' % 2 ^ lm) → l' ≤ W lm →
      (∀ (w : Bool) (q d : Nat), BC R L K g sp st zp zc M L1 zzp tp lm w q d → 0 < d →
        Apart q (8 * d) p (8 * c) → BC R L K g sp st zp zc s'.mem L2 zzp tp lm w q d ∧
          ∀ a k, q ≤ a → a + k ≤ q + 8 * d → s'.mem.readLE a k = M.readLE a k) →
      b1 - P2Pre.tC lm ≤ b2 → ReachesRet (LibW.program.link impl) ret0 s' Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  obtain ⟨xlc, xv, xN, xo⟩ := hxv
  have hl0 : 0 < l := len_pos xv xo
  have hc : 0 < c := by omega
  obtain ⟨hce, hsv, -, -, hinv, hsN, hgN, hfsN⟩ := bodyEnv hP hB hsp h14 hfs hm hkT haT
  obtain ⟨dW, -, -, -, dA⟩ := BC.arg hP hB hd hc hsN hgN hfsN hm hkT haT
  obtain ⟨xR, -⟩ := dA l xlc
  obtain ⟨-, hlv, aW, -, aS, -, -, -⟩ := BC.facts hP hB hd hc
  have hd48 := (hlv hc).2.2.2
  have hK := hP.1.2.2.2.2.2.2.1
  have hlm2 := hP.2.2.2.2.1
  have hlm := hP.2.2.2.2.2.1
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hW1 : 1 ≤ W lm := by simp only [W]; omega
  have hneed : truncNeed l lm ≤ l := Nat.min_le_left _ _
  have hmc : makeCost (truncNeed l lm) ≤ P2Pre.tC lm :=
    makeCost_mono (Nat.le_trans (Nat.min_le_right _ _) (by simp only [P2Pre.W]; omega)) (by omega)
  have hst48 := hB.wc.sok.2.2.2.1
  have hrd : T.mem.readLE (T.regs 4).toNat 8 = 6197952 + idx := by rw [hsN, hm]; exact hra
  subst hm
  refine LibCalls.truncCall hap hns htr (b := b1 + stkR (HW (stLen s.mem st) lm) T.mem st) (L := L1)
    (ra_w4 hap hnf idx hidx) hpc hrd h0 h3 h1 h7 h6 h8 h9 hx15 hdf (by omega) (by omega) (by omega) (by omega)
    (by omega)
    ⟨hce, hsv, xlc, dW, xR, hl, by omega, Or.inl rfl, by omega, hinv⟩ (Or.inl xN) (Or.inl rfl)
    fun s' hpc' hsp' h5' h14' hx15' hrg hpost => ?_
  obtain ⟨hfs', hdf', p', l', c', e0, e3, e1, L2, b2, ⟨hv', hn', hlc', -, -, hre, -⟩, -, ⟨hLE, hbud', hinv'⟩, hF',
    hLF'⟩ := hpost
  obtain ⟨rfl, rfl⟩ := hre (by omega)
  simp only [win, hsN] at hF'
  have hstw : Apart st 24 (sp - 0x8 - K) (K + 0x360) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  rw [hgN] at hinv'
  unfold Apart at aW aS
  have hK0 : K ≤ sp - 0x8 := (hB.wc.cenv hP).2.1
  -- the header is kept (outside the callee's writes)
  have hLF3 : LiveFrame T.mem s'.mem L1 ([(sp - 0x8 - stkT, sp - 0x8 + aboveT)] ++ [(p', p' + 8 * c')]) :=
    Expmc.liveFrame_widen hLF' fun a k ho => by rw [outside_append] at ho; exact ho.2
  have hF3 : MemFrame T.mem s'.mem (R.rt ++ ([(sp - 0x8 - stkT, sp - 0x8 + aboveT)] ++ [(p', p' + 8 * c')])) := by
    simpa only [List.append_assoc] using hF'
  have hhd : ∀ j, j + 8 ≤ 24 → s'.mem.readLE (st + j) 8 = T.mem.readLE (st + j) 8 := fun j hj =>
    Held.readLE (hB.wc.sok.2.1.sub (by omega) (by omega)) hF3 hLF3 (by
      simp only [List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega)
  have ee0 : stW s'.mem st = stW T.mem st := by have := hhd 0 (by omega); simpa using this
  have ee1 : stLen s'.mem st = stLen T.mem st := hhd 8 (by omega)
  have ee2 : stCap s'.mem st = stCap T.mem st := hhd 16 (by omega)
  have hsb : StackBackL R L1 L2 st T.mem s'.mem :=
    ⟨⟨stkOK_hdr hB.wc.sok hF' ee0 ee1 ee2 hLE, ee1, Or.inl ⟨ee0, ee2⟩⟩, fun hn => absurd ⟨ee0, ee2⟩ hn⟩
  have hF2 : MemFrame T.mem s'.mem (R.rt ++ [(sp - 0x8 - stkT, sp - 0x8 + aboveT)] ++ [(p', p' + 8 * c')] ++
      stkWs T.mem st) := hF'.mono fun a k ho => by rw [outside_append] at ho; exact ho.1
  have hLF2 : LiveFrame T.mem s'.mem L1 ([(p', p' + 8 * c')] ++ stkWs T.mem st) :=
    Expmc.liveFrame_widen hLF' fun a k ho => by rw [outside_append] at ho; exact ho.1
  have hb3 : ∃ b3, R.inv (b3 + stkR (HW (stLen s.mem st) lm) s'.mem st) L2 g (view R.rt L2 s'.mem) ∧
      b1 - P2Pre.tC lm ≤ b3 :=
    ⟨b2 - stkR (HW (stLen s.mem st) lm) T.mem st, by rw [stkR_congr ee2, Nat.sub_add_cancel (by omega)]; exact hinv',
      by omega⟩
  obtain ⟨b3, hinv3, hbud3⟩ := hb3
  obtain ⟨hB', hslot, hkeep⟩ := BF.call hP hB hd hc hkT haT hF2 hLF2 hrg hLE hinv3 hsb
  have hval : natVal s'.mem p' l' = X' % 2 ^ lm := by rw [hv', xv]
  have hlW : l' ≤ W lm := by
    refine nlen_bd hn' (by
      rw [hval]
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by decide) (by simp only [W]; omega)))
  have hodd : X' % 2 ^ lm % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow_iff_le_right'.2 (by omega : 1 ≤ lm) : 2 ^ 1 ∣ 2 ^ lm)]; exact xo
  have hsp2 : s'.regs 4 = BitVec.ofNat 64 sp := by
    rw [hsp', hsp]; apply BitVec.eq_of_toNat_eq
    have hce' := hB.wc.cenv hP
    have := hce'.2.2.1
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; rw [show BitVec.toNat (8 : BitVec 64) = 8 from rfl]; omega
  exact KC s' L2 b3 l' hpc' hsp2 h5' h14' (hx15'.trans hx15) (hfs'.trans hfs) (hdf'.trans hdf) e0 e3 e1 hB' hslot
    (BC.call hd hF'.accessible hLE hsb.1) ⟨hlc', hval, hn', hodd⟩ hlW hkeep (by omega)

end

end FvModexp.Amd64.P2W4
