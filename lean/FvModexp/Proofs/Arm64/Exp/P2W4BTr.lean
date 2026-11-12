import FvModexp.Proofs.Arm64.Exp.P2W4BA
import FvModexp.Proofs.Arm64.Exp.P2W4Cp1

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): a loop-body `z = z.trunc(z, logM)` call (agent infra)

`trB`: at the `nat.trunc` entry from `SP = sp` (return address `fn + 4 idx`) with `z = x = (p, l, c)` a buffer of
either class (odd value `X'`): the callee (asm's `Trunc.Hyp2`) works in place (`min(l, w) ≤ c`), the continuation
gets `BF` at the result memory, the result `(p, l', c)` (same class, value `X' mod 2^logM`, `l' ≤ w`), every other
buffer apart from `z` kept, the window slots from `sp + 88` on and the budget (`makeCost ≤ tC`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn WrOut stWs)

theorem trunc_a : segAddr Extracted.program fnTrunc = 1786000 := by decide

theorem makeCost_mono {a b : Nat} (h : a ≤ b) (hb : 2 ≤ b) : makeCost a ≤ makeCost b := by
  unfold makeCost makeCap allocCost
  split <;> split <;> omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {ret : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem trB {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp bp : Nat} (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp)
    {v : Bool} {p l c X' : Nat} (hd : BC R L K g sp st zp zc M L1 zzp bp lm v p c) (hxv : NV M p l c X')
    (hl : l ≤ 2 ^ 16) (hcost : P2Pre.tC lm ≤ b1)
    {ret0 : BitVec 64} {Q : State → Prop} {idx : Nat} (hidx : idx < 519)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1786000) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (hm : T.mem = M) (h30 : T.regs 30 = BitVec.ofNat 64 (1792928 + 4 * idx))
    (h0 : T.regs 0 = BitVec.ofNat 64 p) (h1 : T.regs 1 = BitVec.ofNat 64 l) (h2 : T.regs 2 = BitVec.ofNat 64 c)
    (h3 : T.regs 3 = BitVec.ofNat 64 p) (h4 : T.regs 4 = BitVec.ofNat 64 l) (h5 : T.regs 5 = BitVec.ofNat 64 c)
    (h6 : T.regs 6 = BitVec.ofNat 64 lm)
    (KC : ∀ (s' : State) (L2 : List (Nat × Nat)) (b2 l' : Nat), s'.pc = BitVec.ofNat 64 (1792928 + 4 * idx) →
      s'.sp = T.sp → s'.regs 28 = T.regs 28 → s'.regs 29 = T.regs 29 → s'.regs 18 = T.regs 18 →
      s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = BitVec.ofNat 64 l' → s'.regs 2 = BitVec.ofNat 64 c →
      BF R L K g sp st zp zc xp xl xc yp yl lm ret s s'.mem L2 b2 zzp bp →
      (∀ a k, sp + 88 ≤ a → a + k ≤ sp + 848 → s'.mem.readLE a k = M.readLE a k) →
      BC R L K g sp st zp zc s'.mem L2 zzp bp lm v p c → NV s'.mem p l' c (X' % 2 ^ lm) → l' ≤ W lm →
      (∀ (w : Bool) (q d : Nat), BC R L K g sp st zp zc M L1 zzp bp lm w q d → 0 < d →
        Apart q (8 * d) p (8 * c) → BC R L K g sp st zp zc s'.mem L2 zzp bp lm w q d ∧
          ∀ a k, q ≤ a → a + k ≤ q + 8 * d → s'.mem.readLE a k = M.readLE a k) →
      b1 - P2Pre.tC lm ≤ b2 → ReachesRet (LibW.program.link impl) ret0 s' Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  obtain ⟨xlc, xv, xN, xo⟩ := hxv
  have hl0 : 0 < l := len_pos xv xo
  have hc : 0 < c := by omega
  obtain ⟨hce, hsv, -, -, -, hinv, hsN, hgN⟩ := bodyEnv hP hB hsp h28 hm hkT haT
  obtain ⟨dW, dA⟩ := BC.arg hP hB hd hc hsN hgN hm hkT haT
  obtain ⟨xR, -, -, -⟩ := dA l xlc
  obtain ⟨-, hlv, aW, -, aS, -, -⟩ := BC.facts hP hB hd hc
  have hd48 := (hlv hc).2.2.2
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hlm2 := hP.2.2.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.1
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hW1 : 1 ≤ W lm := by simp only [W]; omega
  have hneed : truncNeed l lm ≤ l := Nat.min_le_left _ _
  have hmc : makeCost (truncNeed l lm) ≤ P2Pre.tC lm :=
    makeCost_mono (Nat.le_trans (Nat.min_le_right _ _) (by simp only [P2Pre.W]; omega)) (by omega)
  have hst48 := hB.wc.sok.2.2.2.1
  refine LibCalls.truncCall hap hns htr (b := b1) (L := L1) (ra_w4 hap hnf idx hidx) (by rw [hpc, trunc_a])
    h30 h0 h1 h2 h3 h4 h5 h6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨hce, hsv, xlc, dW, xR, hl, by omega, Or.inl rfl, by omega, hinv⟩ (Or.inl (by rw [hm]; exact xN)) (Or.inl rfl)
    fun s' hpc' hsp' h28' h29' h18' hrg hpost => ?_
  obtain ⟨p', l', c', e0, e1, e2, L2, b2, ⟨hv', hn', hlc', -, -, hre, -⟩, -, ⟨hLE, hbud', hinv'⟩, hF', hLF'⟩ :=
    hpost
  obtain ⟨rfl, rfl⟩ := hre (by omega)
  simp only [winA, hsN] at hF'
  try rw [hm] at hF'
  try rw [hm] at hLF'
  try rw [hm] at hv'
  try rw [hm] at hrg
  have hstw : Apart st 24 (sp - K) (K + 848) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  rw [hgN] at hinv'
  unfold Apart at aW aS
  -- the header is kept (outside the callee's writes)
  have hLF3 : LiveFrame M s'.mem L1 ([(sp - stkT, sp - 8), (sp + 8, sp + aboveT)] ++ [(p', p' + 8 * c')]) :=
    Expmc.liveFrame_widen hLF' fun a k ho => by rw [outside_append] at ho; exact ho.2
  have hF3 : MemFrame M s'.mem (R.rt ++ ([(sp - stkT, sp - 8), (sp + 8, sp + aboveT)] ++ [(p', p' + 8 * c')])) := by
    simpa only [List.append_assoc] using hF'
  have hhd : ∀ j, j + 8 ≤ 24 → s'.mem.readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj =>
    Held.readLE (hB.wc.sok.2.1.sub (by omega) (by omega)) hF3 hLF3 (by
      simp only [List.cons_append, List.nil_append, outside_cons, outside_nil, and_true]; omega)
  obtain ⟨ee0, ee1, ee2⟩ := hdr3 hhd
  have hsb : StackBackL R L1 L2 st M s'.mem :=
    ⟨⟨stkOK_hdr hB.wc.sok hF' ee0 ee1 ee2 hLE, ee1, Or.inl ⟨ee0, ee2⟩⟩, fun hn => absurd ⟨ee0, ee2⟩ hn⟩
  have hF2 : MemFrame M s'.mem (R.rt ++ [(sp - stkT, sp - 8), (sp + 8, sp + aboveT)] ++ [(p', p' + 8 * c')] ++
      stkWs M st) := hF'.mono fun a k ho => by rw [outside_append] at ho; exact ho.1
  have hLF2 : LiveFrame M s'.mem L1 ([(p', p' + 8 * c')] ++ stkWs M st) :=
    Expmc.liveFrame_widen hLF' fun a k ho => by rw [outside_append] at ho; exact ho.1
  obtain ⟨hB', hslot, hkeep⟩ := BF.call hP hB hd hc hkT haT hF2 hLF2 hrg hLE hinv' hsb
  have hval : natVal s'.mem p' l' = X' % 2 ^ lm := by rw [hv', xv]
  have hlW : l' ≤ W lm := by
    refine nlen_bd hn' (by
      rw [hval]
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by decide) (by simp only [W]; omega)))
  have hodd : X' % 2 ^ lm % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow_iff_le_right'.2 (by omega : 1 ≤ lm) : 2 ^ 1 ∣ 2 ^ lm)]; exact xo
  exact KC s' L2 b2 l' hpc' hsp' h28' h29' h18' e0 e1 e2 hB' hslot (BC.call hd hF'.accessible hLE hsb.1)
    ⟨hlc', hval, hn', hodd⟩ hlW hkeep (by omega)

end

end FvModexp.Arm64.P2W4
