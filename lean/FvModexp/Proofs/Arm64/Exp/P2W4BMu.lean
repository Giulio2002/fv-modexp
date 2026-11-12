import FvModexp.Proofs.Arm64.Exp.P2W4BSq

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (arm64): the loop-body `z = z.mul(stk, x, powers[j])` call (agent infra)

`mulB`: as `sqrB` with the second operand a table entry `powers[j] = (bp + 8 j w, ly, w)` (value `p2Pow logM X j`):
the result has class `v`, value `X' · powers[j]`, length `≤ 2w`; the operand `x` is kept.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W4

open P2W2 (grE mcE wbE wTy grE_eq mcE_eq wbE_eq)

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn WrOut stWs)

theorem mul_a : segAddr Extracted.program fnMul = 1814128 := by decide

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {ret : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem mulB {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} {mlC : Nat → Nat → Nat → Nat} (hsq : MulHypX impl R ns stkS aboveS mlC) (hkS : stkS ≤ K)
    (haS : aboveS ≤ 88) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp bp : Nat} (hB : BF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp)
    {v : Bool} {pd ld cd : Nat} (hd : BC R L K g sp st zp zc M L1 zzp bp lm v pd cd) (hcd : 0 < cd) (hld : ld ≤ cd)
    {px lx cx X' : Nat} (hx : BC R L K g sp st zp zc M L1 zzp bp lm (!v) px cx) (hxv : NV M px lx cx X')
    (hlx : lx ≤ W lm) {j ly : Nat} (hj : j < 16) (hly : M.readLE (sp + 320 + 24 * j + 8) 8 = ly)
    (hPo : Exp.p2Pow lm (natVal s.mem xp xl) j % 2 = 1) (hcost : mlC (ℓL (stLen s.mem st) lm) lx ly ≤ b1)
    {ret0 : BitVec 64} {Q : State → Prop} {idx : Nat} (hidx : idx < 519)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 1814128) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (hm : T.mem = M) (h30 : T.regs 30 = BitVec.ofNat 64 (1792928 + 4 * idx))
    (h0 : T.regs 0 = BitVec.ofNat 64 pd) (h1 : T.regs 1 = BitVec.ofNat 64 ld) (h2 : T.regs 2 = BitVec.ofNat 64 cd)
    (h3 : T.regs 3 = BitVec.ofNat 64 st) (h4 : T.regs 4 = BitVec.ofNat 64 px) (h5 : T.regs 5 = BitVec.ofNat 64 lx)
    (h6 : T.regs 6 = BitVec.ofNat 64 cx) (h7 : T.regs 7 = BitVec.ofNat 64 (bp + 8 * (j * W lm)))
    (h8 : T.regs 8 = BitVec.ofNat 64 ly) (h9 : T.regs 9 = BitVec.ofNat 64 (W lm))
    (KC : ∀ (s' : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat), s'.pc = BitVec.ofNat 64 (1792928 + 4 * idx) →
      s'.sp = T.sp → s'.regs 28 = T.regs 28 → s'.regs 29 = T.regs 29 → s'.regs 18 = T.regs 18 →
      s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 1 = BitVec.ofNat 64 l' → s'.regs 2 = BitVec.ofNat 64 c' →
      BF R L K g sp st zp zc xp xl xc yp yl lm ret s s'.mem L2 b2 zzp bp →
      (∀ a k, sp + 88 ≤ a → a + k ≤ sp + 848 → s'.mem.readLE a k = M.readLE a k) →
      BC R L K g sp st zp zc s'.mem L2 zzp bp lm v p' c' → NV s'.mem p' l' c' (X' * Exp.p2Pow lm (natVal s.mem xp xl) j) → l' ≤ 2 * W lm →
      BC R L K g sp st zp zc s'.mem L2 zzp bp lm (!v) px cx → NV s'.mem px lx cx X' →
      b1 - mlC (ℓL (stLen s.mem st) lm) lx ly ≤ b2 → ReachesRet (LibW.program.link impl) ret0 s' Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  obtain ⟨xlc, xv, xN, xo⟩ := hxv
  have hlx0 : 0 < lx := len_pos xv xo
  have hcx : 0 < cx := by omega
  obtain ⟨hce, hsv, hgl, hsi, hsx, hinv, hsN, hgN⟩ := bodyEnv hP hB hsp h28 hm hkS haS
  obtain ⟨dW, dA⟩ := BC.arg hP hB hd hcd hsN hgN hm hkS haS
  obtain ⟨-, -, dS, dO⟩ := dA cd (Nat.le_refl _)
  obtain ⟨xR, xC, xS, xO⟩ := (BC.arg hP hB hx hcx hsN hgN hm hkS haS).2 lx xlc
  have hdx := bc_apart hP hB hd hx hcd hcx
  have hdx' := hdx
  unfold Apart at hdx'
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.2.1; simp only [W]; omega
  have hl16 : stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 :=
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlen := hB.wc.len
  have hd48 := ((BC.facts hP hB hd hcd).2.1 hcd).2.2.2
  have hx48 := ((BC.facts hP hB hx hcx).2.1 hcx).2.2.2
  have hdc40 := (BC.facts hP hB hd hcd).1
  have hxc40 := (BC.facts hP hB hx hcx).1
  have hst48 := hB.wc.sok.2.2.2.1
  have hdWo := dW.2.2 hcd
  obtain ⟨-, -, yd2, yd3, -⟩ := hB.tz.pw j hj
  rw [hly] at yd2 yd3
  have yN : NatNorm M (bp + 8 * (j * W lm)) ly := by
    have := (hB.tz.pw j hj).2.2.2.2; rw [hly] at this; exact this
  have eW : P2Pre.W lm = W lm := rfl
  rw [eW] at yd2 yd3
  obtain ⟨yR, yC, yS, yO⟩ := tbl_arg hP hB (j := j) (l := ly) hj yd2 hsN hm hkS haS
  have hjW : (j + 1) * W lm ≤ P2Pre.NB 16 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : j * W lm + W lm ≤ P2Pre.NB 16 lm := by rw [← Nat.succ_mul]; exact hjW
  have hdb : Apart pd (8 * cd) bp (8 * P2Pre.NB 16 lm) := by
    cases v
    · obtain ⟨rfl, rfl⟩ := hd; exact hB.tz.zb
    · exact (hd.ap hcd).2.2.2.2.2.2
  have hdy : Apart pd (8 * cd) (bp + 8 * (j * W lm)) (8 * W lm) := by unfold Apart at hdb ⊢; omega
  have hb48 := hB.tz.bscr.b48
  have hW1 : 1 ≤ W lm := by have := hP.2.2.2.2.2.1; simp only [W]; omega
  have hdy' := hdy
  unfold Apart at hdy'
  refine LibCalls.mulCallX hap hns hsq (b := b1) (L := L1) (ra_w4 hap hnf idx hidx) (by rw [hpc, mul_a])
    h30 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    ⟨hce, hsv, hgl, hld, dW, xR, yR, by omega, by omega, Or.inr fun _ _ => by unfold Apart; omega,
      Or.inr fun _ _ => by unfold Apart; omega, hsi,
      by rw [hm, hlen]; have := lL_bd (stLen s.mem st) lm; omega, by rw [hm]; exact dS,
      by rw [hm]; exact xS, by rw [hm]; exact yS, by rw [hm, hlen]; exact hcost, hinv⟩ xC yC
    ⟨hsx, hdWo.1, fun he => absurd he (by omega), fun he => absurd he (by omega), by rw [hm]; exact dO,
      by rw [hm]; exact xO, by rw [hm]; exact yO⟩
    fun s' hpc' hsp' h28' h29' h18' hrg hpost hreu => ?_
  obtain ⟨p', l', c', e0, e1, e2, L2, b2, ⟨hv', hn', hlc', hc40', hlive', horg⟩, ⟨hLE, hbud', hinv'⟩, hsb, hnew, hF',
    hLF'⟩ := hpost
  simp only [winA, hsN, stWs, hm] at hF' hLF' hsb hnew hbud' hv' hrg
  rw [hgN] at hinv'
  rw [hlen] at hbud'
  obtain ⟨hB', hslot, hkeep⟩ := BF.call hP hB hd hcd hkS haS hF' hLF' hrg hLE hinv' hsb
  obtain ⟨hx', hxb⟩ := hkeep (!v) px cx hx hcx hdx.symm
  obtain ⟨xv', xN'⟩ := nv_keep (M := M) (M' := s'.mem) (p := px) (l := lx) fun a k h1 h2 => hxb a k h1 (by omega)
  have hval : natVal s'.mem p' l' = X' * Exp.p2Pow lm (natVal s.mem xp xl) j := by rw [hv', xv, yd3]
  have hlt : natVal s'.mem p' l' < 2 ^ (64 * (lx + ly)) := by
    rw [hv']
    calc natVal M px lx * natVal M (bp + 8 * (j * W lm)) ly < 2 ^ (64 * lx) * 2 ^ (64 * ly) :=
          Nat.mul_lt_mul'' (natVal_lt M px lx) (natVal_lt _ _ ly)
      _ = 2 ^ (64 * (lx + ly)) := by rw [← Nat.pow_add]; congr 1; omega
  have hl2 : l' ≤ 2 * W lm := Nat.le_trans (nlen_bd hn' hlt) (by omega)
  have hodd : X' * Exp.p2Pow lm (natVal s.mem xp xl) j % 2 = 1 := by rw [Nat.mul_mod, xo, hPo]
  have hacc : ∀ a n w, s'.mem.accessible a n w = M.accessible a n w := hF'.accessible
  have hres : BC R L K g sp st zp zc s'.mem L2 zzp bp lm v p' c' := by
    cases v
    · obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨r0, r2⟩ := hreu (by omega) (by
        intro o ho; simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · exact end_ne hdx hcd hcx
        · exact end_ne hdy hcd (by omega))
      have hc' : c' = 2 * W lm := ofNat_inj' (by omega) (by omega) (e2.symm.trans r2)
      subst hc'
      have hp' : p' = pd := ofNat_inj' (by have := (hlive' (by omega)).2.2.2; omega) (by omega)
        (e0.symm.trans r0)
      exact ⟨hp', rfl⟩
    · by_cases heq : p' = pd ∧ c' = cd
      · obtain ⟨rfl, rfl⟩ := heq
        exact UB.call hd hacc hLE hsb.1
      · obtain ⟨hn2, hin, hap'⟩ := horg.resolve_left heq
        exact ub_res hP hB (by omega) hc40' hin hap' hlive' hLE hsb.1 (hnew heq (by omega))
  exact KC s' L2 b2 p' l' c' hpc' hsp' h28' h29' h18' e0 e1 e2 hB' hslot hres ⟨hlc', hval, hn', hodd⟩ hl2 hx'
    ⟨xlc, xv'.trans xv, xN' xN, xo⟩ hbud'

end

end FvModexp.Arm64.P2W4
