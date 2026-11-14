import FvModexp.Proofs.Amd64.Exp.P2W2BSq

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the loop-body `zz = zz.mul(stk, z, powers[d])` call (agent divmc s72; amd64
twin of agent infra's `Arm64.P2W2BMu`)

`mulB`: at the `nat.mul` entry (`RSP = sp - 8`, `[sp - 8]` = the return address `fn + idx`, the stack argument
`y = powers[j]` at `[sp, sp + 24)`) with the destination `(pd, ld, cd)` of class `v` and `x = (px, lx, cx)` of the
other class (odd `X'`, `lx ≤ w`): the Q-form `nat.mul` (`MulHypQE`, window `kM`) and the continuation with `BF`, the
result `(p', l', c')` of class `v` holding `X'·powers[j]`, `l' ≤ 2w`, the operand unchanged, the slots and the budget.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

open FvModexp.Amd64.EvenHyp (RdIn WrOut)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem mulB {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kM : Nat} (hml : Q.DivRec.MulHypQE impl R ns kM) (hkM : kM ≤ K) (hkM1 : mulWX64 ≤ kM)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp tp : Nat} (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp)
    {v : Bool} {pd ld cd : Nat} (hd : BC R L K g sp st zp zc M L1 zzp tp lm v pd cd) (hcd : 0 < cd) (hld : ld ≤ cd)
    {px lx cx X' : Nat} (hx : BC R L K g sp st zp zc M L1 zzp tp lm (!v) px cx) (hxv : NV M px lx cx X')
    (hlx : lx ≤ W lm) {j ly : Nat} (hj : j < 4) (hly : M.readLE (sp + 0x140 + 24 * j + 8) 8 = ly)
    (hPo : Exp.p2Pow lm (natVal s.mem xp xl) j % 2 = 1) (hcost : mulCQ lx ly ≤ b1)
    {ret0 : W64} {Q : State → Prop} {idx : Nat} (hidx : idx < 0xa51)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6228032) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0) (hdf : T.df = false)
    (hm : T.mem = M) (hra : M.readLE (sp - 8) 8 = 6200864 + idx)
    (h0 : T.regs 0 = BitVec.ofNat 64 pd) (h3 : T.regs 3 = BitVec.ofNat 64 ld) (h1 : T.regs 1 = BitVec.ofNat 64 cd)
    (h7 : T.regs 7 = BitVec.ofNat 64 st) (h6 : T.regs 6 = BitVec.ofNat 64 px) (h8 : T.regs 8 = BitVec.ofNat 64 lx)
    (h9 : T.regs 9 = BitVec.ofNat 64 cx) (hy0 : M.readLE sp 8 = tp + 8 * (j * W lm)) (hy1 : M.readLE (sp + 8) 8 = ly)
    (hy2 : M.readLE (sp + 16) 8 = W lm)
    (KC : ∀ (s' : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat), s'.rip = BitVec.ofNat 64 (6200864 + idx) →
      s'.regs 4 = BitVec.ofNat 64 sp → s'.regs 5 = T.regs 5 → s'.regs 14 = T.regs 14 → s'.xmm 15 = 0 →
      s'.fsBase = s.fsBase → s'.df = false →
      s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 l' → s'.regs 1 = BitVec.ofNat 64 c' →
      BF R L K g sp st bp r zp zc xp xl xc yp yl lm s s'.mem L2 b2 zzp tp →
      (∀ a k, sp + 0x50 ≤ a → a + k ≤ sp + 0x230 → s'.mem.readLE a k = M.readLE a k) →
      BC R L K g sp st zp zc s'.mem L2 zzp tp lm v p' c' → NV s'.mem p' l' c' (X' * Exp.p2Pow lm (natVal s.mem xp xl) j) → l' ≤ 2 * W lm →
      BC R L K g sp st zp zc s'.mem L2 zzp tp lm (!v) px cx → NV s'.mem px lx cx X' →
      b1 - mulCQ lx ly ≤ b2 → ReachesRet (LibW.program.link impl) ret0 s' Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  obtain ⟨xlc, xv, xN, xo⟩ := hxv
  have hlx0 : 0 < lx := len_pos xv xo
  have hcx : 0 < cx := by omega
  have h88 : (88 : Nat) ≤ 88 := Nat.le_refl _
  obtain ⟨hce, hsv, hgl, hsi, hinv, hsN, hgN, hfsN⟩ := bodyEnv hP hB hsp h14 hfs hm hkM h88
  obtain ⟨dW, dS, -, -, -⟩ := BC.arg hP hB hd hcd hsN hgN hfsN hm hkM h88
  obtain ⟨-, -, xH, x48, xA⟩ := BC.arg hP hB hx hcx hsN hgN hfsN hm hkM h88
  obtain ⟨xR, xS⟩ := xA lx xlc
  have hdx := bc_apart hB hd hx hcd hcx
  have hdx' := hdx
  unfold Apart at hdx'
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.1; simp only [W]; omega
  have hl16 : stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 :=
    hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwt : Outside StackNat.wT 16 R.rt := hP.2.2.2.1
  have ewt : NatAdd.wordT = StackNat.wT := by decide
  have hlen := hB.wc.len
  have hlL := lL_bd (stLen s.mem st) lm
  have hdc40 := (BC.facts hP hB hd hcd).1
  have hxc40 := (BC.facts hP hB hx hcx).1
  have hst48 : st < 2 ^ 64 := by have := hB.wc.sok.2.2.2.1; omega
  have hd48 := ((BC.facts hP hB hd hcd).2.1 hcd).2.2.2
  have hx48 := ((BC.facts hP hB hx hcx).2.1 hcx).2.2.2
  have hrd : T.mem.readLE (T.regs 4).toNat 8 = 6200864 + idx := by rw [hsN, hm]; exact hra
  have hH := lvl_twin hlen (a := 2 * lx) (by omega)
  subst hm
  obtain ⟨-, -, yd2, yd3, -⟩ := hB.tz.pw j hj
  rw [hly] at yd2 yd3
  have yN : NatNorm T.mem (tp + 8 * (j * W lm)) ly := by
    have := (hB.tz.pw j hj).2.2.2.2; rw [hly] at this; exact this
  have eW : P2Pre.W lm = W lm := rfl
  rw [eW] at yd2 yd3
  obtain ⟨yR, yS, yH, y48, yc40⟩ := tbl_arg hP hB (j := j) (l := ly) hj yd2 hsN rfl hkM h88
  have hjW : (j + 1) * W lm ≤ P2Pre.NB 4 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : j * W lm + W lm ≤ P2Pre.NB 4 lm := by rw [← Nat.succ_mul]; exact hjW
  have hdb : Apart pd (8 * cd) tp (8 * P2Pre.NB 4 lm) := by
    cases v
    · obtain ⟨rfl, rfl⟩ := hd; exact hB.tz.zb
    · exact (hd.ap hcd).2.2.2.2.2.2
  have hdy : Apart pd (8 * cd) (tp + 8 * (j * W lm)) (8 * W lm) := by unfold Apart at hdb ⊢; omega
  have hW1 : 1 ≤ W lm := by have := hP.2.2.2.2.1; simp only [W]; omega
  have hdy' := hdy
  unfold Apart at hdy'
  have hH2 := lvl_twin hlen (a := lx + ly) (by omega)
  have hb48 := hB.tz.bscr.b48
  have hsp8 : 8 ≤ sp := by have := (hB.wc.cenv hP).2.1; have := hP.1.2.2.2.2.2.2.1; omega
  refine LibCalls.mulCallQ hap hns hml (HW (stLen s.mem st) lm) (b := b1 + stkR (HW (stLen s.mem st) lm) T.mem st)
    (L := L1) (ra_w2 hap hnf idx hidx) hpc hrd h0 h3 h1 h7 h6 h8 h9 hx15 hdf (by omega) (by omega) hst48 (by omega)
    (by omega) (by omega) (by rw [hsN, show sp - 8 + 8 = sp by omega]; exact hy0)
    (by rw [hsN, show sp - 8 + 16 = sp + 8 by omega]; exact hy1)
    (by rw [hsN, show sp - 8 + 24 = sp + 16 by omega]; exact hy2)
    ⟨hce, Nat.le_trans (mulW64_le_X (by omega) (by omega)) hkM1, hsv, hgl, by rw [ewt]; exact hwt,
      ⟨⟨xlc, hxc40, by omega, fun _ => xR.2.1, fun _ => ⟨xH, x48⟩, fun _ => ⟨xR.2.2.2.2, xS⟩⟩,
       ⟨yd2, yc40, by omega, fun _ => yR.2.1, fun _ => ⟨yH, by omega⟩, fun _ => ⟨yR.2.2.2.2, yS⟩⟩,
       ⟨hdc40, dW.2.1, (dW.2.2 hcd).1, fun _ => ⟨(dW.2.2 hcd).2.1, (dW.2.2 hcd).2.2, dS⟩,
        Or.inr fun _ _ => by unfold Apart; omega, Or.inr fun _ _ => by unfold Apart; omega⟩,
       by omega⟩,
      hsi, ⟨by omega, by omega⟩, by rw [hB.wc.fr.accessible]; exact hadx, hinv⟩
    fun s' hpc' hsp' h5' h14' hx15' hrg hpost => ?_
  obtain ⟨hfs', hdf', p', l', c', e0, e3, e1, hv', hn', hlc', hl2, hc40', L2, b', hLE, hbud', hinv', hlive', horg,
    hnew, hreu, hsbl, hF', hLF'⟩ := hpost
  simp only [win, hsN] at hreu
  simp only [win, hsN] at hF'
  rw [hgN] at hinv'
  have hb3 : ∃ b3, R.inv (b3 + stkR (HW (stLen s.mem st) lm) s'.mem st) L2 g (view R.rt L2 s'.mem) ∧
      b1 - mulCQ lx ly ≤ b3 :=
    ⟨b' - stkR (HW (stLen s.mem st) lm) s'.mem st, by rw [Nat.sub_add_cancel (by omega)]; exact hinv', by omega⟩
  obtain ⟨b3, hinv3, hbud3⟩ := hb3
  obtain ⟨hB', hslot, hkeep⟩ := BF.call hP hB hd hcd hkM h88 hF' hLF' hrg hLE hinv3 hsbl
  obtain ⟨hx', hxb⟩ := hkeep (!v) px cx hx hcx hdx.symm
  have hval : natVal s'.mem p' l' = X' * Exp.p2Pow lm (natVal s.mem xp xl) j := by rw [hv', xv, yd3]
  have hodd : X' * Exp.p2Pow lm (natVal s.mem xp xl) j % 2 = 1 := by rw [Nat.mul_mod, xo, hPo]
  have hacc : ∀ a n w, s'.mem.accessible a n w = T.mem.accessible a n w := hF'.accessible
  have hres : BC R L K g sp st zp zc s'.mem L2 zzp tp lm v p' c' := by
    cases v
    · obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨r0, r2, -⟩ := hreu (by omega) (end_ne hdx hcd hcx) (end_ne hdy hcd (by omega))
      exact ⟨r0, r2⟩
    · by_cases heq : p' = pd ∧ c' = cd
      · obtain ⟨rfl, rfl⟩ := heq
        exact UB.call hd hacc hLE hsbl.1
      · obtain ⟨-, hin, hap'⟩ := horg.resolve_left heq
        exact ub_res hP hB (by omega) hc40' hin hap' hlive' hLE hsbl.1 (hnew heq (by omega))
  have hsp2 : s'.regs 4 = BitVec.ofNat 64 sp := by
    rw [hsp', hsp]; apply BitVec.eq_of_toNat_eq
    have hce' := hB.wc.cenv hP
    have := hce'.2.2.1; have := hce'.2.1; have := hP.1.2.2.2.2.2.2.1
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; rw [show BitVec.toNat (8 : BitVec 64) = 8 from rfl]; omega
  exact KC s' L2 b3 p' l' c' hpc' hsp2 h5' h14' (hx15'.trans hx15) (hfs'.trans hfs) (hdf'.trans hdf) e0 e3 e1 hB'
    hslot hres ⟨hlc', hval, hn', hodd⟩ (by omega) hx' (NV.keep ⟨xlc, xv, xN, xo⟩ hxb) hbud3

end

end FvModexp.Amd64.P2W2
