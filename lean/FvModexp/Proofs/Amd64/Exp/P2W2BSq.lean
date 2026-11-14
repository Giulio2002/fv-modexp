import FvModexp.Proofs.Amd64.Exp.P2W2BA
import FvModexp.Proofs.Amd64.Exp.P2W2R1b
import FvModexp.Proofs.Amd64.Exp.LibCallsQ
import FvModexp.Proofs.Amd64.Exp.P2W2N

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): a loop-body `z = z.sqr(stk, x)` call (agent divmc s72; amd64 twin of agent
infra's `Arm64.P2W2BSq`)

* `BF.push`: `BF`, the buffer classes and their bytes through a `CALL`'s return-address push at `[sp - 8]`.
* `sqrB`: at the `nat.sqr` entry (`RSP = sp - 8`, `[sp - 8]` = the return address `fn + idx`) with the destination
  `(pd, ld, cd)` a buffer of class `v` and the operand `x = (px, lx, cx)` of the other class (odd value `X'`,
  `lx ≤ w`): divmc's Q-form callee (`SqrE`, window `kS`, reserve level `HW`) and the continuation with `BF` at the
  result memory, the result `(p', l', c')` of class `v` (the S buffer is always reused: `2 lx ≤ 2 w`; a U buffer is
  reused or replaced by a fresh one), value `X'²`, `l' ≤ 2w`, the operand unchanged, the slots `[sp + 0x50,
  sp + 0x230)` and the budget.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

open FvModexp.Amd64.EvenHyp (RdIn WrOut)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep)

/-- value and normal form of `p[0:l]` through a step keeping its bytes -/
theorem nv_keep {M M' : Memory} {p l : Nat}
    (hk : ∀ a k, p ≤ a → a + k ≤ p + 8 * l → M'.readLE a k = M.readLE a k) :
    natVal M' p l = natVal M p l ∧ (NatNorm M p l → NatNorm M' p l) := by
  refine ⟨hk p (8 * l) (Nat.le_refl _) (Nat.le_refl _), fun h => ?_⟩
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact Or.inl h0
  rcases h with h | h
  · exact Or.inl h
  · right; rw [hk _ _ (by omega) (by omega)]; exact h

/-- a nat of odd value has a positive length -/
theorem len_pos {M : Memory} {p l Z : Nat} (hv : natVal M p l = Z) (hz : Z % 2 = 1) : 0 < l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · subst h0; simp at hv; omega
  · exact h0

/-- two non-empty apart ranges have different ends -/
theorem end_ne {p c q d : Nat} (h : Apart p (8 * c) q (8 * d)) (hc : 0 < c) (hd : 0 < d) :
    p + 8 * c ≠ q + 8 * d := by unfold Apart at h; omega

/-- `NV` through a step keeping the bytes of the nat -/
theorem NV.keep {M M' : Memory} {p l c v : Nat} (h : NV M p l c v)
    (hk : ∀ a k, p ≤ a → a + k ≤ p + 8 * c → M'.readLE a k = M.readLE a k) : NV M' p l c v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨e, n⟩ := nv_keep (M := M) (M' := M') (p := p) (l := l) fun a k a1 a2 => hk a k a1 (by omega)
  exact ⟨h1, e.trans h2, n h3, h4⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `BF` and every buffer (class, bytes) through the return-address push `[sp - 8] := v` of a `CALL` -/
theorem BF.push (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp tp : Nat} (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) (v : Nat) :
    BF R L K g sp st bp r zp zc xp xl xc yp yl lm s (M.writeLE (sp - 8) 8 v) L1 b1 zzp tp ∧
    (∀ a k, sp ≤ a → (M.writeLE (sp - 8) 8 v).readLE a k = M.readLE a k) ∧
    (∀ (w : Bool) (q c : Nat), BC R L K g sp st zp zc M L1 zzp tp lm w q c → 0 < c →
      BC R L K g sp st zp zc (M.writeLE (sp - 8) 8 v) L1 zzp tp lm w q c ∧
        ∀ a k, q ≤ a → a + k ≤ q + 8 * c → (M.writeLE (sp - 8) 8 v).readLE a k = M.readLE a k) := by
  obtain ⟨hw, he⟩ := wc_push hP hB.wc hB.esl v
  have hce := hB.wc.cenv hP
  have hK0 : K ≤ sp - 8 := hce.2.1
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hwr : MemFrame M (M.writeLE (sp - 8) 8 v) [(sp - 8, sp)] := by janus_frame
  have hacc : ∀ a n w, (M.writeLE (sp - 8) 8 v).accessible a n w = M.accessible a n w := hwr.accessible
  have hstw : Apart st 24 (sp - 8 - K) (K + 0x238) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have e0 : stW (M.writeLE (sp - 8) 8 v) st = stW M st :=
    hwr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have e1 : stLen (M.writeLE (sp - 8) 8 v) st = stLen M st :=
    hwr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have e2 : stCap (M.writeLE (sp - 8) 8 v) st = stCap M st :=
    hwr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hbW := scr_win hP hB.tz.bscr
  unfold Apart at hbW
  refine ⟨⟨hw, he, hB.tz.keep hacc (LiveExt.refl R L1) e0 e1 e2 fun a k ha => hwr.readLE a k ?_⟩,
    fun a k ha => hwr.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega),
    fun w q c hq hc => ⟨?_, fun a k h1 h2 => hwr.readLE a k ?_⟩⟩
  · simp only [outside_cons, outside_nil, and_true]; omega
  · cases w
    · exact hq
    · exact UB.keep hq hacc (LiveExt.refl R L1) e0 e1 e2
  · have := (BC.facts hP hB hq hc).2.2.1
    unfold Apart at this
    simp only [outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem sqrB {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS : kS ≤ K) (hkS1 : sqrW 128 ≤ kS)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) {M : Memory} {L1 : List (Nat × Nat)}
    {b1 zzp tp : Nat} (hB : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp)
    {v : Bool} {pd ld cd : Nat} (hd : BC R L K g sp st zp zc M L1 zzp tp lm v pd cd) (hcd : 0 < cd) (hld : ld ≤ cd)
    {px lx cx X' : Nat} (hx : BC R L K g sp st zp zc M L1 zzp tp lm (!v) px cx) (hxv : NV M px lx cx X')
    (hlx : lx ≤ W lm) (hcost : sqrCQ lx ≤ b1)
    {ret0 : W64} {Q : State → Prop} {idx : Nat} (hidx : idx < 0xa51)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6229984) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0) (hdf : T.df = false)
    (hm : T.mem = M) (hra : M.readLE (sp - 8) 8 = 6200864 + idx)
    (h0 : T.regs 0 = BitVec.ofNat 64 pd) (h3 : T.regs 3 = BitVec.ofNat 64 ld) (h1 : T.regs 1 = BitVec.ofNat 64 cd)
    (h7 : T.regs 7 = BitVec.ofNat 64 st) (h6 : T.regs 6 = BitVec.ofNat 64 px) (h8 : T.regs 8 = BitVec.ofNat 64 lx)
    (h9 : T.regs 9 = BitVec.ofNat 64 cx)
    (KC : ∀ (s' : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat), s'.rip = BitVec.ofNat 64 (6200864 + idx) →
      s'.regs 4 = BitVec.ofNat 64 sp → s'.regs 5 = T.regs 5 → s'.regs 14 = T.regs 14 → s'.xmm 15 = 0 →
      s'.fsBase = s.fsBase → s'.df = false →
      s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 l' → s'.regs 1 = BitVec.ofNat 64 c' →
      BF R L K g sp st bp r zp zc xp xl xc yp yl lm s s'.mem L2 b2 zzp tp →
      (∀ a k, sp + 0x50 ≤ a → a + k ≤ sp + 0x230 → s'.mem.readLE a k = M.readLE a k) →
      BC R L K g sp st zp zc s'.mem L2 zzp tp lm v p' c' → NV s'.mem p' l' c' (X' * X') → l' ≤ 2 * W lm →
      BC R L K g sp st zp zc s'.mem L2 zzp tp lm (!v) px cx → NV s'.mem px lx cx X' →
      b1 - sqrCQ lx ≤ b2 → ReachesRet (LibW.program.link impl) ret0 s' Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  obtain ⟨xlc, xv, xN, xo⟩ := hxv
  have hlx0 : 0 < lx := len_pos xv xo
  have hcx : 0 < cx := by omega
  have h64 : (64 : Nat) ≤ 88 := by decide
  obtain ⟨hce, hsv, hgl, hsi, hinv, hsN, hgN, hfsN⟩ := bodyEnv hP hB hsp h14 hfs hm hkS h64
  obtain ⟨dW, dS, -, -, -⟩ := BC.arg hP hB hd hcd hsN hgN hfsN hm hkS h64
  obtain ⟨-, -, xH, x48, xA⟩ := BC.arg hP hB hx hcx hsN hgN hfsN hm hkS h64
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
  refine LibCalls.sqrCallQ hap hns hsq (HW (stLen s.mem st) lm) (b := b1 + stkR (HW (stLen s.mem st) lm) T.mem st)
    (L := L1) (ra_w2 hap hnf idx hidx) hpc hrd h0 h3 h1 h7 h6 h8 h9 hx15 hdf (by omega) (by omega) hst48 (by omega)
    (by omega) (by omega)
    ⟨hce, by unfold sqrW ksqrW at hkS1 ⊢; omega, hsv, hgl, by rw [ewt]; exact hwt, xlc, hxc40,
      by omega, xR.2.1, fun _ => ⟨xH, x48⟩, fun _ => xR.2.2.2.2, hdc40, dW.2.1, (dW.2.2 hcd).1,
      fun _ => ⟨(dW.2.2 hcd).2.1, (dW.2.2 hcd).2.2, dS⟩, Or.inr fun _ _ => by unfold Apart; omega, hsi, fun _ => xS,
      by omega, ⟨by omega, by omega⟩, by rw [hB.wc.fr.accessible]; exact hadx, hinv⟩
    fun s' hpc' hsp' h5' h14' hx15' hrg hpost => ?_
  obtain ⟨hfs', hdf', p', l', c', e0, e3, e1, hv', hn', hlc', hl2, hc40', L2, b', hLE, hbud', hinv', hlive', horg,
    hnew, hreu, hsbl, hF', hLF'⟩ := hpost
  simp only [win, hsN] at hF'
  rw [hgN] at hinv'
  have hb3 : ∃ b3, R.inv (b3 + stkR (HW (stLen s.mem st) lm) s'.mem st) L2 g (view R.rt L2 s'.mem) ∧
      b1 - sqrCQ lx ≤ b3 :=
    ⟨b' - stkR (HW (stLen s.mem st) lm) s'.mem st, by rw [Nat.sub_add_cancel (by omega)]; exact hinv', by omega⟩
  obtain ⟨b3, hinv3, hbud3⟩ := hb3
  obtain ⟨hB', hslot, hkeep⟩ := BF.call hP hB hd hcd hkS h64 hF' hLF' hrg hLE hinv3 hsbl
  obtain ⟨hx', hxb⟩ := hkeep (!v) px cx hx hcx hdx.symm
  have hval : natVal s'.mem p' l' = X' * X' := by rw [hv', xv]
  have hodd : X' * X' % 2 = 1 := by rw [Nat.mul_mod, xo]
  have hacc : ∀ a n w, s'.mem.accessible a n w = T.mem.accessible a n w := hF'.accessible
  have hres : BC R L K g sp st zp zc s'.mem L2 zzp tp lm v p' c' := by
    cases v
    · obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨r0, r2, -⟩ := hreu (by omega) (end_ne hdx hcd hcx)
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
