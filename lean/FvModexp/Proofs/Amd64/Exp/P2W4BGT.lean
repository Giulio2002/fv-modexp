import FvModexp.Proofs.Amd64.Exp.P2W4BJ
import FvModexp.Proofs.Amd64.Exp.P2W4Seg

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the body's generic `trunc` step (agent divmc s77; amd64 twin of agent infra's
`Arm64.P2W4BGT`, generalising divmc's amd64 `P2W2.callB1`)

`callT`: at the `trunc` entry (`zz = zz.trunc(zz, logM)`, return `fn + idx`) from a join point
`JX pc v w Vr lrb Vo o1 o2 o3 rem` (a `sqr`/`mul` just returned `(pr, lr, cr)`): the continuation gets
`JX (fn + idx) v w (Vr mod 2^logM) W Vo o1 o2 o3 rem'` for any `rem' + tC ≤ rem`. `segT`: the five trunc segments
(`MOVQ AX, DI; BX, SI; CX, R8; [0x350], R9; CALL`, return = join pc + 0x16) as one lemma over the join pc.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the generic `trunc` call (`T` = the callee entry state) -/
theorem callT (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    {pc : Nat} {v w : Bool} {Vr lrb Vo o1 o2 o3 rem rem' idx : Nat} (hvw : v = !w) (hlrb : lrb ≤ 2 * W lm)
    (ho : 0x50 ≤ o1 ∧ o1 + 8 ≤ 0x358 ∧ 0x50 ≤ o2 ∧ o2 + 8 ≤ 0x358 ∧ 0x50 ≤ o3 ∧ o3 + 8 ≤ 0x358)
    (hrem : rem' + P2Pre.tC lm ≤ rem) (hidx : idx < 0xb11)
    (KT : KJ impl ret0 Q (JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
      (6197952 + idx) v w (Vr % 2 ^ lm) (W lm) Vo o1 o2 o3 rem'))
    {S0 : State} {M0 : Memory} {L1 : List (Nat × Nat)} {b1 po lo co pr lr cr : Nat}
    (h : JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u pc v w Vr lrb Vo
      o1 o2 o3 rem S0 M0 L1 b1 po lo co pr lr cr)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6188320) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (h5 : T.regs 5 = r5) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0)
    (hdf : T.df = false) (hm : T.mem = M0.writeLE (sp - 8) 8 (6197952 + idx))
    (h0 : T.regs 0 = BitVec.ofNat 64 pr) (h3 : T.regs 3 = BitVec.ofNat 64 lr) (h1 : T.regs 1 = BitVec.ofNat 64 cr)
    (h7 : T.regs 7 = BitVec.ofNat 64 pr) (h6 : T.regs 6 = BitVec.ofNat 64 lr) (h8 : T.regs 8 = BitVec.ofNat 64 cr)
    (h9 : T.regs 9 = BitVec.ofNat 64 lm) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hjc := h.jc
  obtain ⟨hB2, hrd2, hkeep2⟩ := BF.push hP hjc.bf (6197952 + idx)
  have hlo0 := len_pos h.no.2.1 h.no.2.2.2
  have hco : 0 < co := by have := h.no.1; omega
  have hcr : 0 < cr := by have := len_pos h.nr.2.1 h.nr.2.2.2; have := h.nr.1; omega
  obtain ⟨hO2, hOk2⟩ := hkeep2 w po co h.ro hco
  obtain ⟨hR2, hRk2⟩ := hkeep2 v pr cr h.rr hcr
  have hOn : NV (M0.writeLE (sp - 8) 8 (6197952 + idx)) po lo co Vo := NV.keep h.no hOk2
  have hRn : NV (M0.writeLE (sp - 8) 8 (6197952 + idx)) pr lr cr Vr := NV.keep h.nr hRk2
  have hrr : BC R L K g sp st zp zc M0 L1 zzp tp lm (!w) pr cr := hvw ▸ h.rr
  have hapO := bc_apart hjc.bf h.ro hrr hco hcr
  have hb := h.hb
  have hcb := hjc.hcb
  have hcst : P2Pre.tC lm ≤ b1 := by simp only [bodyB] at hb; omega
  have hra : (M0.writeLE (sp - 8) 8 (6197952 + idx)).readLE (sp - 8) 8 = 6197952 + idx := by
    rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have hW : W lm ≤ 128 := by have := hP.2.2.2.2.2.1; simp only [W]; omega
  have hlr := h.lrb
  rw [← hm] at hB2 hra hR2 hO2 hOn hRn hrd2
  refine trB hap hns hnf htr hkT haT hP hB2 (v := v) hR2 hRn (by omega) hcst hidx
    T hpc hsp h14 hfs hx15 hdf rfl hra h0 h3 h1 h7 h6 h8 h9 ?_
  intro s' L2 b2 l' hpc' hsp' h5' h14' hx15' hfs' hdf' e0 e3 e1 hB' hslot hres hnv hl' hk hbud
  obtain ⟨hO', hOk'⟩ := hk w po co hO2 hco hapO
  have q : ∀ a k, sp + 0x50 ≤ a → a + k ≤ sp + 0x358 → s'.mem.readLE a k = M0.readLE a k := fun a k h1 h2 =>
    (hslot a k h1 h2).trans (hrd2 a k (by omega))
  exact KT s' s'.mem L2 b2 po lo co pr l' cr
    { jc := hjc.call (hsp'.trans hjc.esp.symm) ((h14'.trans h14).trans hjc.e14.symm)
        ((h5'.trans h5).trans hjc.e5.symm) hfs' hx15' hdf' rfl hB' q
      epc := hpc', e0 := e0, e3 := e3, e1 := e1, rr := hres, nr := hnv, lrb := hl', ro := hO',
      no := NV.keep hOn hOk', lob := h.lob,
      so1 := (q _ _ (by omega) (by omega)).trans h.so1,
      so2 := (q _ _ (by omega) (by omega)).trans h.so2,
      so3 := (q _ _ (by omega) (by omega)).trans h.so3,
      hb := by simp only [bodyB] at hb hbud ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the trunc segments** `J(2k-1) → J(2k)` (join pc `fn + jp`, return `fn + jp + 0x16`) -/
theorem segT (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ K) (haT : aboveT ≤ 88)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {i c yi Z : Nat} {u : Bool}
    {jp : Nat} {v w : Bool} {Vr Vo o1 o2 o3 rem rem' : Nat}
    (hjp : jp = 0x686 ∨ jp = 0x6dc ∨ jp = 0x732 ∨ jp = 0x788 ∨ jp = 0x814) (hvw : v = !w)
    (ho : 0x50 ≤ o1 ∧ o1 + 8 ≤ 0x358 ∧ 0x50 ≤ o2 ∧ o2 + 8 ≤ 0x358 ∧ 0x50 ≤ o3 ∧ o3 + 8 ≤ 0x358)
    (hrem : rem' + P2Pre.tC lm ≤ rem)
    (KT : KJ impl ret0 Q (JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
      (6197952 + (jp + 0x16)) v w (Vr % 2 ^ lm) (W lm) Vo o1 o2 o3 rem')) :
    KJ impl ret0 Q (JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
      (6197952 + jp) v w Vr (2 * W lm) Vo o1 o2 o3 rem) := by
  intro S M L1 b1 po lo co pr lr cr h
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hce := h.jc.bf.wc.cenv hP
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hsp48 : sp - 8 + 0x360 ≤ 2 ^ 48 := hce.2.2.1
  have hwacc : M.accessible (sp - 8 - K) (K + 0x360) true = true := hce.2.2.2.1
  have hwaccF : M.accessible (sp - 8 - K) (K + 0x360) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have q350 : M.readLE (sp + 0x350) 8 = lm := h.jc.bf.esl.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hH : HdM (JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u (6197952 + jp) v w
    Vr (2 * W lm) Vo o1 o2 o3 rem S M L1 b1 po lo co pr lr cr) := ⟨h⟩
  have epc := h.epc
  have esp := h.jc.esp
  have e14 := h.jc.e14
  have e5 := h.jc.e5
  have efs := h.jc.efs
  have ex := h.jc.ex
  have edf := h.jc.edf
  have e0 := h.e0
  have e3 := h.e3
  have e1 := h.e1
  have em := h.jc.em
  clear h hce
  have hPH : HdM (EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) := ⟨hP⟩
  clear hP
  subst em
  rcases hjp with rfl | rfl | rfl | rfl | rfl
  all_goals
    refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 6188320) ?_
    janus64_run [q350, hwacc, hwaccF] until [6188320]
    refine callT hap hns hnf htr hkT haT hPH.h hvw (Nat.le_refl _) ho hrem (by decide) KT hH.h _ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | exact efs
      | (janus64_simp; done)
      | (janus64_simp; exact bv_sub8 (by omega) (by omega))

end

end FvModexp.Amd64.P2W4
