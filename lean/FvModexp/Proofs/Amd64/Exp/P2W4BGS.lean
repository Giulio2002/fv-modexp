import FvModexp.Proofs.Amd64.Exp.P2W4BJ
import FvModexp.Proofs.Amd64.Exp.P2W4Seg

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the body's generic `sqr` step (agent divmc s77; amd64 twin of agent infra's
`Arm64.P2W4BGS`, generalising divmc's amd64 `P2W2.callB2`)

`callS`: at the `nat.sqr` entry (`zz = zz.sqr(stk, z)`, return `fn + idx`) from a join point
`JX pc v w Vr W Vo o1 o2 o3 rem` (a `trunc` just returned `z = (pr, lr, cr)`; the destination `zz` is the other
buffer `(po, lo, co)`), after the spills of `z` to `n1/n2/n3` (`NS`: `0x2e0/0xe8/0x70` or `0x120/0x68/0xd8`): the
continuation gets `JX (fn + idx) w v (Vr²) 2W Vr n1 n2 n3 rem'` for any `rem' + sqr ≤ rem`. `segS`: the three sqr
segments `J2 → J3`, `J4 → J5`, `J6 → J7` (spill `AX, BX, CX`, `DI := [0x330]`, `x := AX, BX, CX`, `zz` reloaded from
`o1/o2/o3`, `CALL`; return = join pc + 0x40) as one lemma.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- the two spill triples of the body -/
@[reducible] def NS (n1 n2 n3 : Nat) : Prop := (n1 = 0x2e0 ∧ n2 = 0xe8 ∧ n3 = 0x70) ∨ (n1 = 0x120 ∧ n2 = 0x68 ∧ n3 = 0xd8)

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the generic `sqr` call from the spills' memory (`T` = the callee entry state) -/
theorem callS (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS : kS ≤ K) (hkS1 : sqrW 128 ≤ kS)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) {i c yi Z : Nat} {u : Bool}
    {pc : Nat} {v w : Bool} {Vr Vo o1 o2 o3 n1 n2 n3 rem rem' idx : Nat} (hvw : v = !w) (hn : NS n1 n2 n3)
    (hrem : rem' + sqrCQ (W lm) ≤ rem) (hidx : idx < 0xb11)
    (KS : KJ impl ret0 Q (JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
      (6197952 + idx) w v (Vr * Vr) (2 * W lm) Vr n1 n2 n3 rem'))
    {S0 : State} {M0 : Memory} {L1 : List (Nat × Nat)} {b1 po lo co pr lr cr : Nat}
    (h : JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u pc v w Vr (W lm) Vo
      o1 o2 o3 rem S0 M0 L1 b1 po lo co pr lr cr)
    {M1 : Memory} (hF : MemFrame M0 M1 [(sp + n1, sp + n1 + 8), (sp + n2, sp + n2 + 8), (sp + n3, sp + n3 + 8)])
    (hrg : M1.regions = M0.regions)
    (rn1 : M1.readLE (sp + n1) 8 = pr) (rn2 : M1.readLE (sp + n2) 8 = lr) (rn3 : M1.readLE (sp + n3) 8 = cr)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6229984) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (h5 : T.regs 5 = r5) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0)
    (hdf : T.df = false) (hm : T.mem = M1.writeLE (sp - 8) 8 (6197952 + idx))
    (h0 : T.regs 0 = BitVec.ofNat 64 po) (h3 : T.regs 3 = BitVec.ofNat 64 lo) (h1 : T.regs 1 = BitVec.ofNat 64 co)
    (h7 : T.regs 7 = BitVec.ofNat 64 st) (h6 : T.regs 6 = BitVec.ofNat 64 pr) (h8 : T.regs 8 = BitVec.ofNat 64 lr)
    (h9 : T.regs 9 = BitVec.ofNat 64 cr) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hjc := h.jc
  obtain ⟨hB, hrd, hkeep⟩ := BF.win hP hjc.bf hF hrg (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hq with rfl | rfl | rfl <;> simp only [SW] <;> omega)
  obtain ⟨hB2, hrd2, hkeep2⟩ := BF.push hP hB (6197952 + idx)
  have hlo0 := len_pos h.no.2.1 h.no.2.2.2
  have hco : 0 < co := by have := h.no.1; omega
  have hlr0 := len_pos h.nr.2.1 h.nr.2.2.2
  have hcr : 0 < cr := by have := h.nr.1; omega
  obtain ⟨hO, -⟩ := hkeep w po co h.ro hco
  obtain ⟨hO2, -⟩ := hkeep2 w po co hO hco
  obtain ⟨hR1, hRk⟩ := hkeep v pr cr h.rr hcr
  obtain ⟨hR2, hRk2⟩ := hkeep2 v pr cr hR1 hcr
  have hRn : NV (M1.writeLE (sp - 8) 8 (6197952 + idx)) pr lr cr Vr :=
    NV.keep h.nr fun a k a1 a2 => (hRk2 a k a1 a2).trans (hRk a k a1 a2)
  have hmono := sqrCQ_mono h.lrb
  have hb := h.hb
  have hcb := hjc.hcb
  have hcst : sqrCQ lr ≤ b1 := by simp only [bodyB] at hb; omega
  have hra : (M1.writeLE (sp - 8) 8 (6197952 + idx)).readLE (sp - 8) 8 = 6197952 + idx := by
    rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have hsl : ∀ a, (a = sp + 0xc8 ∨ a = sp + 0xd0 ∨ a = sp + 0xf0 ∨ a = sp + 0x98) →
      (M1.writeLE (sp - 8) 8 (6197952 + idx)).readLE a 8 = M0.readLE a 8 :=
    fun a ha => (hrd2 a 8 (by omega)).trans (hF.readLE a 8 (by
      rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases ha with rfl | rfl | rfl | rfl <;> simp only [outside_cons, outside_nil, and_true] <;> omega))
  rw [← hm] at hB2 hra hR2 hO2 hRn hsl hrd2
  refine sqrB hap hns hnf hsq hkS hkS1 hP hadx hB2 (v := w) hO2 hco h.no.1 (hvw ▸ hR2) hRn h.lrb hcst
    hidx T hpc hsp h14 hfs hx15 hdf rfl hra h0 h3 h1 h7 h6 h8 h9 ?_
  intro s' L2 b2 p' l' c' hpc' hsp' h5' h14' hx15' hfs' hdf' e0 e3 e1 hB' hslot hres hnv hl' hx hxn hbud
  have q : ∀ a, sp + 0x50 ≤ a → a + 8 ≤ sp + 0x358 → s'.mem.readLE a 8 = M1.readLE a 8 := fun a h1 h2 =>
    (hslot a 8 h1 h2).trans (hrd2 a 8 (by omega))
  have q0 : ∀ a, (a = sp + 0xc8 ∨ a = sp + 0xd0 ∨ a = sp + 0xf0 ∨ a = sp + 0x98) →
      s'.mem.readLE a 8 = M0.readLE a 8 := fun a ha => (hslot a 8 (by omega) (by omega)).trans (hsl a ha)
  have hn' : 0x50 ≤ n1 ∧ n1 + 8 ≤ 0x358 ∧ 0x50 ≤ n2 ∧ n2 + 8 ≤ 0x358 ∧ 0x50 ≤ n3 ∧ n3 + 8 ≤ 0x358 := by
    rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
  exact KS s' s'.mem L2 b2 pr lr cr p' l' c'
    { jc := ⟨hsp', h14'.trans h14, h5'.trans h5, hfs', hx15', hdf', rfl, hB',
        (q0 _ (Or.inl rfl)).trans hjc.sc0, (q0 _ (Or.inr (Or.inl rfl))).trans hjc.sc8,
        (q0 _ (Or.inr (Or.inr (Or.inl rfl)))).trans hjc.sf0, (q0 _ (Or.inr (Or.inr (Or.inr rfl)))).trans hjc.s98,
        hjc.hi, hjc.hyi, hjc.hc, hjc.hu, hjc.hfv, hcb⟩
      epc := hpc', e0 := e0, e3 := e3, e1 := e1, rr := hres, nr := hnv, lrb := hl', ro := hvw ▸ hx, no := hxn,
      lob := h.lrb, so1 := (q _ (by omega) (by omega)).trans rn1, so2 := (q _ (by omega) (by omega)).trans rn2,
      so3 := (q _ (by omega) (by omega)).trans rn3,
      hb := by simp only [bodyB] at hb hmono ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the sqr segments** `J(2k) → J(2k+1)` (`k = 1, 2, 3`; join pc `fn + jp`, return `fn + jp + 0x40`) -/
theorem segS (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS : kS ≤ K) (hkS1 : sqrW 128 ≤ kS)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) {i c yi Z : Nat} {u : Bool}
    {jp : Nat} {v w : Bool} {Vr Vo o1 o2 o3 n1 n2 n3 rem rem' : Nat} (hvw : v = !w)
    (hjp : (jp = 0x69c ∧ n1 = 0x2e0 ∧ n2 = 0xe8 ∧ n3 = 0x70 ∧ o1 = 0x120 ∧ o2 = 0x68 ∧ o3 = 0xe0) ∨
      (jp = 0x6f2 ∧ n1 = 0x120 ∧ n2 = 0x68 ∧ n3 = 0xd8 ∧ o1 = 0x2e0 ∧ o2 = 0xe8 ∧ o3 = 0x70) ∨
      (jp = 0x748 ∧ n1 = 0x2e0 ∧ n2 = 0xe8 ∧ n3 = 0x70 ∧ o1 = 0x120 ∧ o2 = 0x68 ∧ o3 = 0xd8))
    (hrem : rem' + sqrCQ (W lm) ≤ rem)
    (KS : KJ impl ret0 Q (JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
      (6197952 + (jp + 0x40)) w v (Vr * Vr) (2 * W lm) Vr n1 n2 n3 rem')) :
    KJ impl ret0 Q (JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u
      (6197952 + jp) v w Vr (W lm) Vo o1 o2 o3 rem) := by
  intro S M L1 b1 po lo co pr lr cr h
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hce := h.jc.bf.wc.cenv hP
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hsp48 : sp - 8 + 0x360 ≤ 2 ^ 48 := hce.2.2.1
  have hwacc : M.accessible (sp - 8 - K) (K + 0x360) true = true := hce.2.2.2.1
  have hwaccF : M.accessible (sp - 8 - K) (K + 0x360) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have q330 : M.readLE (sp + 0x330) 8 = st := h.jc.bf.esl.2.2.2.2.2.2.2.2.1
  have hcr : 0 < cr := by have := len_pos h.nr.2.1 h.nr.2.2.2; have := h.nr.1; omega
  have hrf := BC.facts hP h.jc.bf h.rr hcr
  have hcr40 : cr < 2 ^ 40 := hrf.1
  have hpr : pr + 8 * cr ≤ 2 ^ 48 := (hrf.2.1 hcr).2.2.2
  have hlrc : lr ≤ cr := h.nr.1
  clear hrf
  have qo1 := h.so1
  have qo2 := h.so2
  have qo3 := h.so3
  have hH : HdM (JX R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u (6197952 + jp) v w
    Vr (W lm) Vo o1 o2 o3 rem S M L1 b1 po lo co pr lr cr) := ⟨h⟩
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
  rcases hjp with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals
    refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 6229984) ?_
    janus64_run [q330, qo1, qo2, qo3, hwacc, hwaccF] until [6229984]
    refine callS hap hns hnf hsq hkS hkS1 hPH.h hadx hvw (by first | exact Or.inl ⟨rfl, rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl, rfl⟩) hrem (by decide) KS hH.h
      ?hF ?hrg ?r1 ?r2 ?r3 _ ?_ ?hsp ?_ ?_ ?hfs ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case hF => janus_frame
    case hrg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case hfs => exact efs
    case hsp => janus64_simp; exact bv_sub8 (by omega) (by omega)
    case r1 =>
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
    case r2 =>
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
    case r3 =>
      rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
    all_goals (janus64_simp; done)

end

end FvModexp.Amd64.P2W4
