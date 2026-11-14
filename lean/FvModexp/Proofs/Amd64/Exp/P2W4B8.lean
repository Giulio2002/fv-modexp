import FvModexp.Proofs.Amd64.Exp.P2W4BJ
import FvModexp.Proofs.Amd64.Exp.P2W4Seg
import FvModexp.Proofs.Amd64.Exp.P2W4Cp3

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): loop body segment B8 — `J8` → `mul` → `J9` (agent divmc s77, port of divmc s73; amd64 twin of
agent infra's `Arm64.P2W4B8`)

From the `trunc` return fn+0x79e: the stores `0x120/0x68/0xd8 := Z4 = (AX, BX, CX)`, `d = [0x98] >> 60`, the header
`powers[d]` (`[sp + 0x148 + 24 d …]`) stored as the stack argument `[sp], [sp + 0x8], [sp + 0x10]`, `DI := stk`,
`SI, R8, R9 := Z4`, `AX, BX, CX := [0x2e0], [0xe8], [0x70]` (= the `Z3` buffer), `zz = zz.mul(stk, z, powers[d])`
(nat.go:1100; `CALL` at fn+0x80f, return fn+0x814).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

theorem shr60 (yi : Nat) (hyi : yi < 2 ^ 64) : BitVec.ofNat 64 yi >>> 60 = BitVec.ofNat 64 (dOf yi) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, dOf]
  omega

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the `mul` call from the stores' memory (`T` = the callee entry state) -/
theorem callB8 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kM : Nat} (hml : FvModexp.Amd64.Q.DivRec.MulHypQE impl R ns kM) (hkM : kM ≤ K) (hkM1 : mulWX64 ≤ kM)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hX : natVal s.mem xp xl % 2 = 1)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) {i c yi Z : Nat} {u : Bool}
    (K9 : KJ impl ret0 Q (J9 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u))
    {S0 : State} {M0 : Memory} {L1 : List (Nat × Nat)} {b1 p1 l1 c1 p2 l2 c2 : Nat}
    (h : J8 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S0 M0 L1 b1 p1 l1 c1 p2 l2
      c2)
    {M1 : Memory} (hF : MemFrame M0 M1 [(sp + 0x120, sp + 0x120 + 8), (sp + 0x68, sp + 0x68 + 8), (sp + 0xd8, sp + 0xd8 + 8),
      (sp, sp + 0x8), (sp + 0x8, sp + 0x8 + 8), (sp + 0x10, sp + 0x10 + 8)]) (hrg : M1.regions = M0.regions)
    (r118 : M1.readLE (sp + 0x120) 8 = p2) (r68 : M1.readLE (sp + 0x68) 8 = l2) (rd0 : M1.readLE (sp + 0xd8) 8 = c2)
    (r0 : M1.readLE sp 8 = M0.readLE (sp + 0x148 + 24 * dOf yi) 8)
    (r8 : M1.readLE (sp + 0x8) 8 = M0.readLE (sp + 0x148 + 24 * dOf yi + 8) 8)
    (r16 : M1.readLE (sp + 0x10) 8 = M0.readLE (sp + 0x148 + 24 * dOf yi + 16) 8)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6228032) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 0x8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (h5 : T.regs 5 = r5) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0)
    (hdf : T.df = false) (hm : T.mem = M1.writeLE (sp - 0x8) 8 6200020)
    (h0 : T.regs 0 = BitVec.ofNat 64 p1) (h3 : T.regs 3 = BitVec.ofNat 64 l1) (h1 : T.regs 1 = BitVec.ofNat 64 c1)
    (h7 : T.regs 7 = BitVec.ofNat 64 st) (h6 : T.regs 6 = BitVec.ofNat 64 p2) (h8 : T.regs 8 = BitVec.ofNat 64 l2)
    (h9 : T.regs 9 = BitVec.ofNat 64 c2) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hjc := h.jc
  have hyi := hjc.hyi
  have hj : dOf yi < 16 := by simp only [dOf]; omega
  obtain ⟨t0, t2, t1, -, -⟩ := hjc.bf.tz.pw (dOf yi) hj
  have eW : P2Pre.W lm = W lm := rfl
  rw [eW] at t0 t2 t1
  obtain ⟨hB, hrd, hkeep⟩ := BF.win hP hjc.bf hF hrg (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [SW] <;> omega)
  obtain ⟨hB2, hrd2, hkeep2⟩ := BF.push hP hB 6200020
  have hl2 := len_pos h.nr.2.1 h.nr.2.2.2
  have hc2 : 0 < c2 := by have := h.nr.1; omega
  have hl1 := len_pos h.no.2.1 h.no.2.2.2
  have hc1 : 0 < c1 := by have := h.no.1; omega
  obtain ⟨h21, h2k⟩ := hkeep u p2 c2 h.rr hc2
  obtain ⟨h22, h2k2⟩ := hkeep2 u p2 c2 h21 hc2
  obtain ⟨h11, -⟩ := hkeep (!u) p1 c1 h.ro hc1
  obtain ⟨h12, -⟩ := hkeep2 (!u) p1 c1 h11 hc1
  have h2n : NV (M1.writeLE (sp - 0x8) 8 6200020) p2 l2 c2 (Z4 lm Z) :=
    NV.keep h.nr fun a k a1 a2 => (h2k2 a k a1 a2).trans (h2k a k a1 a2)
  have hly : (M1.writeLE (sp - 0x8) 8 6200020).readLE (sp + 0x148 + 24 * dOf yi + 8) 8 =
      M0.readLE (sp + 0x148 + 24 * dOf yi + 8) 8 := (hrd2 _ _ (by omega)).trans (hrd _ _ (by omega))
  have hy0 : (M1.writeLE (sp - 0x8) 8 6200020).readLE sp 8 = tp + 8 * (dOf yi * W lm) :=
    (hrd2 _ _ (by omega)).trans (r0.trans t0)
  have hy1 : (M1.writeLE (sp - 0x8) 8 6200020).readLE (sp + 0x8) 8 = M0.readLE (sp + 0x148 + 24 * dOf yi + 8) 8 :=
    (hrd2 _ _ (by omega)).trans r8
  have hy2 : (M1.writeLE (sp - 0x8) 8 6200020).readLE (sp + 0x10) 8 = W lm :=
    (hrd2 _ _ (by omega)).trans (r16.trans t2)
  have hmono := mulCQ_mono h.lrb t1
  have hb := h.hb
  have hcb := hjc.hcb
  have hcst : mulCQ l2 (M0.readLE (sp + 0x148 + 24 * dOf yi + 8) 8) ≤ b1 := by simp only [bodyB] at hb; omega
  have hPo := p2Pow_odd lm (natVal s.mem xp xl) (dOf yi) (by have := hP.2.2.2.2.1; omega) hX
  have hra : (M1.writeLE (sp - 0x8) 8 6200020).readLE (sp - 0x8) 8 = 6197952 + 0x814 :=
    Janus.Arm64.Memory.readLE_writeLE_self ..
  have hsl : ∀ a, (a = sp + 0xc8 ∨ a = sp + 0xd0 ∨ a = sp + 0xf0 ∨ a = sp + 0x98) →
      (M1.writeLE (sp - 0x8) 8 6200020).readLE a 8 = M0.readLE a 8 :=
    fun a ha => (hrd2 a 8 (by omega)).trans (hF.readLE a 8 (by
      rcases ha with rfl | rfl | rfl | rfl <;> simp only [outside_cons, outside_nil, and_true] <;> omega))
  rw [← hm] at hB2 hra h12 h22 h2n hsl hrd2 hly hy0 hy1 hy2
  refine mulB hap hns hnf hml hkM hkM1 hP hadx hB2 (v := !u) h12 hc1 h.no.1 (by rw [Bool.not_not]; exact h22) h2n
    h.lrb hj hly hPo hcst (idx := 0x814) (by decide) T hpc hsp h14 hfs hx15 hdf rfl hra h0 h3 h1 h7 h6 h8 h9 hy0 hy1
    hy2 ?_
  intro s' L2 b2 p' l' c' hpc' hsp' h5' h14' hx15' hfs' hdf' e0 e3 e1 hB' hslot hres hnv hl' hx hxn hbud
  rw [Bool.not_not] at hx
  have q : ∀ a, sp + 0x50 ≤ a → a + 8 ≤ sp + 0x358 → s'.mem.readLE a 8 = M1.readLE a 8 := fun a h1 h2 =>
    (hslot a 8 h1 h2).trans (hrd2 a 8 (by omega))
  have q0 : ∀ a, (a = sp + 0xc8 ∨ a = sp + 0xd0 ∨ a = sp + 0xf0 ∨ a = sp + 0x98) →
      s'.mem.readLE a 8 = M0.readLE a 8 := fun a ha => (hslot a 8 (by omega) (by omega)).trans (hsl a ha)
  exact K9 s' s'.mem L2 b2 p2 l2 c2 p' l' c'
    { jc := ⟨hsp', h14'.trans h14, h5'.trans h5, hfs', hx15', hdf', rfl, hB',
        (q0 _ (Or.inl rfl)).trans hjc.sc0, (q0 _ (Or.inr (Or.inl rfl))).trans hjc.sc8,
        (q0 _ (Or.inr (Or.inr (Or.inl rfl)))).trans hjc.sf0, (q0 _ (Or.inr (Or.inr (Or.inr rfl)))).trans hjc.s98,
        hjc.hi, hjc.hyi, hjc.hc, hjc.hu, hjc.hfv, hcb⟩
      epc := hpc', e0 := e0, e3 := e3, e1 := e1, rr := hres, nr := hnv, lrb := hl', ro := hx, no := hxn,
      lob := h.lrb, so1 := (q _ (by omega) (by omega)).trans r118, so2 := (q _ (by omega) (by omega)).trans r68,
      so3 := (q _ (by omega) (by omega)).trans rd0,
      hb := by simp only [bodyB] at hb hmono ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B8** -/
theorem segB8 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kM : Nat} (hml : FvModexp.Amd64.Q.DivRec.MulHypQE impl R ns kM) (hkM : kM ≤ K) (hkM1 : mulWX64 ≤ kM)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hX : natVal s.mem xp xl % 2 = 1)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) {i c yi Z : Nat} {u : Bool}
    (K9 : KJ impl ret0 Q (J9 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u)) :
    KJ impl ret0 Q (J8 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u) := by
  intro S M L1 b1 p1 l1 c1 p2 l2 c2 h
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hce := h.jc.bf.wc.cenv hP
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hsp48 : sp - 0x8 + 0x360 ≤ 2 ^ 48 := hce.2.2.1
  have hwacc : M.accessible (sp - 0x8 - K) (K + 0x360) true = true := hce.2.2.2.1
  have hwaccF : M.accessible (sp - 0x8 - K) (K + 0x360) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have q208 : M.readLE (sp + 0x330) 8 = st := h.jc.bf.esl.2.2.2.2.2.2.2.2.1
  have hyi := h.jc.hyi
  have hj : dOf yi < 16 := by simp only [dOf]; omega
  have hsh := shr60 yi hyi
  have q98 := h.jc.s98
  have q1b8 := h.so1
  have qd8 := h.so2
  have q70 := h.so3
  have hc2 : 0 < c2 := by have := len_pos h.nr.2.1 h.nr.2.2.2; have := h.nr.1; omega
  have h2f := BC.facts hP h.jc.bf h.rr hc2
  have hc240 : c2 < 2 ^ 40 := h2f.1
  have hp2 : p2 + 8 * c2 ≤ 2 ^ 48 := (h2f.2.1 hc2).2.2.2
  have hl2c : l2 ≤ c2 := h.nr.1
  clear h2f
  have hH : HdM (J8 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u S M L1 b1 p1 l1 c1 p2
    l2 c2) := ⟨h⟩
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
  refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 6228032) ?_
  janus64_run [q208, q98, q1b8, qd8, q70, hsh, hwacc, hwaccF] until [6228032]
  have rl : ∀ o, o < 24 → S.mem.readLE (sp + (dOf yi + dOf yi * 2) * 8 + (0x148 + o)) 8 =
      S.mem.readLE (sp + 0x148 + 24 * dOf yi + o) 8 := fun o _ => by
    congr 1; omega
  refine callB8 hap hns hnf hml hkM hkM1 hPH.h hX hadx K9 hH.h ?hF ?hrg ?q1 ?q2 ?q3 ?r0 ?r8 ?r16 _ ?_ ?hsp ?_ ?_ ?hfs
    ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case hF => janus_frame
  case hrg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case hfs => exact efs
  case hsp => janus64_simp; exact bv_sub8 (by omega) (by omega)
  case q1 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  case q2 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  case q3 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  case r0 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt ..)]
    exact rl 0 (by decide)
  case r8 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt ..)]
    exact rl 8 (by decide)
  case r16 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt ..)]
    exact rl 16 (by decide)
  all_goals (janus64_simp; done)
end

end FvModexp.Amd64.P2W4
