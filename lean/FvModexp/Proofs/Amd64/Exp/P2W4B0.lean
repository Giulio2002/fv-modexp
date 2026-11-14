import FvModexp.Proofs.Amd64.Exp.P2W4BJ
import FvModexp.Proofs.Amd64.Exp.P2W4Seg

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): loop body segment B0 — loop test → first `sqr` → `J1` (agent divmc s77, port of divmc s73;
amd64 twin of agent infra's `Arm64.P2W4B0`)

From `LT` (fn+0x88a) with `c + 1` windows left: the test's stores `0x68 := z.len`, `0x120 := z.ptr`, `TESTQ R15, R15`
/ `JGE` (taken: `k = c ≥ 0`), the body's stores `0xe0 := z.cap`, `0xf0 := k`, `0x98 := yi` (fn+0x654), the argument
moves and `zz = zz.sqr(stk, z)` (nat.go:1069-1084; `CALL` at fn+0x681, return fn+0x686).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

theorem msb_c {c : Nat} (h : c < 2 ^ 63) : (BitVec.ofNat 64 c).msb = false := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ofNat]
  simp only [show (64 - 1 : Nat) = 63 from rfl, show (63 : Nat) < 64 from by decide, decide_true, Bool.true_and]
  exact Nat.testBit_lt_two_pow h

section
variable {impl : List Amd64.Segment} {ret0 : W64} {Q : State → Prop} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the first `sqr` call from the stores' memory (`T` = the callee entry state) -/
theorem callB0 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS : kS ≤ K) (hkS1 : sqrW 128 ≤ kS)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) (hcb : cst ≤ b) {i c yi Z : Nat} {u : Bool}
    (K1 : KJ impl ret0 Q (J1 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u))
    {M0 : Memory} {L1 : List (Nat × Nat)} {b1 pA lA cA pB lB cB : Nat}
    (li : LI R L K g sp st bp r zp zc xp xl xc yp yl lm s M0 L1 b1 zzp tp kk i u pA lA cA pB lB cB Z)
    (hi : i < yl) (hyi : yi < 2 ^ 64) (hc : c + 1 ≤ 16) (hu : u = true ↔ (c + 1 + kk) % 2 = 1)
    (hb : b + (c + 1 + 16 * i) * bc lm + P2Pre.tC lm ≤ b1 + cst)
    (hfv : Exp.outerLoop 4 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 16 i yi (c + 1) Z = FV)
    {M1 : Memory} (hF : MemFrame M0 M1 [(sp + 0x68, sp + 0x68 + 8), (sp + 0x120, sp + 0x120 + 8), (sp + 0xe0, sp + 0xe0 + 8),
      (sp + 0xf0, sp + 0xf0 + 8), (sp + 0x98, sp + 0x98 + 8)]) (hrg : M1.regions = M0.regions)
    (r68 : M1.readLE (sp + 0x68) 8 = lA) (r118 : M1.readLE (sp + 0x120) 8 = pA) (re0 : M1.readLE (sp + 0xe0) 8 = cA)
    (rf0 : M1.readLE (sp + 0xf0) 8 = c) (r98 : M1.readLE (sp + 0x98) 8 = yi)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6229984) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 0x8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (h5 : T.regs 5 = r5) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0)
    (hdf : T.df = false) (hm : T.mem = M1.writeLE (sp - 0x8) 8 6199622)
    (h0 : T.regs 0 = BitVec.ofNat 64 pB) (h3 : T.regs 3 = BitVec.ofNat 64 lB) (h1 : T.regs 1 = BitVec.ofNat 64 cB)
    (h7 : T.regs 7 = BitVec.ofNat 64 st) (h6 : T.regs 6 = BitVec.ofNat 64 pA) (h8 : T.regs 8 = BitVec.ofNat 64 lA)
    (h9 : T.regs 9 = BitVec.ofNat 64 cA) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  have hBF : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M0 L1 b1 zzp tp := ⟨li.wc, li.esl, li.tz⟩
  obtain ⟨hB, hrd, hkeep⟩ := BF.win hP hBF hF hrg (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp only [SW] <;> omega)
  obtain ⟨hB2, hrd2, hkeep2⟩ := BF.push hP hB 6199622
  have hlA := len_pos li.va li.zo
  have hcA : 0 < cA := by have := li.lac; omega
  obtain ⟨hA, hAk⟩ := hkeep u pA cA li.ca hcA
  obtain ⟨hA2, hAk2⟩ := hkeep2 u pA cA hA hcA
  obtain ⟨hBc, -⟩ := hkeep (!u) pB cB li.cb li.cb0
  obtain ⟨hBc2, -⟩ := hkeep2 (!u) pB cB hBc li.cb0
  have hAn : NV (M1.writeLE (sp - 0x8) 8 6199622) pA lA cA Z :=
    NV.keep ⟨li.lac, li.va, li.na, li.zo⟩ fun a k h1 h2 => (hAk2 a k h1 h2).trans (hAk a k h1 h2)
  have hmono := sqrCQ_mono li.la
  have hb' := hb
  rw [bud_c1 _ c i] at hb'
  have hcst : sqrCQ lA ≤ b1 := by simp only [bc] at hb'; omega
  have hra : (M1.writeLE (sp - 0x8) 8 6199622).readLE (sp - 0x8) 8 = 6197952 + 0x686 :=
    Janus.Arm64.Memory.readLE_writeLE_self ..
  have hsl : ∀ a, (a = sp + 0xc8 ∨ a = sp + 0xd0) → (M1.writeLE (sp - 0x8) 8 6199622).readLE a 8 = M0.readLE a 8 :=
    fun a ha => (hrd2 a 8 (by omega)).trans (hrd a 8 (by omega))
  rw [← hm] at hB2 hra hBc2 hA2 hAn hsl hrd2
  refine sqrB hap hns hnf hsq hkS hkS1 hP hadx hB2 (v := !u) hBc2 li.cb0 li.lbc (by rw [Bool.not_not]; exact hA2) hAn
    li.la hcst (idx := 0x686) (by decide) T hpc hsp h14 hfs hx15 hdf rfl hra h0 h3 h1 h7 h6 h8 h9 ?_
  intro s' L2 b2 p' l' c' hpc' hsp' h5' h14' hx15' hfs' hdf' e0 e3 e1 hB' hslot hres hnv hl' hx hxn hbud
  rw [Bool.not_not] at hx
  have q : ∀ a, sp + 0x50 ≤ a → a + 8 ≤ sp + 0x358 → s'.mem.readLE a 8 = M1.readLE a 8 := fun a h1 h2 =>
    (hslot a 8 h1 h2).trans (hrd2 a 8 (by omega))
  exact K1 s' s'.mem L2 b2 pA lA cA p' l' c'
    { jc := ⟨hsp', h14'.trans h14, h5'.trans h5, hfs', hx15', hdf', rfl, hB',
        (hslot _ _ (by omega) (by omega)).trans ((hsl _ (Or.inl rfl)).trans li.sc0),
        (hslot _ _ (by omega) (by omega)).trans ((hsl _ (Or.inr rfl)).trans li.sc8),
        (q _ (by omega) (by omega)).trans rf0, (q _ (by omega) (by omega)).trans r98, hi, hyi, by omega, hu, hfv, hcb⟩
      epc := hpc', e0 := e0, e3 := e3, e1 := e1, rr := hres, nr := hnv, lrb := hl', ro := hx, no := hxn,
      lob := li.la, so1 := (q _ (by omega) (by omega)).trans r118, so2 := (q _ (by omega) (by omega)).trans r68,
      so3 := (q _ (by omega) (by omega)).trans re0,
      hb := by simp only [bc, bodyB] at hb' hmono ⊢; omega }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **B0**: the body premise's first segment, from `KS` at the loop test with `c + 1` windows left -/
theorem segB0 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {kS : Nat} (hsq : P2Pre.SqrE impl R ns kS) (hkS : kS ≤ K) (hkS1 : sqrW 128 ≤ kS)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hadx : s.mem.accessible Callees.adxAddr 1 false = true) (hcb : cst ≤ b) {i c yi Z : Nat} {u : Bool}
    (K1 : KJ impl ret0 Q (J1 R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV i c yi Z u))
    (S : State) (M : Memory) (L1 : List (Nat × Nat)) (b1 pA lA cA pB lB cB : Nat)
    (h : KS R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV S M L1 b1 i (c + 1) yi Z pA lA
      cA pB lB cB u) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hc32 := h.hc
  have e15 : S.regs 15 = BitVec.ofNat 64 c := h.e15.trans (sub1c c)
  have hmsb := msb_c (c := c) (by omega)
  have hbit : (BitVec.ofNat 64 c).getLsbD 63 = false := by
    rw [BitVec.getLsbD_ofNat]; simp only [show (63 : Nat) < 64 from by decide, decide_true, Bool.true_and]
    exact Nat.testBit_lt_two_pow (by omega)
  have hce := h.li.wc.cenv hP
  have hsp48 : sp - 0x8 + 0x360 ≤ 2 ^ 48 := hce.2.2.1
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hwacc : M.accessible (sp - 0x8 - K) (K + 0x360) true = true := hce.2.2.2.1
  have hwaccF : M.accessible (sp - 0x8 - K) (K + 0x360) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have hli : HdM (LI R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp kk i u pA lA cA pB lB cB Z) := ⟨h.li⟩
  have hcA : 0 < cA := by have := len_pos h.li.va h.li.zo; have := h.li.lac; omega
  have hAf := BC.facts hP (⟨h.li.wc, h.li.esl, h.li.tz⟩ : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp
    tp) h.li.ca hcA
  have hcA40 : cA < 2 ^ 40 := hAf.1
  have hpA : pA + 8 * cA ≤ 2 ^ 48 := (hAf.2.1 hcA).2.2.2
  have hlac : lA ≤ cA := h.li.lac
  clear hAf
  have hi := h.hi
  have hyi := h.hyi
  have hu := h.hu
  have hb := h.hb
  have hfv := h.hfv
  obtain ⟨epc, esp, e14, e5, efs, ex, edf, em, e9, e6, e13, e8, e1, e2, e3, -, e10, e12, e11, e7, e0, -, -, -, -, -,
    -, -⟩ := h
  subst em
  have hPH : HdM (EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) := ⟨hP⟩
  clear hP hce
  refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 6229984) ?_
  janus64_run [hmsb, hbit, hwacc, hwaccF] until [6229984]
  refine callB0 hap hns hnf hsq hkS hkS1 hPH.h hadx hcb K1 hli.h hi hyi hc32 hu hb hfv ?hF ?hrg ?r1 ?r2 ?r3 ?_ ?_ _
    ?_ ?hsp ?_ ?_ ?hfs ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case hF => janus_frame
  case hrg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case hfs => exact efs
  case hsp => janus64_simp; exact bv_sub8 (by omega) (by omega)
  case r1 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  case r2 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  case r3 =>
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  all_goals (janus64_simp; done)

end

end FvModexp.Amd64.P2W4
