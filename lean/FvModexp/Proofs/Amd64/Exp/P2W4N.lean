import FvModexp.Proofs.Amd64.Exp.P2W4PP
import FvModexp.Proofs.Amd64.Exp.P2W4Seg
import FvModexp.Proofs.Amd64.Exp.LibCallsQ

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): `zz := stk.nat(2w)` (nat.go:1147) → the entry of
`buildPrecomputationWindowModPower2(stk, powers[:], 2, logM, x)` (nat.go:1151) (agent divmc s76, port of divmc s67; amd64 twin of agent
infra's `Arm64.P2W4N`)

From `rsE` (`LEAQ (DX)(DX*1), BX; MOVQ DI, AX`): the call of `(*stack).nat` (+0x214, return `snRet` = +0x219), the spills
`zz → 0x120/0x68/0x70`, `powers` (`sp + 0x148 … sp + 0x2c8`) zeroed (a six-round loop of four `MOVUPS X15`), the argument loads → the
callee entry `0x5e8900` with `AX = stk`, `BX = sp + 0x148`, `CX = DI = 16`, `SI = 4`, `R8 = logM`, `R9..R11 = x`,
`[sp - 0x8] = ppRet` (+0x295). `WC` is carried through the stack call (`WC.stkNat`) and handed to the continuation `KPs`
with `zz` as a scratch nat relative to the entry.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- the `stk.nat(2w)` return (fn+0x219) -/
abbrev snRet : Nat := 6198489
/-- the table call's return (fn+0x295) -/
abbrev ppRet : Nat := 6198613

set_option maxRecDepth 20000 in
/-- a return address inside the function's own segment (`seg36`, base `0x5e92c0`) is a return address of every callee
program that does not contain the function -/
theorem ra_w4 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0xb11) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (6197952 + i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg36) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [show Extracted.seg36.name = fn by decide]; exact hn) i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5e92c0 + i < 2 ^ 47; omega)
  simpa only [Extracted.seg36] using this

/-- the continuation at the table's entry (`M2` = the memory after `stk.nat(2w)`) -/
@[reducible] def KPs (impl : List Amd64.Segment) (R : RtInv) (H : Nat) (L : List (Nat × Nat)) (K g fs sp st zp zc : Nat)
    (m0 : Memory) (b1 ℓ : Nat) (bp r xp xl xc yp yl lm l0 : Nat) (ret0 : W64) (Q : State → Prop) : Prop :=
  ∀ (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat), b1 ≤ b2 →
    WC R H L K g sp st zp zc m0 M2 L2 b2 (ℓ + StackNat.rnd (2 * W lm)) →
    Scr R L L2 m0 M2 st (stW M2 st + 8 * ℓ) (2 * W lm) → ESl M2 sp st bp r zp zc xp xl xc yp yl lm l0 →
    ∀ S2 : State, S2.rip = BitVec.ofNat 64 0x5e8900 → S2.regs 4 = BitVec.ofNat 64 (sp - 0x8) →
      S2.regs 0 = BitVec.ofNat 64 st → S2.regs 3 = BitVec.ofNat 64 (sp + 0x148) → S2.regs 1 = 16#64 →
      S2.regs 7 = 16#64 → S2.regs 6 = 4#64 → S2.regs 8 = BitVec.ofNat 64 lm → S2.regs 9 = BitVec.ofNat 64 xp →
      S2.regs 10 = BitVec.ofNat 64 xl → S2.regs 11 = BitVec.ofNat 64 xc → S2.regs 14 = BitVec.ofNat 64 g →
      S2.fsBase.toNat = fs → S2.xmm 15 = 0 → S2.df = false →
      MemFrame M2 S2.mem [(sp - 0x8, sp), (sp + 0x68, sp + 0x78), (sp + 0x120, sp + 0x128), (sp + 0x148, sp + 0x2c8)] →
      S2.mem.regions = M2.regions → S2.mem.readLE (sp - 0x8) 8 = ppRet →
      S2.mem.readLE (sp + 0x120) 8 = stW M2 st + 8 * ℓ → S2.mem.readLE (sp + 0x68) 8 = 2 * W lm →
      S2.mem.readLE (sp + 0x70) 8 = 2 * W lm →
      ReachesRet (LibW.program.link impl) ret0 S2 Q

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the `(*stack).nat` entry (`[RSP] = snRet`) to the table's entry -/
theorem segN1 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ K) (haN : aboveN ≤ 0x58)
    {ret0 : W64} {Q : State → Prop}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}
    (h : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ) (hl0 : 0 < ℓ)
    (hH : ℓ + 2 * W lm + 3 ≤ HW (stLen s.mem st) lm) (hl16 : ℓ + 2 * W lm + 3 ≤ 2 ^ 16)
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st))
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 LibCalls.snE) (hsp : S1.regs 4 = BitVec.ofNat 64 (sp - 0x8))
    (h0 : S1.regs 0 = BitVec.ofNat 64 st) (h3 : S1.regs 3 = BitVec.ofNat 64 (2 * W lm))
    (h14 : S1.regs 14 = BitVec.ofNat 64 g) (hfs : S1.fsBase.toNat = fs) (hx15 : S1.xmm 15 = 0)
    (hdf : S1.df = false) (hm : S1.mem = M) (hrd : M.readLE (sp - 0x8) 8 = snRet)
    (KP : KPs impl R (HW (stLen s.mem st) lm) L K g fs sp st zp zc s.mem b1 ℓ bp r xp xl xc yp yl lm (stLen s.mem st)
      ret0 Q) :
    ReachesRet (LibW.program.link impl) ret0 S1 Q := by
  have hce := h.cenv hP
  have hK0 : K ≤ sp - 0x8 := hce.2.1
  have hA0 : sp - 0x8 + 0x360 ≤ 2 ^ 48 := hce.2.2.1
  have hg48 : g + 24 ≤ 2 ^ 48 := hce.2.2.2.2.1
  have hlm : lm ≤ 2 ^ 13 := hP.2.2.2.2.2.1
  have hlm2 : 2 ≤ lm := hP.2.2.2.2.1
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hW1 : 0 < W lm := by simp only [W]; omega
  have hspN : (S1.regs 4).toNat = sp - 0x8 := by rw [hsp, BitVec.toNat_ofNat]; omega
  have h14N : (S1.regs 14).toNat = g := by rw [h14, BitVec.toNat_ofNat]; omega
  have hst48 : st + 24 ≤ 2 ^ 48 := h.sok.2.2.2.1
  have hpre := snPre (stk := stkN) (above := aboveN) (n := 2 * W lm) hP h hkN (by omega) hspN h14N hfs hm
    (by omega) hl16 hH
  refine LibCalls.stkNatCallQ hap hns hsn (HW (stLen s.mem st) lm) (ra_w4 hap hnf 0x219 (by decide)) hpc
    (by rw [hspN, hm]; exact hrd) h0 h3 hx15 hdf (by omega) (by omega) hpre
    fun s' hpc' hsp' h5' h14' hx15' hrg' hpost => ?_
  obtain ⟨L2, b2, hb2, hW2, hscr, e0, e3, e1, efs, edf, hF2⟩ :=
    WC.stkNat hP h hkN (by omega) hspN h14N hm (by rw [hrg', hm]) (by omega) hpost
  have hwo := h.win_out hP hl0
  have hkeep : ∀ a k, sp + 0x57 ≤ a → a + k ≤ sp + 0x358 → s'.mem.readLE a k = M.readLE a k := by
    intro a k h1 h2
    refine hF2.readLE a k ?_
    have := hwo a k (by omega) h2
    rw [outside_append] at this ⊢
    refine ⟨?_, this.2⟩
    rw [outside_append]
    exact ⟨this.1, by simp only [outside_cons, outside_nil, and_true]; omega⟩
  have hsl2 : ESl s'.mem sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st) :=
    ESl.keep hsl fun a k ha => hkeep a k (by omega) (by omega)
  have hsl2' := hsl2
  obtain ⟨-, -, -, -, -, -, -, -, q208, q210, q218, q220, -, -, q228, -, -, -⟩ := hsl2'
  have hacc : s'.mem.accessible (sp - 0x8 - K) (K + 0x360) true = true := by
    rw [hW2.fr.accessible]; exact hP.cenv0.2.2.2.1
  have a118 : s'.mem.accessible (sp + 0x120) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have a68 : s'.mem.accessible (sp + 0x68) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have a70 : s'.mem.accessible (sp + 0x70) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have a140 : s'.mem.accessible (sp + 0x148) 0x180 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have am8 : s'.mem.accessible (sp - 0x8) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  have hsp2 : s'.regs 4 = BitVec.ofNat 64 sp := by
    rw [hsp', hsp]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]; omega
  have hz48 : stW s'.mem st + 8 * ℓ < 2 ^ 64 := by
    have hc := hW2.sok.2.2.2.2.2.1; have := hW2.len
    have := (hW2.sok.2.2.2.2.1 (by omega)).2.2.2; omega
  have hpc2 : s'.rip = BitVec.ofNat 64 snRet := hpc'
  have h14s := h14'.trans h14
  have hx15s := hx15'.trans hx15
  have edf2 := edf.trans hdf
  have efs2 : s'.fsBase.toNat = fs := by rw [efs]; exact hfs
  have hWH : LibCalls.Hide (WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem s'.mem L2 b2 (ℓ + StackNat.rnd (2 * W lm))) :=
    ⟨hW2⟩
  have hSH : LibCalls.Hide (Scr R L L2 s.mem s'.mem st (stW s'.mem st + 8 * ℓ) (2 * W lm)) := ⟨hscr⟩
  have hKH : LibCalls.Hide (KPs impl R (HW (stLen s.mem st) lm) L K g fs sp st zp zc s.mem b1 ℓ bp r xp xl xc yp yl lm
    (stLen s.mem st) ret0 Q) := ⟨KP⟩
  have hEH : LibCalls.Hide (ESl s'.mem sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) := ⟨hsl2⟩
  have h8 : 8 ≤ sp := by have := hP.1.2.2.2.2.2.2.1; omega
  clear hpost hF2 hkeep hW2 hscr KP hsl hsl2 h hpre hP hce hwo hpc' hsp' h14' hx15' edf efs
  refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 6195456) ?_
  janus64_run [q208, q210, q218, q220, q228, a118, a68, a70, a140, am8] until [6195456]
  refine hKH.h s'.mem L2 b2 hb2 hWH.h hSH.h hEH.h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?mf ?rg ?r0 ?r1 ?r2 ?r3
  case mf => janus_frame
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals first | (janus64_simp; done) | skip
  all_goals first | exact efs2 | exact hx15s | exact edf2 | skip
  all_goals
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from `rsE`** (after the reserve): `zz := stk.nat(2w)` → the table's entry -/
theorem segN {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkN aboveN : Nat} (hsn : StackNatX.HypQ impl R ns stkN aboveN) (hkN : stkN ≤ K) (haN : aboveN ≤ 0x58)
    {ret0 : W64} {Q : State → Prop}
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ : Nat}
    (h : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 ℓ) (hl0 : 0 < ℓ)
    (hH : ℓ + 2 * W lm + 3 ≤ HW (stLen s.mem st) lm) (hl16 : ℓ + 2 * W lm + 3 ≤ 2 ^ 16)
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 rsE) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h2 : S.regs 2 = BitVec.ofNat 64 (W lm))
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) (hm : S.mem = M)
    (KP : KPs impl R (HW (stLen s.mem st) lm) L K g fs sp st zp zc s.mem b1 ℓ bp r xp xl xc yp yl lm (stLen s.mem st)
      ret0 Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hce := h.cenv hP
  have hK0 : K ≤ sp - 0x8 := hce.2.1
  have hA0 : sp - 0x8 + 0x360 ≤ 2 ^ 48 := hce.2.2.1
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hlm : lm ≤ 2 ^ 13 := hP.2.2.2.2.2.1
  have hW : W lm ≤ 128 := by simp only [W]; omega
  have hacc : M.accessible (sp - 0x8) 8 true = true := by
    rw [h.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega)
  have e2w : BitVec.ofNat 64 (W lm) + BitVec.ofNat 64 (W lm) = BitVec.ofNat 64 (2 * W lm) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hst48 : st + 24 ≤ 2 ^ 48 := h.sok.2.2.2.1
  have hwr : MemFrame M (M.writeLE (sp - 0x8) 8 snRet) [(sp - 0x8, sp)] := by janus_frame
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  have hrt := hP.win_rt
  have hLs := hP.cenv0.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have h1 : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem (M.writeLE (sp - 0x8) 8 snRet) L1 b1 ℓ := by
    refine h.frame hwr (by simp only [Janus.Arm64.Memory.regions_writeLE]) (fun a k ho => ?_) (fun a k hin _ => ?_)
      (by simp only [outside_cons, outside_nil, and_true]; omega) (fun q hq => Or.inr ?_)
    · simp only [WN, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
    · obtain ⟨q, hq, q1, q2⟩ := hin
      have := hLs q hq
      simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    · simp only [List.mem_singleton] at hq; subst hq; dsimp only
      exact hrt.of_sub (by omega) (by omega)
  have hsl1 : ESl (M.writeLE (sp - 0x8) 8 snRet) sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st) :=
    ESl.keep hsl fun a k ha => hwr.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hrd : (M.writeLE (sp - 0x8) 8 snRet).readLE (sp - 0x8) 8 = snRet := Janus.Arm64.Memory.readLE_writeLE_self ..
  have hKH : LibCalls.Hide (KPs impl R (HW (stLen s.mem st) lm) L K g fs sp st zp zc s.mem b1 ℓ bp r xp xl xc yp yl lm
    (stLen s.mem st) ret0 Q) := ⟨KP⟩
  have hPH : LibCalls.Hide (EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) := ⟨hP⟩
  have h1H : LibCalls.Hide (WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem (M.writeLE (sp - 0x8) 8 snRet) L1 b1 ℓ) :=
    ⟨h1⟩
  have hsH : LibCalls.Hide (ESl (M.writeLE (sp - 0x8) 8 snRet) sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) :=
    ⟨hsl1⟩
  have h8 : 8 ≤ sp := by omega
  subst hm
  clear KP hP h hsl h1 hsl1 hce hwr hLs hrt
  refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 6186112) ?_
  janus64_run [e2w, hacc] until [6186112]
  refine segN1 hap hns hnf hsn hkN haN hPH.h h1H.h hl0 hH hl16 hsH.h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrd hKH.h
  all_goals first | (janus64_simp; done) | exact hfs | skip
  all_goals
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

end

end FvModexp.Amd64.P2W4
