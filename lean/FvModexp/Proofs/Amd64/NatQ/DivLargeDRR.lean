import FvModexp.Proofs.Amd64.NatQ.DivLargeDRP
import FvModexp.Proofs.Amd64.NatQ.DivLargeDBR

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeDRR.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): `n ≥ divRecursiveThreshold` → the call `q.divRecursiveStep(stk, u, v, 0)` (natdiv.go:742)

`dr3`: at `divRecursiveStep`'s entry (`RSP = entry RSP - 312`, return address `+0x647`), the call (premise `DrsHyp`,
as an 8-register summary `Ensures.toSummaryRegs8D`; `R10 = depth` is not used by `DrsPre`), then `JMP joinD` (`+0x676`)
→ `AtD` (`divPost`, window `40960 / 96`). Port of `Arm64/Nat/DivLargeDRR.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (outside_of_inRanges)
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
/-- the stack header at a state whose memory is `AtJ`'s up to `scrB` slots and `q` (pure) -/
theorem stk_Y {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S) {m : Memory}
    (hA : MemFrame S.mem m (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)])) (hAL : LiveFrame S.mem m Lq [(qp, qp + 8 * qc)]) :
    stLen m st = stLen s.mem st + StackNat.rnd vl := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hsth := hE.pre.sti.1.2.1
  have hqs := hS.qa.ps; unfold Apart at hqs
  have hsw := hl.sw
  simp only [stLen]
  rw [← hS.mem.mem.hlen]
  rcases (hS.ext3.held (hE.ext.held hsth)).sub (a := st + 8) (n := 8) (by omega) (by omega) with hi | ho
  · exact hAL.readLE _ 8 hi (by simp only [outside_cons, outside_nil, and_true]; omega)
  · refine hA.readLE _ 8 ?_
    rw [outside_append, outside_append]
    exact ⟨⟨ho, by simp only [scrB, outside_cons, outside_nil, and_true]; omega⟩,
      by simp only [outside_cons, outside_nil, and_true]; omega⟩

set_option maxRecDepth 20000 in
/-- the stack's `cap` at the call (`c1`) -/
theorem cap_Y {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lq : List (Nat × Nat)} {bq P C sh qp qc : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S) {m : Memory}
    (hA : MemFrame S.mem m (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)])) (hAL : LiveFrame S.mem m Lq [(qp, qp + 8 * qc)]) :
    stCap m st = c1 := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hsth := hE.pre.sti.1.2.1
  have hqs := hS.qa.ps; unfold Apart at hqs
  have hsw := hl.sw
  simp only [stCap]
  rw [← hS.mem.mem.hcap]
  rcases (hS.ext3.held (hE.ext.held hsth)).sub (a := st + 16) (n := 8) (by omega) (by omega) with hi | ho
  · exact hAL.readLE _ 8 hi (by simp only [outside_cons, outside_nil, and_true]; omega)
  · refine hA.readLE _ 8 ?_
    rw [outside_append, outside_append]
    exact ⟨⟨ho, by simp only [scrB, outside_cons, outside_nil, and_true]; omega⟩,
      by simp only [outside_cons, outside_nil, and_true]; omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- at `divRecursiveStep`'s entry: the call, `JMP joinD`, then `AtD` -/
theorem dr3 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat) (hD : DrsHypQ impl R dc)
    (b : Nat) (L : List (Nat × Nat)) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lq : List (Nat × Nat)) (bq P C sh qp qc : Nat)
    (hE : Env R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lq bq P C sh qp qc S) (X : State)
    (hpc : X.rip = BitVec.ofNat 64 (segAddr Extracted.program drsFn))
    (hspn : (X.regs 4).toNat = (s.regs 4).toNat - 312)
    (hrd : X.mem.readLE (X.regs 4).toNat 8 = segAddr Extracted.program fn + 0x647) (h5 : X.regs 5 = s.regs 4 - 8#64)
    (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase) (hx15 : X.xmm 15 = 0#128) (hdf : X.df = false)
    (hr0 : X.regs 0 = BitVec.ofNat 64 qp) (hr3 : X.regs 3 = BitVec.ofNat 64 (il - vl + 1))
    (hr1 : X.regs 1 = BitVec.ofNat 64 qc) (hr7 : X.regs 7 = BitVec.ofNat 64 st) (hr6 : X.regs 6 = BitVec.ofNat 64 P)
    (hr8 : X.regs 8 = BitVec.ofNat 64 (il + 1)) (hr9 : X.regs 9 = BitVec.ofNat 64 C)
    (hA : MemFrame S.mem X.mem (R.rt ++ scrB s ++ [(qp, qp + 8 * qc)]))
    (hAL : LiveFrame S.mem X.mem Lq [(qp, qp + 8 * qc)])
    (hq0 : X.mem.readLE ((s.regs 4).toNat - 64) 8 = qp) (hq1 : X.mem.readLE ((s.regs 4).toNat - 56) 8 = il - vl + 1)
    (hq2 : X.mem.readLE ((s.regs 4).toNat - 48) 8 = qc)
    (hvS : X.mem.readLE ((s.regs 4).toNat - 304) 8 = t) (hlS : X.mem.readLE ((s.regs 4).toNat - 296) 8 = vl)
    (hcS : X.mem.readLE ((s.regs 4).toNat - 288) 8 = vl)
    (hreg : X.mem.regions = s.mem.regions) (hz : natVal X.mem qp (il - vl + 1) = 0)
    (hinvX : R.inv bq Lq (s.regs 14).toNat (view R.rt Lq X.mem)) (Q : State → Prop)
    (k : ∀ L2 b2 w2 c2 T, AtD R b H L (costQ dc il vl) zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P
      C sh qp qc L2 b2 w2 c2 T → ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) X Q := by
  have hl := hE.lay
  have hil9 := hl.il9; have hvil := hl.vil; have hv2 := hl.v2; have hsp0 := hl.sp0
  have hcap := hS.ua.cap; have hc40 := hS.ua.c40; have hqcap := hS.qa.cap; have hq40 := hS.qa.c40
  have e0 : (BitVec.ofNat 64 qp).toNat = qp := tN64 (by have := hS.qa.p48; omega)
  have e1 : (BitVec.ofNat 64 (il - vl + 1)).toNat = il - vl + 1 := tN64 (by omega)
  have e2 : (BitVec.ofNat 64 qc).toNat = qc := tN64 (by omega)
  have e3 : (BitVec.ofNat 64 st).toNat = st := tN64 (by have := hl.st48; omega)
  have e4 : (BitVec.ofNat 64 P).toNat = P := tN64 (by have := hS.ua.p48; omega)
  have e5 : (BitVec.ofNat 64 (il + 1)).toNat = il + 1 := tN64 (by omega)
  have e6 : (BitVec.ofNat 64 C).toNat = C := tN64 (by omega)
  have hLn := stk_Y hE hS hA hAL
  have hCY := cap_Y hE hS hA hAL
  have hcost : dc (il + 1) vl + (stkRes H - potK * c1) ≤ bq := bud_div hE hS.bud3
  have hpre := dr_pre hE hS X hspn h14 hfs hA hAL hreg hz hinvX hvS hlS hcS hcost
  have hc : CodeIn64 ((Extracted.program.onlySegments drsNames).link impl) (LibDivL.program.link impl) := by
    rw [LibDivL.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hsum := Ensures.toSummaryRegs8D (fun a0 a1 a2 a3 a4 a5 a6 a7 => hD H bq Lq a0 a1 a2 a3 a4 a5 a6 a7 t vl vl)
    (A64.noExit_restrict64 hap drsNames) hc
  refine ReachesRet.call_regions hsum hpc ⟨?_, hx15, hdf, ?_⟩ fun T hT ⟨⟨f4, f5, f14, f15⟩, hq⟩ hrg => ?_
  · simp only [regSP]; rw [hrd]
    exact ra_dl (i := 0x647) hap (by decide) (by decide)
  · rw [hr0, hr3, hr1, hr7, hr6, hr8, hr9, e0, e1, e2, e3, e4, e5, e6]; exact hpre
  rw [hr0, hr3, hr7, hr6, hr8, e0, e1, e3, e4, e5] at hq
  obtain ⟨qfs, qdf, hqv, hrv, L', b', ⟨hx, hb, hinv⟩, hSB, hMF, hLF⟩ := hq
  rw [h14] at hinv
  have hbud : b - (costQ dc il vl + stkR H s.mem st) + stkR H T.mem st ≤ b' := by
    have hb3 := hS.bud3
    have hb1 := hE.bud
    have hc := hE.pre.cost
    simp only [stkR] at hb hb1 hc ⊢
    rw [hCY] at hb
    simp only [costQ] at hc ⊢
    omega
  have hsp' : T.regs 4 = s.regs 4 - 304#64 := by
    rw [f4]; bv_omega
  have hTpc : T.rip = BitVec.ofNat 64 (segAddr Extracted.program fn + 0x647) := by
    rw [hT, retAddrOf, hrd]
  have h5' : T.regs 5 = s.regs 4 - 8#64 := by rw [f5, h5]
  have h14' : T.regs 14 = s.regs 14 := by rw [f14, h14]
  have hfs' : T.fsBase = s.fsBase := by rw [qfs, hfs]
  have hx15' : T.xmm 15 = 0#128 := by rw [f15, hx15]
  have hdf' : T.df = false := by rw [qdf, hdf]
  clear hT hpre hsum hc
  janus64_run until [joinD]
  exact k L' b' (stW T.mem st) (stCap T.mem st) _ (divPost (T := { T with rip := 6221718#64, df := false }) hE hS hspn
    hA hAL hq0 hq1 hq2 hreg (K := 40960) (A := 96) (by omega) (by omega) rfl hsp' h5' h14' hfs' hx15' rfl hrg hqv hrv hx
    hbud hinv hSB
    (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hMF) hLF)

end FvModexp.Amd64.Q.DivLarge
