import FvModexp.Proofs.Arm64.NatQ.DivMEpi
import FvModexp.Proofs.Arm64.NatQ.DivMBigPost
import FvModexp.Proofs.Arm64.NatQ.DivMLPre

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DivMBig.lean, TIGHT COSTS, asm s38)
# `nat.div` (arm64), `stk == nil`, `z = nil`, `z2 = u`, `u ≥ v`: the `divLarge` call, the deferred `stk.free()`, return

`bigCallM`: from `divLarge`'s entry `X` (after `getStack()` and the defer record, `joinD`): the call (premise
`DivLarge.Hyp`, precondition `l_preM`), the epilogue (`epiCD`), the closure `nat.div.deferwrap1` (`dsumD`, pre
`freePreD`) and the return (`epiRD`); the postcondition `postBigM`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.DivNil

namespace FvModexp.Arm64.Q.NatDiv
open FvModexp.Arm64.NatDiv
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem bigCallM (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (dc : Nat → Nat → Nat) (hL : DivLarge.Hyp impl R dc)
    (hput : PoolPutLive (LibDivFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {b : Nat} {L : List (Nat × Nat)} {u ul uc v vl vc : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl s)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl) (hu64 : u < 2 ^ 64)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    {L1 : List (Nat × Nat)} {b1 st : Nat} (X : State) (hN : NewStk R L L1 b b1 (s.regs 28).toNat X.mem st)
    (hF : MemFrame s.mem X.mem (R.rt ++ winA s 41504 112)) (hLF : LiveFrame s.mem X.mem L [])
    (hreg : X.mem.regions = s.mem.regions)
    (hpc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program DivLarge.fn)) (hsp : X.sp = s.sp - 240#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 248#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 retL)
    (hr0 : X.regs 0 = BitVec.ofNat 64 0) (hr1 : X.regs 1 = BitVec.ofNat 64 0) (hr2 : X.regs 2 = BitVec.ofNat 64 0)
    (hr3 : X.regs 3 = BitVec.ofNat 64 st) (hr4 : X.regs 4 = BitVec.ofNat 64 u) (hr5 : X.regs 5 = BitVec.ofNat 64 ul)
    (hr6 : X.regs 6 = BitVec.ofNat 64 uc) (hr7 : X.regs 7 = BitVec.ofNat 64 u) (hr8 : X.regs 8 = BitVec.ofNat 64 ul)
    (hr9 : X.regs 9 = BitVec.ofNat 64 uc) (hr10 : X.regs 10 = BitVec.ofNat 64 v)
    (hr11 : X.regs 11 = BitVec.ofNat 64 vl) (hr12 : X.regs 12 = BitVec.ofNat 64 vc)
    (mlr : X.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat)
    (mfp : X.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat) (mfl : X.mem.readLE (s.sp.toNat - 122) 1 = 1)
    (mdw : X.mem.readLE (s.sp.toNat - 32) 8 = dwD) (mst : X.mem.readLE (s.sp.toNat - 24) 8 = st)
    (mrc : X.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 32) :
    ReachesRet (LibDiv.program.link impl) (s.regs 30) X (RQM R b dc L u ul uc v vl s) := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hp.ce
  have hwO : Outside (s.sp.toNat - 41504) (41504 + 112) R.rt := hout
  have hspn : X.sp.toNat = s.sp.toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hul := hp.ul9; have hvl := hp.vl9
  have hu40 := hp.uo.1; have hv48 := hp.vo.2.2.1
  have hst48 := hN.2.2.2.2.1
  have e : ∀ x, x < 2 ^ 64 → (BitVec.ofNat 64 x).toNat = x := fun x h => tN h
  have hsum := lsum impl hap R dc hL (16 * ul + 64) b1 L1 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 u) (BitVec.ofNat 64 ul) (BitVec.ofNat 64 uc) (BitVec.ofNat 64 u)
    (BitVec.ofNat 64 ul) (BitVec.ofNat 64 uc) (BitVec.ofNat 64 v) (BitVec.ofNat 64 vl) (BitVec.ofNat 64 vc)
  have e30 : (X.regs 30).toNat = retL := by rw [h30]; decide
  have e00 := e 0 (by decide); have est := e st (by omega); have eu := e u hu64
  have euc := e uc (by omega); have eul := e ul (by omega); have ev := e v (by omega)
  have evl := e vl (by omega)
  refine ReachesRet.call_regions hsum hpc ⟨?ra, ?args, ?pre⟩ (fun T hT ⟨⟨f1, f2, f3, f4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [e30]; exact raD impl hap _ (by decide) _ (by decide) (by decide) (by decide) (by decide +kernel)
  case args =>
    simp only [ArgsFrom]
    exact ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, trivial⟩
  case pre =>
    show DivLarge.Pre R b1 (16 * ul + 64) L1 (DivLarge.costQ dc (BitVec.ofNat 64 ul).toNat
      (BitVec.ofNat 64 vl).toNat) (BitVec.ofNat 64 0).toNat (BitVec.ofNat 64 0).toNat (BitVec.ofNat 64 st).toNat
      (BitVec.ofNat 64 u).toNat (BitVec.ofNat 64 uc).toNat (BitVec.ofNat 64 u).toNat (BitVec.ofNat 64 ul).toNat
      (BitVec.ofNat 64 v).toNat (BitVec.ofNat 64 vl).toNat X
    rw [e00, est, eu, euc, eul, ev, evl]
    exact l_preM hp hN hF hLF hreg hge hv2 X hsp h28 rfl
  rw [e00, est, eu, euc, eul, ev, evl] at hq
  -- (the `(BitVec.ofNat 64 x).toNat = x` facts make every later `omega` slow: clear them)
  clear e00 est eu euc eul ev evl e30 e hsum hspn
  obtain ⟨q, ql, qc, r, rl, rc, e0, e1, e2, e3, e4, e5, L2, b'', -, hr', ⟨hx, hbb, hinvT⟩, hsb, hfr, hmf, hlf⟩ := hq
  -- the stack facts used below (the disjunctive `StackBackL`/`NatOF` go into a `Box`: `omega` splits disjunctions)
  have hl0 : stLen X.mem st = 0 := hN.2.2.2.2.2.2.1
  have hmH : (st, st + 24) ∈ L1 := by rw [hN.1]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hmA : 0 < stCap X.mem st → (stW X.mem st, stW X.mem st + 8 * stCap X.mem st) ∈ L1 := fun hc => by
    rw [hN.1]; refine List.mem_append_right _ ?_
    simp only [stkRs, Nat.ne_of_gt hc, ↓reduceIte, List.mem_cons, true_or, or_true]
  have hok1 : StkOK T.mem R L2 st := hsb.1.1
  have hl1 : stLen T.mem st = 0 := hsb.1.2.1.trans hl0
  have hc01 : stCap T.mem st = 0 → stW T.mem st = 0 := hsb.2.cap0 hN.2.2.2.2.2.2.2.2.1
  have hdis1 : 0 < stCap T.mem st → Apart st 24 (stW T.mem st) (8 * stCap T.mem st) := fun hc => by
    rcases hsb.1.2.2 with ⟨ew, ec⟩ | ⟨-, hap'⟩
    · rw [ew, ec]; exact hN.2.2.2.2.2.2.2.2.2.2.2.2.1
    · have := hap' _ hmH; simp only [Nat.add_sub_cancel_left] at this; exact this.symm
  have hrs1 : ∀ x ∈ stkRs T.mem st, x ∈ L2 := stkRs_forall (hx.mem_old hmH) fun hc => by
    by_cases hk' : stW T.mem st = stW X.mem st ∧ stCap T.mem st = stCap X.mem st
    · rw [hk'.1, hk'.2]; exact hx.mem_old (hmA (by rw [← hk'.2]; exact hc))
    · exact hsb.2.mem hk'
  have hB : Box (ExpHyp.NatOF R L1 L2 T.mem u uc 1 r rl rc (natVal X.mem u ul % natVal X.mem v vl) ∧
      StackBackL R L1 L2 st X.mem T.mem) := ⟨⟨hr', hsb⟩⟩
  clear hr' hsb
  have hKb : Box (T.mem.readLE (s.sp.toNat - 240) 8 = (s.regs 30).toNat ∧
      T.mem.readLE (s.sp.toNat - 248) 8 = (s.regs 29).toNat ∧ T.mem.readLE (s.sp.toNat - 122) 1 = 1 ∧
      T.mem.readLE (s.sp.toNat - 32) 8 = dwD ∧ T.mem.readLE (s.sp.toNat - 24) 8 = st ∧
      T.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 32) :=
    ⟨slots6 (u := u) (uc := uc) hN hb' hwO (fun hc => (hp.uo.2.2 hc).1) hsp hmf mlr mfp mfl mdw mst mrc⟩
  clear mlr mfp mfl mdw mst mrc
  have hpcT : T.pc = BitVec.ofNat 64 retL := by rw [hT, h30]
  have hspT : T.sp = s.sp - 240#64 := by rw [f1, hsp]
  have hTacc : T.mem.accessible (s.sp.toNat - 41504) (41504 + 112) true = true := by
    rw [hmf.accessible, hF.accessible]; exact hw
  have hg28 : T.regs 28 = s.regs 28 := f2.trans h28
  rw [h28] at hinvT
  refine epiCD impl _ hal hb' ha T hpcT hspT hTacc hKb.h.2.2.1 hKb.h.2.2.2.2.2 hKb.h.2.2.2.1 ?_
  intro S2 p2 sp2 r26 r30 g18 g28 g29 hF2 hrg2 w0 w1 w2 w3 w4 w5
  have hWb : Box (S2.mem.readLE (s.sp.toNat - 80) 8 = (T.regs 3).toNat ∧
      S2.mem.readLE (s.sp.toNat - 72) 8 = (T.regs 4).toNat ∧ S2.mem.readLE (s.sp.toNat - 64) 8 = (T.regs 5).toNat) :=
    ⟨⟨w3, w4, w5⟩⟩
  clear w0 w1 w2 w3 w4 w5
  -- the stack at `S2`
  have hhdO := out_inR2 hwO hN.hdr.1
  have hst2 : Outside st 24 [(s.sp.toNat - 80, s.sp.toNat - 32), (s.sp.toNat - 121, s.sp.toNat - 120)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  obtain ⟨hok2, ew2, el2, ec2⟩ := stkOK_frame hok1 hF2 hst2
  have hrsE : stkRs S2.mem st = stkRs T.mem st := stkRs_congr ew2 ec2
  -- the guard word and the window at `S2`
  have hgS : S2.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    guardS hN hb' hga hgr (fun hc => (hp.uo.2.2 hc).2) hsp hF hmf hF2
  have hacS : ∀ a k w, S2.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hF2.accessible, hmf.accessible, hF.accessible]
  have h24' : S2.mem.readLE (s.sp.toNat - 24) 8 = st := by
    rw [hF2.readLE _ 8 (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hKb.h.2.2.2.2.1
  have e28 : (S2.regs 28).toNat = (s.regs 28).toNat := by rw [g28, hg28]
  have hinv2 : R.inv b'' L2 (s.regs 28).toNat (view R.rt L2 S2.mem) := RtInv.inv_frame' hF2 (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    all_goals left; exact hwO.of_sub (by simp only; omega) (by simp only; omega)) hinvT
  have hpre := freePreD (b' := b'') (L2 := L2) (sp := s.sp.toNat) hN
    (by rw [sp2, hspT, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega)
    (by rw [r26, BitVec.toNat_ofNat]; omega) (by rw [r30]; decide) e28 hg1
    (by rw [hacS]; exact hg2) (by rw [hgS]; exact hg3) hga hgr hal hb' ha (by rw [hacS]; exact hw) hwO hLs h24'
    hok2 (by rw [el2]; exact hl1) (by rw [ec2, ew2]; exact hc01) (by rw [ec2, ew2]; exact hdis1)
    (by rw [hrsE]; exact hrs1) hx (hp.sv.2.2.2.2.2.2.2.2 [Free.poolA]) hinv2
  refine epiRD impl (dsumD impl hap R hput b'' L2 (stkRs S2.mem st)) _ hal hb' ha S2 p2 (sp2.trans hspT) r30 hpre
    hl48 hl4 ?_
  intro s3 hpost3 hrg3
  obtain ⟨⟨t1, t18, t28, t29⟩, hMF3, hLF3, hinv3⟩ := hpost3
  have hso : Free.stkOf S2 = st := by
    show S2.mem.readLE ((S2.regs 26).toNat + 8) 8 = st
    rw [r26, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show s.sp.toNat - 32 + 8 = s.sp.toNat - 24 by omega]
    exact h24'
  have esp2 : S2.sp.toNat = s.sp.toNat - 240 := by
    rw [sp2, hspT, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  rw [hso, esp2] at hMF3
  rw [hso] at hLF3
  rw [e28] at hinv3
  have hrd3 : ∀ a, s.sp.toNat - 248 ≤ a → a + 8 ≤ s.sp.toNat + 112 → s3.mem.readLE a 8 = S2.mem.readLE a 8 := by
    intro a i1 i2
    refine hMF3.readLE a 8 ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hwO.of_sub (by omega) (by omega), by omega, by omega⟩
  have hrdT : ∀ a, (a + 8 ≤ s.sp.toNat - 121 ∨ s.sp.toNat - 120 ≤ a) → (a + 8 ≤ s.sp.toNat - 80 ∨ s.sp.toNat - 32 ≤ a) →
      S2.mem.readLE a 8 = T.mem.readLE a 8 := fun a i1 i2 =>
    hF2.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ⟨t1, by rw [hMF3.accessible, hacS]; exact hw, ?_, ?_⟩
  · rw [hrd3 _ (by omega) (by omega), hrdT _ (by omega) (by omega)]; exact hKb.h.1
  intro s4 hs4 v0 v1 v2 v3 v4 v5 v29 v18 v28 hm4
  have q3 : s4.regs 3 = BitVec.ofNat 64 r := by
    rw [v3, hrd3 _ (by omega) (by omega), hWb.h.1, e3, Expmc.bv_ofNat_toNat]
  have q4 : s4.regs 4 = BitVec.ofNat 64 rl := by
    rw [v4, hrd3 _ (by omega) (by omega), hWb.h.2.1, e4, Expmc.bv_ofNat_toNat]
  have q5 : s4.regs 5 = BitVec.ofNat 64 rc := by
    rw [v5, hrd3 _ (by omega) (by omega), hWb.h.2.2, e5, Expmc.bv_ofNat_toNat]
  have q29 : s4.regs 29 = s.regs 29 := by
    rw [v29, hrd3 _ (by omega) (by omega), hrdT _ (by omega) (by omega), hKb.h.2.1, Expmc.bv_ofNat_toNat]
  refine ⟨⟨hs4, v28.trans (t28.trans (g28.trans hg28)), q29, v18.trans (t18.trans (g18.trans (f4.trans h18)))⟩, ?_⟩
  obtain ⟨hr', hsb⟩ := hB.h
  exact postBigM hp hN hF hLF hsp hr' hx hbb hsb hfr hmf hlf hF2 hMF3 hLF3 (by rw [hrsE] at hinv3 ⊢; exact hinv3) s4 hm4
    v0 v1 v2 q3 q4 q5

end FvModexp.Arm64.Q.NatDiv
