import FvModexp.Proofs.Amd64.NatQ.DivBasicQh
import FvModexp.Proofs.Amd64.NatQ.DivBasicMul
import FvModexp.Proofs.Amd64.NatQ.DivBasicSub
import FvModexp.Proofs.Amd64.NatQ.DivBasicAdd
import FvModexp.Proofs.Amd64.NatQ.DivBasicTail
import FvModexp.Proofs.Amd64.NatQ.DivBasicInv

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivBasicStep.lean, TIGHT COSTS, top s38)
# `divBasic` (amd64): one loop iteration, head (`j`) → head (`j - 1`), with the invariant

Composes `est` → `mul1` → `sub1` → `add1` → `tail`; the values: `Asm.su_bridge` (multiply/subtract/add-back =
`Mdl.dbSubAdd`) and `pre_facts` (`Mdl.dbStep_inv`). The twin of `Arm64/Nat/DivBasicStep.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.DivBasic
open FvModexp.Amd64.DivBasic
variable {H : Nat}

set_option maxHeartbeats 4000000 in
theorem step (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (qp ql st up ul uc vp vl vc : Nat) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat) (hE : Env R b H L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    (hvu : vl ≤ ul) (j ujn : Nat) (hjm : j ≤ ul - vl) (S : State)
    (hH : Hd R b H L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S j ujn)
    (hI : Inv qp ql up ul vp vl s (j + 1) ujn S.mem) (Q : State → Prop)
    (k : ∀ S' ujn', Hd R b H L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S' (j + 2 ^ 64 - 1) ujn' →
      Inv qp ql up ul vp vl s j ujn' S'.mem → ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S' Q) :
    ReachesRet (LibDivBasic.program.link impl) (retAddrOf s) S Q := by
  obtain ⟨hjl, hle, hcz0, hst0, hInv, hdb⟩ := pre_facts hE.pre hvu hjm hI
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2
  have hqB := qhatM_lt S.mem up j ujn hE.pre.vtop hle
  generalize hqh : qhatM s vp vl S.mem up j ujn = qhat at hcz0 hst0 hdb hqB
  have hM0 := hH.mem
  refine est impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 S j ujn hH hjl hle Q (fun S1 hA => ?_)
  rw [show Mdl.qhatEst _ _ _ _ _ _ = qhat from hqh] at hA
  have fr1 := hA.fr
  refine mul1 impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S S1 j qhat _ _ hM0 hA hqB Q
    (fun S2 hB2 hq2 hm1 hc2 hF2 => ?_)
  have hcz : ul = j + vl → natVal s.mem vp vl * qhat / 2 ^ (64 * vl) = 0 := by
    intro h; have := hcz0 h
    rwa [mav_carry _ _ (Asm.Wd_limbs _ _ _) hqB, Asm.val_limbs, Asm.length_limbs] at this
  refine sub1 impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S2 j qhat _ hB2 hq2 hc2 hjl hcz Q
    (fun S3 hB3 hq3 hql3 huj3 hcj3 hF3 htc3 hsv3 hbw3 => ?_)
  generalize hc : natVal s.mem vp vl * qhat / 2 ^ (64 * vl) = c at hcz hql3 hF3 htc3 hsv3 hc2
  have hqv : qhlOf j vl ul c = vl ∨ qhlOf j vl ul c = vl + 1 := by unfold qhlOf; split <;> simp
  have hqj : j + qhlOf j vl ul c ≤ ul := by
    unfold qhlOf; split
    · omega
    · rename_i h
      by_cases hc0 : c = 0
      · omega
      · have := mt hcz hc0; omega
  refine add1 impl hap R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S3 j qhat _ _ hB3 hq3 hql3 huj3 hcj3 rfl
    hqv hqj Q (fun S4 hK => ?_)
  obtain ⟨hB4, h04, h44, h74, h24, hF4, hz4, hnz4⟩ := hK
  generalize hbw : S3.mem.readLE ((s.regs 4).toNat - 152) 8 = bw at hsv3 hbw3 h24 hz4 hnz4
  generalize hq : qhlOf j vl ul c = q at hqv hqj hF3 hF4 hsv3 hnz4
  -- the word-level facts for `su_bridge`
  have htw := hl.tw; have huw := hl.uw; have htu := hl.tu; have ht48 := hl.t48; have hu48 := hl.u48
  have hU2 : ∀ i < ul, S2.mem.readLE (up + 8 * i) 8 = S.mem.readLE (up + 8 * i) 8 := fun i hi => by
    rw [hF2.readLE _ _ (by simp only [scr, outside_append, outside_cons, outside_nil, and_true]; omega),
      fr1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have hT : ∀ i < vl, S3.mem.readLE (t + 8 * i) 8 = S2.mem.readLE (t + 8 * i) 8 := fun i hi =>
    hF3.readLE _ _ (by simp only [scr, outside_append, outside_cons, outside_nil, and_true]; omega)
  have hU3 : ∀ i < ul, (i < j ∨ j + q ≤ i) → S3.mem.readLE (up + 8 * i) 8 = S2.mem.readLE (up + 8 * i) 8 :=
    fun i hi h => hF3.readLE _ _ (by simp only [scr, outside_append, outside_cons, outside_nil, and_true]; omega)
  have hU4 : ∀ i < ul, (i < j ∨ j + q ≤ i) → S4.mem.readLE (up + 8 * i) 8 = S3.mem.readLE (up + 8 * i) 8 :=
    fun i hi h => hF4.readLE _ _ (by simp only [scr, outside_append, outside_cons, outside_nil, and_true]; omega)
  obtain ⟨hsu1, hsu2⟩ := Asm.su_bridge S.mem S2.mem S3.mem S4.mem s.mem up ul vp vl t j qhat c bw q hqB hm1 hc.symm
    hU2 (by rw [← hq]) hqj hT htc3 hU3 hsv3 hbw3 hU4 (fun h i _ => hz4 h _ _) hnz4
  rw [← hsu2] at hst0
  refine tail impl R b L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 hE S4 j _ hB4 h04 h44 h74 h24
    (by split <;> omega) hjl hst0 Q (fun S5 hH5 hm5 => k S5 _ hH5 ?_)
  -- the invariant at `j`
  rw [← hsu2] at hdb
  rw [hdb] at hInv
  have hqw := hl.qw; have hqt := hl.tq; have hqu := hl.qu; have hq48 := hl.q48
  have hQ4 : ∀ i < ql, S4.mem.readLE (qp + 8 * i) 8 = S.mem.readLE (qp + 8 * i) 8 := fun i hi => by
    rw [hF4.readLE _ _ (by simp only [scr, outside_append, outside_cons, outside_nil, and_true]; omega),
      hF3.readLE _ _ (by simp only [scr, outside_append, outside_cons, outside_nil, and_true]; omega),
      hF2.readLE _ _ (by simp only [scr, outside_append, outside_cons, outside_nil, and_true]; omega),
      fr1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  generalize hqh2 : (if bw = 0 then qhat else (qhat + 2 ^ 64 - 1) % 2 ^ 64) = qh2 at hInv hst0 hm5
  have hu5 : Asm.limbs S5.mem up ul = Asm.limbs S4.mem up ul := Asm.limbs_ext fun i hi => by
    rw [hm5]
    by_cases h : skipQ j ul vl ql qh2
    · rw [if_pos h]
    · rw [if_neg h]; exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have hqh2B : qh2 < 2 ^ 64 := by rw [← hqh2]; split <;> omega
  have hq5 : Asm.limbs S5.mem qp ql = (if skipQ j ul vl ql qh2 then Asm.limbs S.mem qp ql
      else Mdl.upd (Asm.limbs S.mem qp ql) j [qh2]) := by
    split
    · rename_i h
      exact Asm.limbs_ext fun i hi => by rw [hm5, if_pos h]; exact hQ4 i hi
    · rename_i h
      have hjq := hst0 h
      rw [Asm.limbs_upd (m' := S5.mem) (m := S.mem) (j := j) (k := 1) (by omega) (fun i hi hh => by
        rw [hm5, if_neg h, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hQ4 i hi])]
      congr 1
      rw [Asm.limbs_one, hm5, if_neg h, Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by simpa using hqh2B)]
  show Mdl.DbInv _ _ _ _ _ (Asm.limbs S5.mem qp ql) (Asm.limbs S5.mem up ul) _
  rw [hq5, hu5, hsu1, ← Asm.limbs_getD _ _ _ _ (by omega : j + vl - 1 < ul), hsu1]
  exact hInv

end FvModexp.Amd64.Q.DivBasic
