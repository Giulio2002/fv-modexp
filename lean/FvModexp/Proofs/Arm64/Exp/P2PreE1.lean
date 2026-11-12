import FvModexp.Proofs.Arm64.Exp.P2PreX
import FvModexp.Proofs.Common.StkFrame

/-!
# `buildPrecomputationWindowModPower2` (arm64): the call `buf = stk.nat((len + 1) w)` (nat.go:871) → fill loop
head `FillJ 0` (agent infra)

`ctx0`: the context `Ctx` after `stk.nat` (memory before the call framed by the function's own window stores).
`callSN`: at the `(*stack).nat` entry (`SP' = SP - 208`, return `0x1b544c` = 1791052), the call and the reloads
`R3 = powers`, `R4 = w`, `R5 = len`, `R1 = 0` → `FillJ 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs)

theorem sn_addr : segAddr Extracted.program StackNat.fn = 1784176 := by decide

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the stack header and array words are kept by the function's own window stores -/
theorem stk_win (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {M : Memory}
    (hF : MemFrame s.mem M (winA s (K kc) A)) :
    StkOK M R L st ∧ stW M st = stW s.mem st ∧ stLen M st = stLen s.mem st ∧ stCap M st = stCap s.mem st := by
  obtain ⟨hok, hstw, -, -⟩ := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine stkOK_frame hok hF ?_ (LiveExt.refl R L)
  simp only [win, winA, K, A, outside_cons, outside_nil, and_true] at hstw ⊢; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **the context after `stk.nat`** -/
theorem ctx0 (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {M : Memory}
    (hF : MemFrame s.mem M (winA s (K kc) A)) (hrg : M.regions = s.mem.regions) (hsl : Sl s st pw pl lm M)
    {S' s' : State} (hspN : S'.sp.toNat = s.sp.toNat - 208) (hm : S'.mem = M) {stk above : Nat} (hk : stk ≤ kc)
    (ha : above ≤ 88) (hrg' : s'.mem.regions = S'.mem.regions)
    {L' : List (Nat × Nat)} {b' : Nat} (hLE : LiveExt R L L') (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem))
    (hok : StkOK s'.mem R L' st) (hlen : stLen s'.mem st = stLen S'.mem st + StackNat.rnd (NB pl lm))
    (hsame : stLen S'.mem st + StackNat.rnd (NB pl lm) ≤ stCap S'.mem st →
      stW s'.mem st = stW S'.mem st ∧ stCap s'.mem st = stCap S'.mem st)
    (hgrow : stCap S'.mem st < stLen S'.mem st + StackNat.rnd (NB pl lm) →
      InRanges (stW s'.mem st) (8 * stCap s'.mem st) R.rt ∧ ApartAll (stW s'.mem st) (8 * stCap s'.mem st) L)
    (hF' : MemFrame S'.mem s'.mem (R.rt ++ winA S' stk above ++ stkWs S'.mem st))
    (hLF' : LiveFrame S'.mem s'.mem L (stkWs S'.mem st))
    (hmemb : stCap S'.mem st < stLen S'.mem st + StackNat.rnd (NB pl lm) →
      (stW s'.mem st, stW s'.mem st + 8 * stCap s'.mem st) ∈ L') :
    Ctx R kc L st pw pl lm s (stW s'.mem st + 8 * stLen s.mem st) s'.mem L' b' := by
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  have hrt := hf.w.rt
  have hhd := hf.w.hd
  have har := hf.w.ar
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hK hrt hhd har
  obtain ⟨-, e0, e1, e2⟩ := stk_win hpre hF
  subst hm
  simp only [e0, e1, e2] at hsame hgrow hlen hmemb
  have hsfree := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hstk := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨-, hsth, -, -, -, -, -⟩, -, -, -⟩ := hstk
  have hnb : 0 < NB pl lm := Nat.mul_pos (by have := (pl_facts hpre).1; omega) (w_facts hpre).1
  have hws : stkWs S'.mem st = stWs s.mem st := by simp only [stWs, stkWs]; rw [e0, e1, e2]
  -- the frame
  have hfr : MemFrame s.mem s'.mem (AW R kc s pw pl st) := by
    refine hF.trans hF' fun a n h => ?_
    simp only [AW, LW, outside_append] at h
    obtain ⟨⟨h1, h2⟩, -, h4⟩ := h
    refine ⟨h2, ?_⟩
    rw [hws]
    simp only [outside_append]
    refine ⟨⟨h1, ?_⟩, h4⟩
    simp only [winA, K, A, outside_cons, outside_nil, and_true] at h2 ⊢
    rw [hspN]; omega
  have hlf : LiveFrame s.mem s'.mem L (LW s pw pl st) := by
    refine LiveFrame.trans (L' := L) ?_ (LiveFrame.mono_ws hLF' fun a n h => ?_) fun a n h => h
    · refine Expmc.liveFrame_of_frame hF fun a n hin _ => ?_
      obtain ⟨r, hr, h1, h2⟩ := hin
      have := hf.ls r hr
      simp only [win, winA, K, A, outside_cons, outside_nil, and_true] at this ⊢; omega
    · rw [hws]; simp only [LW, outside_append] at h; exact h.2
  -- the scratch nat
  have hscr : Scr R L L' s.mem s'.mem st (stW s'.mem st + 8 * stLen s.mem st) (NB pl lm) :=
    Scr.of_post hok hlen hnb hsame hgrow rfl
  have hsa : StkAfter R L L' st (stLen s.mem st) pl lm s.mem s'.mem := by
    refine ⟨hok, hlen, ?_⟩
    by_cases hc : stLen s.mem st + StackNat.rnd (NB pl lm) ≤ stCap s.mem st
    · exact Or.inl (hsame hc)
    · exact Or.inr (hgrow (by omega))
  have hsap : StkApart s'.mem st (stW s'.mem st + 8 * stLen s.mem st) (8 * NB pl lm) := by
    intro _
    refine ⟨?_, fun _ => by rw [hlen]; unfold Apart; simp only [StackNat.rnd]; omega⟩
    rcases hscr.loc with ⟨h0, l1, l2⟩ | ⟨hin, hap⟩
    · have := hsfree; unfold Apart at this ⊢; omega
    · rcases hsth with hL | hO
      · exact hap.apart_of_inRanges hL
      · exact (hin.apart hO).symm
  have hain : ArrIn L' st s.mem s'.mem := by
    intro hne
    by_cases hc : stLen s.mem st + StackNat.rnd (NB pl lm) ≤ stCap s.mem st
    · exact absurd (hsame hc) hne
    · exact hmemb (by omega)
  have hbu : BU s'.mem st (stW s'.mem st + 8 * stLen s.mem st) (8 * NB pl lm) := by
    left; rw [hlen]; simp only [StackNat.rnd]; omega
  refine ⟨hfr, hlf, hrg'.trans hrg, hLE, hinv, hscr, hsa, hsap, ?_, hain, hbu⟩
  refine sl_keep (L := L) (L1 := L) hf.w hspN hk ha (fun r hr => ?_) hF' hsl
  simp only [stkWs, List.mem_cons, List.not_mem_nil, or_false] at hr
  intro hlt
  rcases hr with rfl | rfl
  · right; left; simp only; omega
  · left; simp only at hlt ⊢; rw [e0, e1, e2] at hlt ⊢; omega

set_option maxRecDepth 20000 in
/-- the callee environment at `SP' = SP - 208` before `stk.nat` (memory framed by the own window stores) -/
theorem cenv0 (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {M : Memory}
    (hF : MemFrame s.mem M (winA s (K kc) A)) (hrg : M.regions = s.mem.regions) :
    CallW.CEnv R L (s.regs 28).toNat (s.sp.toNat - 208) kc 88 M := by
  have hFA : MemFrame s.mem M (AW R kc s pw pl st) :=
    hF.mono fun a n h => by simp only [AW, outside_append] at h; exact h.1.2
  have hgk := guard_keep hpre hFA
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgrt, hLs, hro⟩, -, -, -, -, -, -, -, -, hacc, -, -, -,
    -, -, ⟨-, hxa, -, -, -⟩, -, -, -, ⟨⟨-, -, hsta, -, hstl, -, -⟩, -⟩, -⟩ := hpre
  simp only [K, A] at hb' ha hw hout hga hg3 hLs
  unfold Apart at hga
  refine ⟨by omega, by omega, by omega, ?_, hg1, by rw [hF.accessible]; exact hg2, by rw [hgk]; omega,
    hout.of_sub (by omega) (by omega), by unfold Apart; omega, hgrt, ?_, ?_, hro⟩
  · rw [hF.accessible]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · intro q hq
    have := hLs q hq
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
  · refine dataLoaded_frame hd hrg hro (by simpa only [AW, List.append_assoc] using hFA) ?_
    intro r hr hlt
    simp only [winA, LW, stWs, stkWs, K, A, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl | rfl | rfl
    · dsimp only at hlt ⊢; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · dsimp only at hlt ⊢; exact Memory.accessible_mono _ hw (by omega) (by omega)
    · dsimp only at hlt ⊢; rw [show pw + 24 * pl - pw = 24 * pl by omega]; exact hacc
    · dsimp only at hlt ⊢; rw [show st + 24 - st = 24 by omega]; exact hsta
    · dsimp only at hlt ⊢
      exact Memory.accessible_mono _ (hstl (by omega)).2.2.1 (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `stk.nat`'s precondition at its entry (`SP' = SP - 208`) -/
theorem snPre {stkS aboveS : Nat} (hkS : stkS ≤ kc) (haS : aboveS ≤ 88) (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {M : Memory}
    (hF : MemFrame s.mem M (winA s (K kc) A)) (hrg : M.regions = s.mem.regions)
    {S' : State} (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 208)) (h28 : S'.regs 28 = s.regs 28) (hm : S'.mem = M) :
    StackNat.Pre R b L stkS aboveS st (NB pl lm) S' := by
  have hsl0 := s.sp.isLt
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  have hhd := hf.w.hd
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hK hhd
  have hspN : S'.sp.toNat = s.sp.toNat - 208 := by
    rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hnb := nb_le hpl16 hw128
  obtain ⟨hok, e0, e1, e2⟩ := stk_win hpre hF
  obtain ⟨hce, hsv, hgl, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hsta⟩, hstl, hsfree, -, hcost,
    hinv, -, -⟩ := id hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, g11, -, g13⟩ := hgl
  have hrtw : Outside (s.sp.toNat - (208 + kc)) (208 + kc + 80) R.rt := by have := hf.w.rt; simpa only [K, A] using this
  have hsnc : stackNatCost (stLen s.mem st) (NB pl lm) ≤ b := by
    have := Nat.le_trans (Nat.le_add_right _ _) hcost; simp only [c0] at this; omega
  subst hm
  simp only [StackNat.Pre]
  rw [e0, e1, e2]
  refine ⟨CallW.callEnv_of (cenv0 hpre hF hrg) hsp (by rw [h28, BitVec.ofNat_toNat, BitVec.setWidth_eq]) rfl hkS
      haS, hsv, hok, ?_, fun hc0 => ?_, by omega, by omega, hsnc, ?_, by rw [hF.accessible]; exact g11, ?_, hsfree⟩
  · simp only [win, outside_cons, outside_nil, and_true]; rw [hspN]; omega
  · obtain ⟨o1, o2⟩ := hsta hc0
    refine ⟨?_, by rw [h28]; exact o2⟩
    simp only [win, K, A, outside_cons, outside_nil, and_true] at o1 ⊢
    rw [hspN]; omega
  · rw [h28]
    refine Expmc.inv_frame hF (fun r hr => Or.inr ?_) hinv
    simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (dsimp only; simp only [K, A]; exact hrtw.of_sub (by omega) (by omega))
  · have v1 : RunIface.wbA = 7616064 := rfl
    have v2 : StackNat.wbA = 7616064 := rfl
    have v3 : Extracted.dataAddr.«runtime.writeBarrier» = 7616064 := rfl
    simp only [LW, stWs, stkWs, winA, K, A, outside_append, outside_cons, outside_nil, and_true, v1] at g13
    simp only [v2]
    unfold Apart; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`buf = stk.nat((len+1) w)`** from the callee entry, then the reloads → `FillJ 0` -/
theorem callSN (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkS aboveS : Nat} (hsn : StackNat.HypL impl R ns stkS aboveS) (hkS : stkS ≤ kc) (haS : aboveS ≤ 88)
    (hkc : 4608 ≤ kc) (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s)
    (kF : FillJ impl R kc sqC mlC b L st pw pl lm x xl s 0) {M : Memory}
    (hF : MemFrame s.mem M (winA s (K kc) A)) (hrg : M.regions = s.mem.regions) (hsl : Sl s st pw pl lm M)
    (S' : State) (hsp : S'.sp = BitVec.ofNat 64 (s.sp.toNat - 208)) (h28 : S'.regs 28 = s.regs 28)
    (h29 : S'.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216)) (h18 : S'.regs 18 = s.regs 18) (hm : S'.mem = M)
    (hpc : S'.pc = BitVec.ofNat 64 1784176) (h30 : S'.regs 30 = BitVec.ofNat 64 1791052)
    (h0 : S'.regs 0 = BitVec.ofNat 64 st) (h1 : S'.regs 1 = BitVec.ofNat 64 (NB pl lm)) :
    ReachesRet (LibExp.program.link impl) (s.regs 30) S' (GoalQ R kc sqC mlC b L st pw pl lm x xl s) := by
  have hsl0 := s.sp.isLt
  have hK : 208 + kc ≤ s.sp.toNat := by have := hpre.1.2.1.2.1; simpa only [K] using this
  have hspN : S'.sp.toNat = s.sp.toNat - 208 := by
    rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨hok, e0, e1, e2⟩ := stk_win hpre hF
  have hnb0 : 0 < NB pl lm := Nat.mul_pos (by have := (pl_facts hpre).1; omega) (w_facts hpre).1
  have hnb := nb_le (pl_facts hpre).2.1 (w_facts hpre).2
  refine LibCalls.stkNatCallL hap hns hsn (b := b) (L := L) (ra_bp hap hnf 31 (by decide)) (by rw [hpc, sn_addr]) h30
    h0 h1 (by have := hok.2.2.2.1; omega) (by omega) (by decide) (snPre hkS haS hkc hpre hF hrg hsp h28 hm)
    fun s' hpc' hsp' h28' h29' h18' hrg' hpost => ?_
  obtain ⟨hr0, hr1, hr2, L', b', ⟨hLE, hbud, hinv'⟩, hok', hlen, hsame, hgrow, hF', hLF', hmemb⟩ := hpost
  have hc := ctx0 hpre hkc hF hrg hsl hspN hm hkS haS hrg' hLE (by rw [h28] at hinv'; exact hinv') hok' hlen hsame
    hgrow hF' hLF' hmemb
  rw [hm, e1] at hr0 hbud
  have hr0' := hr0 hnb0
  obtain ⟨-, -, -, f3, f4, -, f6, -, -, -, -, -⟩ := hc.sl
  have f224 : s'.mem.readLE (s.sp.toNat - 208 + 224) 8 = pw := by
    rw [show s.sp.toNat - 208 + 224 = s.sp.toNat + 16 by omega]; exact f3
  have f232 : s'.mem.readLE (s.sp.toNat - 208 + 232) 8 = pl := by
    rw [show s.sp.toNat - 208 + 232 = s.sp.toNat + 24 by omega]; exact f4
  have f144 : s'.mem.readLE (s.sp.toNat - 208 + 144) 8 = W lm := by
    rw [show s.sp.toNat - 208 + 144 = s.sp.toNat - 64 by omega]; exact f6
  have hsp2 : s'.sp = BitVec.ofNat 64 (s.sp.toNat - 208) := hsp'.trans hsp
  have hwm : s'.mem.accessible (s.sp.toNat - (208 + kc)) (208 + kc + 80) true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2.2; simpa only [K, A] using this
  have h29' := h29'.trans h29
  have h28' := h28'.trans h28
  have h18' := h18'.trans h18
  have hpreH : Hide (Pre R kc sqC mlC b L st pw pl ws lm x xl s) := ⟨hpre⟩
  have hcH : Hide (Ctx R kc L st pw pl lm s (stW s'.mem st + 8 * stLen s.mem st) s'.mem L' b') := ⟨hc⟩
  clear hF' hLF' hF hsame hgrow hpre hc hok hok' hsl hLE hinv' e0 e2 hlen
  have hpc2 : s'.pc = BitVec.ofNat 64 1791052 := hpc'
  obtain ⟨hal, -, ha, -⟩ := hpreH.h.1.2.1
  simp only [K, A] at ha
  clear hpc' hsp'
  janus_run [f224, f232, f144] until [pcF]
  refine kF _ _ L' b' rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcH.h (fun j hj => absurd hj (Nat.not_lt_zero _)) (Nat.zero_le _)
    hbud
  all_goals janus_simp

end

end FvModexp.Arm64.P2Pre
