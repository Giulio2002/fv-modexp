import FvModexp.Proofs.Arm64.Nat.DivBasicMemF
import FvModexp.Proofs.Arm64.Nat.DivBasicRec

/-!
# `divBasic` (arm64): the postcondition at the return (pure)

From the head memory `M` (`Mem`), the memory `E` at the closure call (defer bit cleared) and the memory `F` after the
closure (`len(stk.w)` restored, closure frame): `Post`, given the values of `q[0:qn]` and `u` in `M`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivBasic

/-- the ranges the closure writes -/
@[reducible] def wsF (sp st : Nat) : List (Nat × Nat) := [(sp - 264, sp - 248), (st + 8, st + 16)]

/-- `t` (in the stack's old free part or a fresh runtime block) is outside every range a caller keeps -/
theorem t_out {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    {a n : Nat} (h1 : Outside a n R.rt)
    (h2 : a + n ≤ stW s.mem st + 8 * stLen s.mem st ∨ stW s.mem st + 8 * stCap s.mem st ≤ a) :
    a + n ≤ t ∨ t + 8 * (vl + 1) ≤ a := by
  rcases hE.scr.loc with ⟨-, h3, h4⟩ | ⟨⟨r, hr, h3, h4⟩, -⟩
  · omega
  · have := MemFrame.outside_mem h1 hr; omega

theorem t_live {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1)
    {a n : Nat} (h1 : InRanges a n L)
    (h2 : a + n ≤ stW s.mem st + 8 * stLen s.mem st ∨ stW s.mem st + 8 * stCap s.mem st ≤ a) :
    a + n ≤ t ∨ t + 8 * (vl + 1) ≤ a := by
  rcases hE.scr.loc with ⟨-, h3, h4⟩ | ⟨-, hap⟩
  · omega
  · have := hap.apart_of_inRanges h1; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem post_fin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {qp ql st up ul uc vp vl vc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L qp ql st up ul uc vp vl s t L1 b1 w1 c1) {M E F : Memory}
    (hM : Mem R L qp ql st up ul uc vp vl vc s t L1 b1 w1 c1 M)
    (hq : vl ≤ ul → natVal M qp (qn ql ul vl) = natVal s.mem up ul / natVal s.mem vp vl)
    (hu : natVal M up ul = natVal s.mem up ul % natVal s.mem vp vl)
    (hFE : MemFrame M E [(s.sp.toNat - 137, s.sp.toNat - 136)])
    (hFF : MemFrame E F (wsF s.sp.toNat st)) (hlen : F.readLE (st + 8) 8 = stLen s.mem st)
    (s' : State) (hs' : s'.mem = F) :
    Post R b L qp ql st up ul vp vl s s' := by
  subst hs'
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1
  have hpre := hE.pre
  obtain ⟨-, -, -, hout, -, -, -, -⟩ := hpre.ce
  obtain ⟨hst8, hsth, hstacc, hst48, -, hslc, -⟩ := hpre.stok
  have hqn : qn ql ul vl ≤ ql := by unfold qn; split <;> omega
  have hsw := hl.sw; have hsq := hl.sq; have hsu := hl.su; have hts := hl.ts
  have hqw := hl.qw; have huw := hl.uw
  have hlsep := hl.lsep
  have hc1 := hE.c1len
  have mfr := hM.fr
  have mlf := hM.lf
  have hMF := mfTrans (mfTrans mfr hFE) hFF
  have hacc : ∀ a n w, s'.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hMF.accessible a n w
  have rdE : ∀ a n, (a + n ≤ s.sp.toNat - 4464 ∨ s.sp.toNat + 88 ≤ a) → (a + n ≤ st + 8 ∨ st + 16 ≤ a) →
      s'.mem.readLE a n = M.readLE a n := fun a n h1 h2 => by
    rw [hFF.readLE a n (by simp only [wsF, outside_cons, outside_nil, and_true]; omega),
      hFE.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have hW : s'.mem.readLE st 8 = w1 := by rw [rdE _ _ (by omega) (by omega)]; exact hM.hw
  have hC : s'.mem.readLE (st + 16) 8 = c1 := by rw [rdE _ _ (by omega) (by omega)]; exact hM.hcap
  refine ⟨fun h => ?_, ?_, L1, b1, hE.ext, hE.bud, ?inv, ?sb, ?mf, ?lf⟩
  · rw [← hq h]; exact rdE _ _ (by omega) (by omega)
  · rw [← hu]; exact rdE _ _ (by omega) (by omega)
  case inv =>
    refine RtInv.inv_frame' (mfTrans hFE hFF) (fun r hr => ?_) hM.inv
    simp only [wsF, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · left; exact hout.of_sub (by omega) (by omega)
    · left; exact hout.of_sub (by omega) (by omega)
    · have := (hE.ext.held hsth).sub (a := st + 8) (n := 8) (by omega) (by omega)
      rcases this with h | h
      · right; simpa using h
      · left; simpa using h
  case sb =>
    refine ⟨⟨hst8, hE.ext.held hsth, by rw [hacc]; exact hstacc, hst48, ?_, ?_, ?_⟩, hlen, ?_⟩
    · show NatLive s'.mem R L1 (s'.mem.readLE st 8) (s'.mem.readLE (st + 16) 8)
      rw [hW, hC]
      intro h0
      obtain ⟨a1, a2, a3, a4⟩ := hE.w1live h0
      exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
    · show s'.mem.readLE (st + 8) 8 ≤ s'.mem.readLE (st + 16) 8
      rw [hlen, hC]; omega
    · show s'.mem.readLE (st + 16) 8 < 2 ^ 40
      rw [hC]; exact hE.c1b
    · show (s'.mem.readLE st 8 = stW s.mem st ∧ s'.mem.readLE (st + 16) 8 = stCap s.mem st) ∨
        (InRanges (s'.mem.readLE st 8) (8 * s'.mem.readLE (st + 16) 8) R.rt ∧
          ApartAll (s'.mem.readLE st 8) (8 * s'.mem.readLE (st + 16) 8) L)
      rw [hW, hC]; exact hE.arr
  case mf =>
    refine hMF.mono fun a n ho => ?_
    simp only [winA, ws, wsL, wsF, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ := ho
    have ht := t_out hE h1 h7
    refine ⟨⟨⟨⟨⟨h1, h2, h3⟩, h4, h5, ht⟩, h6, h7⟩, ?_⟩, ?_, ?_⟩
    all_goals clear hlsep mlf mfr hMF hq hu hFF hFE rdE hacc; omega
  case lf =>
    refine ⟨fun a n hin ho => ?_⟩
    simp only [ws, stkWs, outside_cons, outside_nil, and_true] at ho
    obtain ⟨h4, h5, h6, h7⟩ := ho
    have ht := t_live hE hin h7
    obtain ⟨r, hr, i1, i2⟩ := hin
    have hr' := hlsep r hr
    rw [rdE _ _ (by omega) (by omega)]
    exact mlf.readLE a n ⟨r, hr, i1, i2⟩
      (by simp only [wsL, stkWs, outside_append, outside_cons, outside_nil, and_true]; omega)

end FvModexp.Arm64.DivBasic
