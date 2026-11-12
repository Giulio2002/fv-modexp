import FvModexp.Proofs.Arm64.Exp.P2PreCall

/-!
# `buildPrecomputationWindowModPower2` (arm64): `runtime.memmove(dst, src, 8)` into `buf` (agent infra)

`mvCall`: at the `memmove` contract (`SP' = SP - 208`) with `dst = [d, d + 8)` inside `buf` and a readable source
outside the window: the continuation gets the return state with the context, the kept reads (`powers`, `buf` apart
from `dst`, the frame above the callee's argument area) and the copied word.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs)

/-- `runtime.memmove`'s contract address -/
abbrev mvE : Nat := 609408

theorem mvE_eq : cA "runtime.memmove" = mvE := by decide

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem mvCall (hmv : MemmoveLive (LibExp.program.link impl) mvE 4096 R)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (hkc : 4608 ≤ kc) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat} (hc : Ctx R kc L st pw pl lm s bp M L1 b1) {r : W64} {Q : State → Prop}
    {S : State} (hpc : S.pc = BitVec.ofNat 64 mvE) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 208))
    (h28 : S.regs 28 = s.regs 28) (hm : S.mem = M) {ra : Nat} (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (hra4 : ra % 4 = 0) (hra48 : ra < 2 ^ 48) {d src : Nat} (h0 : S.regs 0 = BitVec.ofNat 64 d)
    (h1 : S.regs 1 = BitVec.ofNat 64 src) (h2 : S.regs 2 = BitVec.ofNat 64 8)
    (hd1 : bp ≤ d) (hd2 : d + 8 ≤ bp + 8 * NB pl lm)
    (hsa : M.accessible src 8 false = true) (hs48 : src + 8 ≤ 2 ^ 48)
    (hsw : src + 8 ≤ s.sp.toNat - 208 - 4096 ∨ s.sp.toNat - 208 + 32 ≤ src)
    (k : ∀ (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory) (ex : Option (Nat × Nat))
      (ep : Nat → Bool), Ctx R kc L st pw pl lm s bp m L1 b1 →
      (∀ a n, 0 < n → ((pw ≤ a ∧ a + n ≤ pw + 24 * pl) ∨ (bp ≤ a ∧ a + n ≤ bp + 8 * NB pl lm) ∨
        (s.sp.toNat - 176 ≤ a ∧ a + n ≤ s.sp.toNat + 80)) → (a + n ≤ d ∨ d + 8 ≤ a) → m.readLE a n = M.readLE a n) →
      m.readLE d 8 = M.readLE src 8 →
      ReachesRet (LibExp.program.link impl) r (retStateX S junk [] f v m ex ep) Q) :
    ReachesRet (LibExp.program.link impl) r S Q := by
  have hf := pf_of hpre (by omega)
  have hK := hf.w.sp
  simp only [K] at hK
  have hsl := s.sp.isLt
  have hspN : S.sp.toNat = s.sp.toNat - 208 := by
    rw [hsp, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hce := callEnv_ctx hpre hc hsp h28 hm (stk := 4096) (above := 32) (by omega) (by omega)
  obtain ⟨hgd, ⟨hal, hb', ha8, hw⟩, -, hout, hga, -, hLs, -⟩ := hce
  simp only [win] at hLs
  rw [hspN] at hb' ha8 hw hout hga hLs
  have hsv := hpre.2.1
  have hok : R.ok mvE [d, src, 8] := by rw [← mvE_eq]; exact hsv.2.1 d src 8 (by decide)
  obtain ⟨o48, oacc, oheld, owin, -, -⟩ := bufObj hpre hc hf (S' := S) hspN (stk := 4096) (above := 32)
    (by omega) (by omega) (a := d) (n := 8) hd1 hd2 (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at owin
  rw [hspN] at owin
  have t0 : (BitVec.ofNat 64 d).toNat = d := by rw [BitVec.toNat_ofNat]; omega
  have t1 : (BitVec.ofNat 64 src).toNat = src := by rw [BitVec.toNat_ofNat]; omega
  have t2 : (BitVec.ofNat 64 8 : BitVec 64).toNat = 8 := rfl
  have hr30 : (S.regs 30).toNat = ra := by rw [h30, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ra < 2 ^ 64 by omega)]
  rw [hspN] at hal
  rw [hm] at hw
  unfold Apart at hga
  refine ReachesRet.call_regions (hmv L1 b1) hpc ?_ ?_
  · simp only [Mem.EqPre, CallOK, LiveMemAt, Mem.Input, LiveDest, calleeStack, hspN, h0, h1, h2,
      hr30, hm, t0, t1, t2, outside_cons, outside_nil, and_true]
    refine ⟨⟨(guardOK_iff S 4096).1 hgd, ⟨by omega, by omega, hal, by omega, by omega, by omega,
      Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)⟩, by omega⟩, ⟨hok, by rw [h28]; exact hc.inv, ?_, ?_⟩,
      ⟨hs48, hsa, by omega⟩, ⟨o48, oacc, by omega, oheld⟩⟩
    · intro r' hr'
      have := hLs r' hr'
      simp only [outside_cons, outside_nil, and_true] at this ⊢
      omega
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact hout.of_sub (by omega) (by simp only; omega)
      · exact hout.of_sub (by simp only; omega) (by simp only; omega)
  intro S2 _ ⟨junk, f2, v2, m', ex2, ep2, hs2, hfr2, hlf2, hinv2, hcp⟩ hrg0
  subst hs2
  simp only [h0, h1, h2, t0, t1, t2, hm, calleeStack] at hfr2 hlf2 hinv2 hcp
  rw [hspN] at hfr2
  rw [h28] at hinv2
  have hrg : m'.regions = M.regions := by rw [← hm]; exact hrg0
  have hws : ∀ r' ∈ [(d, d + 8)], WOK R L s st r' := by
    intro r' hr'; simp only [List.mem_singleton] at hr'; subst hr'; exact wok_buf hc.scr hd1 hd2
  have hF' : MemFrame M m' (R.rt ++ winA S 4096 32 ++ [(d, d + 8)]) := hfr2.mono fun a n ho => by
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    rw [hspN] at ho; exact ⟨⟨ho.1.1, ho.1.2.1, by omega⟩, ho.2⟩
  have hsah := sa_hdr' hc.ain hc.bu hc.sa hc.sap (LiveExt.refl R L1) (fun b n h1 h2 => by
      have hd := hf.w.hd
      simp only [win, K, A, outside_cons, outside_nil, and_true] at hd
      have hz := (bufObj hpre hc hf (S' := S) hspN (stk := 4096) (above := 32) (by omega) (by omega)
        (a := d) (n := 8) hd1 hd2 (by omega)).2.2.2.2.2 (by omega)
      unfold Apart at hz
      exact rd_keep hf.w hspN (by omega) (by omega) hF' hlf2 (hc.sa.1.2.1.sub h1 h2) (by simp only [K, A]; omega)
        fun r hr hr' => by simp only [List.mem_singleton] at hr; subst hr; simp only at hr' ⊢; omega)
    hF'.accessible
  have hc2 := keepC hc hf.w hspN (by omega) (by omega) hws hF' hlf2 hrg (LiveExt.refl R L1) hinv2 hsah.1 hsah.2.1 hsah.2.2.1 hsah.2.2.2
  refine k junk f2 v2 m' ex2 ep2 hc2 (fun a n h0' hr hd => ?_) ?_
  · rcases hr with hr | hr | hr
    · exact pw_rd hf (hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (by have := (pl_facts hpre).1; omega) hspN
        (kC := 4096) (aC := 32) (by omega) (by omega) hws hF' hlf2 hr.1 hr.2
    · exact buf_rd hc hf hspN (kC := 4096) (aC := 32) (by omega) (by omega) (zp := d) (zn := 8)
        (fun r hr => List.mem_append_left _ hr) hF' hlf2 hr.1 hr.2 h0' (by unfold Apart; omega)
    · refine frame_read hF' fun r' hr' hr'' => ?_
      simp only [List.mem_append, winA, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with (hr' | hr' | hr') | hr'
      · have := MemFrame.outside_mem (hf.w.rt.of_sub (a := a) (n := n) (by simp only [K]; omega)
          (by simp only [K, A]; omega)) hr'; omega
      · subst hr'; simp only at hr'' ⊢; rw [hspN]; omega
      · subst hr'; simp only at hr'' ⊢; rw [hspN]; omega
      · subst hr'; simp only at hr'' ⊢; omega
  · exact Expmc.readLE_of_copied hcp

end

end FvModexp.Arm64.P2Pre
