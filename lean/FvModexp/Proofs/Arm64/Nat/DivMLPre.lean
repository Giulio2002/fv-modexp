import FvModexp.Proofs.Arm64.Nat.DivMStk
import FvModexp.Proofs.Arm64.Nat.DivBigP

set_option autoImplicit false

/-!
# `nat.div` (arm64), `stk == nil`, `z = nil`, `z2 = u`: `divLarge`'s precondition at its entry (pure)

After `getStack()` (memory `M`: `s.mem → M` writes only `R.rt` and the window, the new stack `st` with `NewStk`, live
set `L1 = L ++ stkRs M st`, budget `b1 ≥ b - 24`): `DivLarge.Pre` for `nil.divLarge(st, u, u, v)` at the entry `X`
(`SP' = SP - 240`, `X.mem = M`). The stack facts come from `NewStk` (a fresh, empty stack in `R.rt`); `u`, `v` are
held (`L` or outside `R.rt`), hence apart from it.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.DivNil

namespace FvModexp.Arm64.NatDiv

set_option maxRecDepth 20000 in
theorem apartG {x g s0 sx : Nat} (e : x = g) (hsp : sx = s0 - 240) (hb : 41504 ≤ s0)
    (h : g + 16 + 8 ≤ s0 - 41504 ∨ s0 - 41504 + (41504 + 112) ≤ g + 16) :
    Apart (x + 16) 8 (sx - 41264) (41264 + 112) := by
  unfold Apart; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem l_preM {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vl : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl s)
    {L1 : List (Nat × Nat)} {b1 st : Nat} {M : Memory}
    (hN : NewStk R L L1 b b1 (s.regs 28).toNat M st)
    (hF : MemFrame s.mem M (R.rt ++ winA s 41504 112)) (hLF : LiveFrame s.mem M L [])
    (hreg : M.regions = s.mem.regions)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl)
    (X : State) (hsp : X.sp = s.sp - 240#64) (h28 : X.regs 28 = s.regs 28) (hm : X.mem = M) :
    DivLarge.Pre R b1 L1 (DivLarge.cost dc (stLen X.mem st) ul vl) 0 0 st u uc u ul v vl X := by
  subst hm
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hp.ce
  unfold Apart at hga
  have hspn : X.sp.toNat = s.sp.toNat - 240 := by
    rw [hsp, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  obtain ⟨x1, x2, x3, x4, -⟩ := spX hsp (by omega)
  have hwin : ∀ a n, Outside a n (win s 41504 112) → Outside a n (win X 41264 112) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true, x1, x4] at h ⊢; omega
  have hacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := hF.accessible
  have hwO : Outside (s.sp.toNat - 41504) (41504 + 112) R.rt := hout
  -- the held inputs keep their words
  have hrdH : ∀ a n, (InRanges a n L ∨ Outside a n R.rt) → Outside a n (win s 41504 112) →
      X.mem.readLE a n = s.mem.readLE a n := by
    intro a n hh ho
    simp only [win, outside_cons, outside_nil, and_true] at ho
    rcases hh with hin | hr
    · exact hLF.readLE a n hin trivial
    · exact hF.readLE a n (by
        simp only [outside_append, winA, outside_cons, outside_nil, and_true]; exact ⟨hr, by omega, by omega⟩)
  have hvl : vl ≤ ul := by
    rcases Nat.lt_or_ge (natVal s.mem v vl) (natVal s.mem u ul) with h1 | h1
    · exact len_le_of_lt hp.vn h1
    · have : natVal s.mem u ul = natVal s.mem v vl := by omega
      rcases hp.vn with h0 | ht
      · omega
      · refine Nat.le_of_not_lt fun hc => ?_
        have h2 := natVal_ge1 s.mem v vl (by omega) ht
        have h3 := natVal_lt s.mem u ul
        have h4 : 2 ^ (64 * ul) ≤ 2 ^ (64 * (vl - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
  have hui := hp.ui.2 (by omega)
  have hvo := hp.vo
  obtain ⟨hu40, huacc, hu48, huh, huw⟩ := hui
  obtain ⟨hv40, hvacc, hv48, hvh, hvw⟩ := hvo
  -- the new stack
  obtain ⟨hL1, hrs, hst0, hst8, hst48, hstacc, hlen, hcap, hc0, hw8, hw48, hwacc, hdis, hbb, hbb', hinv1⟩ := hN
  have hN : NewStk R L L1 b b1 (s.regs 28).toNat X.mem st :=
    ⟨hL1, hrs, hst0, hst8, hst48, hstacc, hlen, hcap, hc0, hw8, hw48, hwacc, hdis, hbb, hbb', hinv1⟩
  obtain ⟨hhin, hhap⟩ := hN.hdr
  have hhO := out_inR2 hwO hhin
  have hhG := out_inR2 hgr hhin
  obtain ⟨-, -, -, -, -, -, -, -, hgArt, hgAw, -, hwbrt, -⟩ := hp.gl
  have hhgA := out_inR2 hgArt hhin
  have hhwb := out_inR2 hwbrt hhin
  have hgaX : Apart ((X.regs 28).toNat + 16) 8 (X.sp.toNat - 41264) (41264 + 112) := by
    have e : (X.regs 28).toNat = (s.regs 28).toNat := congrArg BitVec.toNat h28
    exact apartG e hspn hb' hga
  -- array facts (`cap > 0`)
  have harrF : 0 < stCap X.mem st → Outside (s.sp.toNat - 41504) (41504 + 112) [(stW X.mem st, stW X.mem st + 8 * stCap X.mem st)] ∧
      InRanges (stW X.mem st) (8 * stCap X.mem st) R.rt := by
    intro hc
    obtain ⟨hin', -⟩ := hN.arr hc
    have := out_inR2 hwO hin'
    exact ⟨by simp only [outside_cons, outside_nil, and_true]; omega, hin'⟩
  have hUap := hN.apart (a := u) (k := 8 * ul) huh
  have hVap := hN.apart (a := v) (k := 8 * vl) hvh
  unfold DivLarge.Pre
  refine ⟨?ce, hp.sv, globals_win hp.gl (hF.mono fun a n h => h) ?gw (fun a n h => hwin a n h),
    ⟨by decide, by simp, fun h => absurd h (by decide)⟩, ?uo, ?ui, ?vi, hv2, hvl, hp.ul9, ?vn,
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun hc => (hp.ug hc).1, Or.inl rfl, ?stk,
    by rw [hlen]; have := hp.ul9; omega, fun h => absurd h (by decide), ?uS, ⟨hUap.1, ?uF⟩, ⟨hVap.1, ?vF⟩,
    ?wb, ?hfree, ⟨hc0, by omega⟩, ⟨fun h => absurd h (by decide), fun hc => (hp.ug hc).2, ?sg, ?fg⟩, ?cost, ?inv⟩
  case ce =>
    refine ⟨⟨by rw [h28]; exact hg1, by rw [h28, hacc]; exact hg2, ?_⟩, ⟨by rw [hspn]; omega, by rw [hspn]; omega,
      by rw [hspn]; omega, by rw [hacc, hspn]; exact Memory.accessible_mono _ hw (by omega) (by omega)⟩, ?_,
      by rw [hspn]; exact hout.of_sub (by omega) (by omega), hgaX,
      by rw [h28]; exact hgr, ?_, hro⟩
    · rw [h28, hF.readLE _ _ (by
        simp only [outside_append, winA, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, by omega⟩), hspn]
      omega
    · exact dataLoaded_win hdl hreg hro hF hw (by
        intro r hr; simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)
    · refine LiveSep.sub_win (lo := s.sp.toNat - 41504) (hi := s.sp.toNat + 112) ?_ (by rw [hspn]; omega)
        (by rw [hspn]; omega)
      exact hN.liveSep hLs (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; simp only
        rw [show s.sp.toNat + 112 - (s.sp.toNat - 41504) = 41504 + 112 by omega]; exact hwO)
  case gw =>
    simp only [win, winA, outside_append, outside_cons, outside_nil, and_true] at hgAw ⊢
    exact ⟨hgArt, by omega, by omega⟩
  case uo =>
    obtain ⟨h1, h2, h3⟩ := hp.uo
    refine ⟨h1, fun hc => ?_, fun hc => ⟨hwin _ _ (h3 hc).1, by rw [h28]; exact (h3 hc).2⟩⟩
    obtain ⟨a1, a2, a3, a4⟩ := h2 hc; exact ⟨a1, hN.held a2, by rw [hacc]; exact a3, a4⟩
  case ui => exact ⟨hu40, by rw [hacc]; exact huacc, hu48, hN.held huh, hwin _ _ huw⟩
  case vi => exact ⟨hv40, by rw [hacc]; exact hvacc, hv48, hN.held hvh, hwin _ _ hvw⟩
  case vn =>
    rcases hp.vn with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [hrdH _ _ (hvh.sub (by omega) (by omega)) (hvw.of_sub (by omega) (by omega))]; exact h
  case stk =>
    refine ⟨⟨hst8, Or.inl ⟨(st, st + 24), by rw [hL1]; exact List.mem_append_right _ (List.mem_cons_self ..),
      by simp only; omega, by simp only; omega⟩, hstacc, hst48, fun hc => ⟨hw8, Or.inl ?_, hwacc hc, hw48⟩,
      by omega, hcap⟩, ?_, by rw [h28]; unfold Apart; omega, fun hc => ⟨?_, ?_⟩⟩
    · refine ⟨(stW X.mem st, stW X.mem st + 8 * stCap X.mem st), ?_, by simp only; omega, by simp only; omega⟩
      rw [hL1]; refine List.mem_append_right _ ?_
      simp only [stkRs]; rw [if_neg (show ¬(stCap X.mem st = 0) by omega)]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · simp only [win, outside_cons, outside_nil, and_true, x1, x4]; omega
    · have := (harrF hc).1; simp only [win, outside_cons, outside_nil, and_true, x1, x4] at this ⊢; omega
    · have := out_inR2 hgr (harrF hc).2; rw [h28]; unfold Apart; omega
  case uS => intro hc; exact hN.apart (hp.uo.2.1 hc).2.1
  case uF => exact hUap.2
  case vF => exact hVap.2
  case wb => show Apart st 24 RunIface.wbA 4; unfold Apart; omega
  case hfree =>
    rw [hlen]; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]; exact hdis
  case sg => unfold Apart; omega
  case fg =>
    rw [hlen]; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
    rcases Nat.eq_zero_or_pos (stCap X.mem st) with hc | hc
    · rw [hc]; unfold Apart; omega
    · have := out_inR2 hgArt (harrF hc).2; unfold Apart; omega
  case cost =>
    have := hp.cost; rw [hlen]; simp only [costM, cost] at this; omega
  case inv => rw [h28]; exact hinv1

end FvModexp.Arm64.NatDiv
