import FvModexp.Proofs.Amd64.NatQ.DivMJoin
import FvModexp.Proofs.Amd64.NatQ.DivBigP
import FvModexp.Proofs.Amd64.Nat.DivmcCall

set_option autoImplicit false

/-!
# `nat.div` (amd64), `stk == nil`, `z = nil`, `z2 = u`: `divLarge`'s precondition at its entry (pure) (top s41)

Twin of Arm64/NatQ/DivMLPre.lean. After `getStack()` and the join (`X` = `divLarge`'s entry, `AtLM`): `s.mem → X.mem`
writes only `R.rt` and `nat.div`'s window, the new stack `st` with `NewStk` (live set `L1 = L ++ stkRs X.mem st`, budget
`b1 ≥ b - 24`). Result: `DivLarge.Pre` for `nil.divLarge(st, u, u, v)` (`H = 16·len u + 64`, `len stk = 0`).
`CallEnv.calleeRt`: `CallEnv.callee` (Amd64/Nat/DivmcCall.lean) for a frame that also covers `R.rt`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Amd64.DivNil

namespace FvModexp.Amd64

set_option maxRecDepth 20000 in
theorem CallEnv.calleeRt {R : RtInv} {L : List (Nat × Nat)} {s s1 : State} {stk above d stk1 above1 : Nat}
    (h : CallEnv R L s stk above) (hsp : (s1.regs 4).toNat = (s.regs 4).toNat - d) (hg : s1.regs 14 = s.regs 14)
    (hfs : s1.fsBase = s.fsBase) (hd8 : d % 8 = 0) (hk : d + stk1 ≤ stk) (ha : above1 ≤ d + above)
    (hF : MemFrame s.mem s1.mem (R.rt ++ win s stk above)) (hreg : s1.mem.regions = s.mem.regions) :
    CallEnv R L s1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha', hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := h
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb ha' hw
  unfold Apart at hga htw
  have hO : ∀ a n, Outside a n R.rt → (a + n ≤ (s.regs 4).toNat - stk ∨ (s.regs 4).toNat + above ≤ a) →
      Outside a n (R.rt ++ win s stk above) := fun a n h1 h2 => by
    simp only [outside_append, win, outside_cons, outside_nil, and_true]; exact ⟨h1, by omega⟩
  have hgr' : s1.mem.readLE ((s1.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hg]; exact hF.readLE _ _ (hO _ _ hgr (by omega))
  have htls : s1.mem.readLE (s1.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
    rw [hfs]; exact hF.readLE _ _ (hO _ _ htrt (by omega))
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [stackguard0Offset, regG]; rw [hg]; exact hg1
  · simp only [stackguard0Offset, regG]; rw [hg, hF.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [hg] at hgr' ⊢; rw [hgr', hsp]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; rw [hF.accessible, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · omega
  · exact dataLoaded_frame64 hdl hreg hro hF (by
      intro r hr _; simp only [win, List.mem_singleton] at hr; subst hr
      simp only; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · rw [hg]; exact hgr
  · intro r hr; have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega
  · rw [hfs]; exact htb
  · rw [hfs, hF.accessible]; exact htr
  · rw [htls, htg, hg]
  · rw [hfs]; exact htrt
  · rw [hfs, hsp]; unfold Apart; omega

end FvModexp.Amd64

namespace FvModexp.Amd64.Q.NatDiv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem l_preM {R : RtInv} {b : Nat} {dc : Nat → Nat → Nat} {L : List (Nat × Nat)}
    {u ul uc v vl vc : Nat} {s : State} (hp : PFM R b dc L u ul uc v vl vc s)
    {L1 : List (Nat × Nat)} {b1 st : Nat} (X : State)
    (hN : NewStk R L L1 b b1 (s.regs 14).toNat X.mem st)
    (hF : MemFrame s.mem X.mem (R.rt ++ win s 41512 112)) (hLF : LiveFrame s.mem X.mem L [])
    (hreg : X.mem.regions = s.mem.regions)
    (hge : natVal s.mem v vl ≤ natVal s.mem u ul) (hv2 : 2 ≤ vl)
    (hsp : X.regs 4 = s.regs 4 - 240#64) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (i0 : X.mem.readLE ((s.regs 4).toNat - 232) 8 = u) (i1 : X.mem.readLE ((s.regs 4).toNat - 224) 8 = ul)
    (i3 : X.mem.readLE ((s.regs 4).toNat - 208) 8 = v) (i4 : X.mem.readLE ((s.regs 4).toNat - 200) 8 = vl) :
    DivLarge.Pre R b1 (16 * ul + 64) L1 (DivLarge.costQ dc ul vl) 0 0 st u uc u ul v vl X := by
  have hce0 := hp.ce
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -, hout, hga, hgr, hLs, hro, ⟨-, -, -⟩, htrt, -⟩ := hp.ce
  simp only [regSP] at hb' ha hw
  unfold Apart at hga
  have hspn := sp240 hsp (by omega)
  have hce1 : CallEnv R L X 41272 112 :=
    CallEnv.calleeRt hce0 hspn h14 hfs (by decide) (by decide) (by decide) hF hreg
  have hwin : ∀ a n, Outside a n (win s 41512 112) → Outside a n (win X 41272 112) := fun a n h =>
    winX hspn hb' h
  have hacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := hF.accessible
  have hrdH : ∀ a n, (InRanges a n L ∨ Outside a n R.rt) → Outside a n (win s 41512 112) →
      X.mem.readLE a n = s.mem.readLE a n := by
    intro a n hh ho
    rcases hh with hin | hr
    · exact hLF.readLE a n hin trivial
    · exact hF.readLE a n (by rw [outside_append]; exact ⟨hr, ho⟩)
  have hvl : vl ≤ ul := vl_le hp.un hp.vn (by omega) hge
  have hui := hp.ui.2 (by omega)
  obtain ⟨hu40, huacc, hu48, huh, huw⟩ := hui
  obtain ⟨hv40, hvacc, hv48, hvh, hvw⟩ := hp.vo
  obtain ⟨hL1, hrs, hst0, hst8, hst48, hstacc, hlen, hcap, hc0, hw8, hw48, hwacc, hdis, hbb, hbb', hinv1⟩ := hN
  have hN : NewStk R L L1 b b1 (s.regs 14).toNat X.mem st :=
    ⟨hL1, hrs, hst0, hst8, hst48, hstacc, hlen, hcap, hc0, hw8, hw48, hwacc, hdis, hbb, hbb', hinv1⟩
  obtain ⟨hhin, -⟩ := hN.hdr
  have hhO := out_inR2 hout hhin
  have hhG := out_inR2 hgr hhin
  have hhT := out_inR2 htrt hhin
  obtain ⟨-, -, -, -, -, -, -, -, hgArt, hgAw, -, hwbrt, -⟩ := hp.gl
  have hhgA := out_inR2 hgArt hhin
  have hhwb := out_inR2 hwbrt hhin
  have harrF : 0 < stCap X.mem st → InRanges (stW X.mem st) (8 * stCap X.mem st) R.rt := fun hc => (hN.arr hc).1
  have hUap := hN.apart (a := u) (k := 8 * ul) huh
  have hVap := hN.apart (a := v) (k := 8 * vl) hvh
  have wr : ∀ p c, EvenHyp.WrOut R L s 41512 112 p c → EvenHyp.WrOut R L1 X 41272 112 p c := by
    intro p c ⟨h1, h2, h3⟩
    refine ⟨h1, fun hc => ?_, fun hc => ⟨hwin _ _ (h3 hc).1, by rw [h14, hfs]; exact (h3 hc).2⟩⟩
    obtain ⟨a1, a2, a3, a4⟩ := h2 hc; exact ⟨a1, hN.held a2, by rw [hacc]; exact a3, a4⟩
  unfold DivLarge.Pre
  rw [hspn, hfs, h14]
  refine ⟨?ce, hp.srv, globals_win hp.gl hF ?gw hwin, ⟨by decide, fun h => absurd h (by decide),
      fun h => absurd h (by decide)⟩, wr _ _ hp.uo, ⟨hu40, by rw [hacc]; exact huacc, hu48, hN.held huh, hwin _ _ huw⟩,
    ⟨hv40, by rw [hacc]; exact hvacc, hv48, hN.held hvh, hwin _ _ hvw⟩, hv2, hvl, hp.ul9, ?vn,
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun hc => (hp.ug hc).1, Or.inl rfl, ?stk,
    by rw [hlen]; have := hp.ul9; omega, fun h => absurd h (by decide), ?uS, hUap, hVap,
    ?wb, ?hfree, hc0, by omega, ⟨fun h => absurd h (by decide), fun hc => (hp.ug hc).2, ?sg, ?fg⟩, ?cost, ?inv,
    ?i0, ?i1, ?i3, ?i4, ?stt, ?stft⟩
  case ce =>
    have e : L1 = L ++ stkRs X.mem st := hL1
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hce1
    refine ⟨c1, c2, c3, c4, c5, c6, c7, ?_, c9, c10⟩
    exact hN.liveSep c8 (fun q hq => by
      simp only [win, List.mem_singleton] at hq; subst hq; simp only
      rw [hspn, show (s.regs 4).toNat - 240 + 112 - ((s.regs 4).toNat - 240 - 41272) = 41272 + 112 by omega]
      exact hout.of_sub (by omega) (by omega))
  case gw =>
    simp only [win, outside_append, outside_cons, outside_nil, and_true] at hgAw ⊢
    exact ⟨hgArt, by omega⟩
  case vn =>
    rcases hp.vn with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      simp only [win, outside_cons, outside_nil, and_true] at hvw
      rw [hrdH _ _ (hvh.sub (by omega) (by omega)) (by simp only [win, outside_cons, outside_nil, and_true]; omega)]
      exact h
  case stk =>
    refine ⟨⟨hst8, Or.inl ⟨(st, st + 24), by rw [hL1]; exact List.mem_append_right _ (List.mem_cons_self ..),
      by simp only; omega, by simp only; omega⟩, hstacc, hst48, fun hc => ⟨hw8, Or.inl ?_, hwacc hc, hw48⟩,
      by omega, hcap⟩, ?_, by (try rw [h14]); unfold Apart; omega, fun hc => ⟨?_, ?_⟩⟩
    · refine ⟨(stW X.mem st, stW X.mem st + 8 * stCap X.mem st), ?_, by simp only; omega, by simp only; omega⟩
      rw [hL1]; refine List.mem_append_right _ ?_
      simp only [stkRs]; rw [if_neg (show ¬(stCap X.mem st = 0) by omega)]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · simp only [win, outside_cons, outside_nil, and_true, hspn]; omega
    · have := out_inR2 hout (harrF hc); simp only [win, outside_cons, outside_nil, and_true, hspn]; omega
    · have := out_inR2 hgr (harrF hc); (try rw [h14]); unfold Apart; omega
  case uS => intro hc; exact hN.apart (hp.uo.2.1 hc).2.1
  case wb => show Apart st 24 RunIface.wbA 4; unfold Apart; omega
  case hfree =>
    rw [hlen]; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]; exact hdis
  case sg => unfold Apart; omega
  case fg =>
    rw [hlen]; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
    rcases Nat.eq_zero_or_pos (stCap X.mem st) with hc | hc
    · rw [hc]; unfold Apart; omega
    · have := out_inR2 hgArt (harrF hc); unfold Apart; omega
  case cost =>
    have h1 := hp.cost
    refine ⟨by rw [hlen]; omega, ?_⟩
    simp only [costMQ, HM, NatDiv.costQ, DivLarge.costQ, stkR, stkRes] at h1 ⊢
    omega
  case inv => exact hinv1
  case i0 => rw [show (s.regs 4).toNat - 240 + 8 = (s.regs 4).toNat - 232 by omega]; exact i0
  case i1 => rw [show (s.regs 4).toNat - 240 + 16 = (s.regs 4).toNat - 224 by omega]; exact i1
  case i3 => rw [show (s.regs 4).toNat - 240 + 32 = (s.regs 4).toNat - 208 by omega]; exact i3
  case i4 => rw [show (s.regs 4).toNat - 240 + 40 = (s.regs 4).toNat - 200 by omega]; exact i4
  case stt => unfold Apart; omega
  case stft =>
    rw [hlen]; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
    rcases Nat.eq_zero_or_pos (stCap X.mem st) with hc | hc
    · rw [hc]; unfold Apart; omega
    · have := out_inR2 htrt (harrF hc); unfold Apart; omega

end FvModexp.Amd64.Q.NatDiv
