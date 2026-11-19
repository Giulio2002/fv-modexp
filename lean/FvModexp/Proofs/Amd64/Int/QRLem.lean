import FvModexp.Proofs.Amd64.Int.QRDefs
import FvModexp.Proofs.Common.Link

set_option autoImplicit false

/-!
# `(*Int).QuoRem` / `(*Int).Mod` (amd64): moving a precondition one frame down (generic frame lemmas, pure)

`callEnv_shift` copied from divmc's `Q.NatMul.callEnv_shift` (Amd64/NatQ/MulOps.lean), `globals_win` from top's
`globals_win` (Amd64/NatQ/DivBigP.lean), so that the Mod chain does not import the multiplication / division chains.
`natLive_frame`, `natNorm_frame`, `natVal_frame'`: an array outside a frame keeps its facts and value (twins of the arm64
`IMod` lemmas, Arm64/Int/ModLem.lean).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IMod

theorem callEnv_shift {R : RtInv} {L L1 : List (Nat × Nat)} {s S1 : State} {W ab f stk1 above1 : Nat}
    (hce : CallEnv R L s W ab) (hLs1 : LiveSep L1 (win s W ab)) (hF1 : MemFrame s.mem S1.mem (R.rt ++ win s W ab))
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - f) (hg : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hreg : S1.mem.regions = s.mem.regions)
    (hk : f + stk1 ≤ W) (ha : above1 ≤ f + ab) (hf8 : f % 8 = 0) :
    CallEnv R L1 S1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb, ha', hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb ha' hw
  unfold Apart at hga htw
  have hgr' : S1.mem.readLE ((S1.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hg]; exact hF1.readLE _ _ (by
      simp only [win, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega⟩)
  have htls : S1.mem.readLE (S1.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
    rw [hfs]; exact hF1.readLE _ _ (by
      simp only [win, outside_append, outside_cons, outside_nil, and_true]; exact ⟨htrt, by omega⟩)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [stackguard0Offset, regG]; rw [hg]; exact hg1
  · simp only [stackguard0Offset, regG]; rw [hg, hF1.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [hg] at hgr' ⊢; rw [hgr', hsp]; omega
  · first | omega | (simp only [stackguard0Offset, regG, regSP]; omega) | (simp_all only [stackguard0Offset, regG, regSP, Apart]; omega)
  · simp only [regSP]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; rw [hF1.accessible, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · omega
  · exact dataLoaded_frame64 hdl hreg hro hF1 (by
      intro r hr _; simp only [win, List.mem_singleton] at hr; subst hr
      simp only; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · rw [hg]; exact hgr
  · intro r hr; have := hLs1 r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega
  · rw [hfs]; exact htb
  · rw [hfs, hF1.accessible]; exact htr
  · rw [htls, htg, hg]
  · rw [hfs]; exact htrt
  · rw [hfs, hsp]; unfold Apart; omega

/-- the threshold globals and the write-barrier flag survive a window-only frame -/
theorem globals_win {R : RtInv} {m m' : Janus.Arm64.Memory} {w w' ws : List (Nat × Nat)} (h : RunIface.Globals R m w)
    (hF : MemFrame m m' ws) (hg : Outside RunIface.gA 32 ws) (hw : ∀ a n, Outside a n w → Outside a n w') :
    RunIface.Globals R m' w' := by
  obtain ⟨h40, h12, h80, h40', e8, e16, e24, hgacc, hgrt, hgw, hwbacc, hwbrt, hwbw⟩ := h
  have hrd : ∀ k, k + 8 ≤ 32 → m'.readLE (RunIface.gA + k) 8 = m.readLE (RunIface.gA + k) 8 := fun k hk =>
    hF.readLE _ _ (hg.of_sub (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, e8, e16, e24, by rw [hF.accessible]; exact hgacc, hgrt, hw _ _ hgw,
    by rw [hF.accessible]; exact hwbacc, hwbrt, hw _ _ hwbw⟩
  · rw [e8, hrd 8 (by omega), ← e8]; exact h40
  · rw [e16, hrd 16 (by omega), ← e16]; exact h12
  · rw [e24, hrd 24 (by omega), ← e24]; exact h80
  · have := hrd 0 (by omega); simp only [Nat.add_zero] at this
    show m'.readLE RunIface.gA 8 = 40; rw [this]; exact h40'

theorem natLive_frame {R : RtInv} {L : List (Nat × Nat)} {m m' : Janus.Arm64.Memory} {p c : Nat}
    (h : NatLive m R L p c) (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) : NatLive m' R L p c := by
  intro hc; obtain ⟨a1, a2, a3, a4⟩ := h hc; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩

theorem natVal_frame' {m m' : Janus.Arm64.Memory} {rs : List (Nat × Nat)} {p l : Nat} (hF : MemFrame m m' rs)
    (ho : 0 < l → Outside p (8 * l) rs) : natVal m' p l = natVal m p l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · subst h0; rfl
  · exact hF.readLE _ _ (ho h0)

theorem natNorm_frame {m m' : Janus.Arm64.Memory} {rs : List (Nat × Nat)} {p l : Nat} (hF : MemFrame m m' rs)
    (ho : 0 < l → Outside p (8 * l) rs) (h : NatNorm m p l) : NatNorm m' p l := by
  rcases h with h | h
  · exact Or.inl h
  · rcases Nat.eq_zero_or_pos l with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [hF.readLE _ _ ((ho h0).of_sub (by omega) (by omega))]; exact h

end FvModexp.Amd64.IMod
