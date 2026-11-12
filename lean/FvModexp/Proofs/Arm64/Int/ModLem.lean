import FvModexp.Proofs.Arm64.Int.ModDefs
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# `(*Int).Mod` (arm64): moving `ModSpec`'s precondition to `nat.div`'s entry (generic frame lemmas, pure)

`callEnv_shift` / `globals_shift` adapted from divmc's `NatMul.callEnv_shift` / `globals_shift` (Arm64/Nat/MulOps.lean),
copied so that the Mod chain does not import the multiplication chain. `natLive_frame`, `natNorm_frame`, `natVal_frame`:
an array outside a frame keeps its facts and value.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IMod

open FvModexp.Arm64.RunIface (Globals)

theorem callEnv_shift {R : RtInv} {L L1 : List (Nat × Nat)} {s S1 : State} {W ab f stk1 above1 : Nat}
    (hce : CallEnv R L s W ab) (hLs1 : LiveSep L1 (win s W ab)) (hF1 : MemFrame s.mem S1.mem (R.rt ++ winA s W ab))
    (hsp : S1.sp.toNat = s.sp.toNat - f) (hg : S1.regs 28 = s.regs 28) (hreg : S1.mem.regions = s.mem.regions)
    (hk : f + stk1 ≤ W) (ha : above1 + 8 ≤ f) (hab : 8 ≤ ab) (hf16 : f % 16 = 0) :
    CallEnv R L1 S1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha', hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce
  unfold Apart at hga
  have hgr' : S1.mem.readLE ((S1.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hg]; exact hF1.readLE _ _ (by
      simp only [winA, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, by omega⟩)
  refine ⟨⟨by rw [hg]; exact hg1, by rw [hg, hF1.accessible]; exact hg2, by rw [hgr', hsp]; omega⟩,
    ⟨by omega, by omega, by omega, ?_⟩, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro⟩
  · rw [hF1.accessible, hsp]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · exact dataLoaded_win hdl hreg hro hF1 hw (by
      intro r hr; simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr; have := hLs1 r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega

theorem globals_shift {R : RtInv} {m m' : Memory} {ws ws' rs : List (Nat × Nat)}
    (h : Globals R m ws) (hF : MemFrame m m' (R.rt ++ rs)) (hrs : ∀ a n, Outside a n ws → Outside a n rs)
    (hws : ∀ a n, Outside a n ws → Outside a n ws') : Globals R m' ws' := by
  obtain ⟨h40, h12, h80, h40d, e1, e2, e3, hacc, hrt, hw, hwacc, hwrt, hww⟩ := h
  have hg : Outside RunIface.gA 32 (R.rt ++ rs) := by rw [outside_append]; exact ⟨hrt, hrs _ _ hw⟩
  have eg : RunIface.gA = 7147136 := rfl
  have e4 : Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.divRecursiveThreshold» =
      RunIface.gA := by rw [eg]; rfl
  refine ⟨?_, ?_, ?_, ?_, e1, e2, e3, by rw [hF.accessible]; exact hacc, hrt, hws _ _ hw,
    by rw [hF.accessible]; exact hwacc, hwrt, hws _ _ hww⟩
  · rw [e1, hF.readLE _ _ (hg.of_sub (by omega) (by omega)), ← e1]; exact h40
  · rw [e2, hF.readLE _ _ (hg.of_sub (by omega) (by omega)), ← e2]; exact h12
  · rw [e3, hF.readLE _ _ (hg.of_sub (by omega) (by omega)), ← e3]; exact h80
  · rw [e4, hF.readLE _ _ (hg.of_sub (by omega) (by omega)), ← e4]; exact h40d

theorem natLive_frame {R : RtInv} {L : List (Nat × Nat)} {m m' : Memory} {p c : Nat}
    (h : NatLive m R L p c) (hacc : ∀ a n w, m'.accessible a n w = m.accessible a n w) : NatLive m' R L p c := by
  intro hc; obtain ⟨a1, a2, a3, a4⟩ := h hc; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩

theorem natVal_frame {m m' : Memory} {rs : List (Nat × Nat)} {p l : Nat} (hF : MemFrame m m' rs)
    (ho : 0 < l → Outside p (8 * l) rs) : natVal m' p l = natVal m p l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · subst h0; rfl
  · exact hF.readLE _ _ (ho h0)

theorem natNorm_frame {m m' : Memory} {rs : List (Nat × Nat)} {p l : Nat} (hF : MemFrame m m' rs)
    (ho : 0 < l → Outside p (8 * l) rs) (h : NatNorm m p l) : NatNorm m' p l := by
  rcases h with h | h
  · exact Or.inl h
  · rcases Nat.eq_zero_or_pos l with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [hF.readLE _ _ ((ho h0).of_sub (by omega) (by omega))]; exact h

end FvModexp.Arm64.IMod
