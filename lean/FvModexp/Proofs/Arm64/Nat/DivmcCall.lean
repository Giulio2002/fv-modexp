import FvModexp.Proofs.Arm64.Conv
import FvModexp.Proofs.Common.Link

/-!
# The callee's `CallEnv` from the caller's (arm64)

A function with `CallEnv R L s stk above` calls a callee at `SP' = SP - d` (its own frame `d` below `SP`): the callee has
`CallEnv R L s1 stk1 above1` when its window fits inside the caller's (`d + stk1 ≤ stk`, `above1 ≤ d + above`) and the
memory changed only inside the caller's window (regions unchanged).
-/

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64

theorem CallEnv.callee {R : RtInv} {L : List (Nat × Nat)} {s s1 : State} {stk above d stk1 above1 : Nat}
    (h : CallEnv R L s stk above) (hsp : s1.sp.toNat = s.sp.toNat - d) (hg : s1.regs 28 = s.regs 28)
    (hd16 : d % 16 = 0) (hk : d + stk1 ≤ stk) (ha : above1 ≤ d + above)
    (hF : MemFrame s.mem s1.mem (win s stk above)) (hreg : s1.mem.regions = s.mem.regions) :
    CallEnv R L s1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha', hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := h
  unfold Apart at hga
  have hgr' : s1.mem.readLE ((s1.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hg]; exact hF.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  refine ⟨⟨by rw [hg]; exact hg1, by rw [hg, hF.accessible]; exact hg2, by rw [hgr', hsp]; omega⟩,
    ⟨by omega, by omega, by omega, ?_⟩, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro⟩
  · rw [hF.accessible, hsp]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · exact dataLoaded_win hdl hreg hro (hF.mono fun a n ho => by
      simp only [outside_append] at ho; exact ho.2) hw (by intro r hr; simp at hr; subst hr; simp only; omega)
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr; have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega

end FvModexp.Arm64
