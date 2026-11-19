import FvModexp.Proofs.Amd64.Conv
import FvModexp.Proofs.Common.Link

/-!
# The callee's `CallEnv` from the caller's (amd64)

A function with `CallEnv R L s stk above` calls a callee whose entry `RSP` is `RSP - d` (its own frame and the pushed
return address `d` below `RSP`): the callee has `CallEnv R L s1 stk1 above1` when its window fits inside the caller's
(`d + stk1 ≤ stk`, `above1 ≤ d + above`) and the memory changed only inside the caller's window (regions unchanged).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace FvModexp.Amd64

theorem CallEnv.callee {R : RtInv} {L : List (Nat × Nat)} {s s1 : State} {stk above d stk1 above1 : Nat}
    (h : CallEnv R L s stk above) (hsp : (s1.regs 4).toNat = (s.regs 4).toNat - d) (hg : s1.regs 14 = s.regs 14)
    (hfs : s1.fsBase = s.fsBase) (hd8 : d % 8 = 0) (hk : d + stk1 ≤ stk) (ha : above1 ≤ d + above)
    (hF : MemFrame s.mem s1.mem (win s stk above)) (hreg : s1.mem.regions = s.mem.regions) :
    CallEnv R L s1 stk1 above1 := by
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb, ha', hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := h
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb ha' hw
  unfold Apart at hga htw
  have hgr' : s1.mem.readLE ((s1.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hg]; exact hF.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have htls : s1.mem.readLE (s1.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
    rw [hfs]; exact hF.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [stackguard0Offset, regG]; rw [hg]; exact hg1
  · simp only [stackguard0Offset, regG]; rw [hg, hF.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [hg] at hgr' ⊢; rw [hgr', hsp]; omega
  · first | omega | (simp only [stackguard0Offset, regG, regSP]; omega) | (simp_all only [stackguard0Offset, regG, regSP, Apart]; omega)
  · simp only [regSP]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; rw [hF.accessible, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · omega
  · exact dataLoaded_frame64 hdl hreg hro (hF.widen R.rt) (by
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
