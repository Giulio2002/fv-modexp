import FvModexp.Proofs.Arm64.Nat.DrsBd

/-!
# `divRecursiveStep` (arm64), big path: the call environment of a callee inside the body (pure)

`Ev.callEnv`: at a call state `X` (`SP = entry SP - 400`, memory `X.mem` of the environment), the callee's `CallEnv`
for a stack of `k` bytes and `a` bytes above (`k + 400 ≤ W`, `a + 8 ≤ 400`), with the current live set.
(Adapted from `callEnv_shift`: the frame from the entry also covers the caller-visible writes `c.ws s`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

set_option maxHeartbeats 8000000 in
theorem Ev.callEnv {R : RtInv} {c : Cx} {s X : State} {Lk : List (Nat × Nat)} {bk k a : Nat}
    (hcr : Cr R c s) (h : Ev R c s Lk bk X.mem) (hsp : X.sp.toNat = s.sp.toNat - 400) (hg : X.regs 28 = s.regs 28)
    (hk : k + 400 ≤ c.W) (ha : a + 8 ≤ 400) : CallEnv R Lk X k a := by
  have hpre := hcr.pre
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hqa, -, -, -, -⟩, ⟨hua, -, -, -, -⟩, -, -, -, -,
    ⟨hsok, -, -, -⟩, ⟨-, hc0⟩, -⟩ := hpre
  have hLs1 := lsep hce (hcr.ext1.trans h.ext)
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha', hw⟩, hdl, hout, hga, hgr, -, hro⟩ := hce
  unfold Apart at hga
  have hgr' : X.mem.readLE ((X.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hg]; exact h.grd hcr
  obtain ⟨-, -, hsacc, -, hnl, hlc, -⟩ := hsok
  obtain ⟨-, -, harr, -⟩ := hnl hc0
  have hal16 : X.sp.toNat % 16 = 0 := by rw [hsp]; omega
  refine ⟨⟨by rw [hg]; exact hg1, by rw [hg, h.fr.accessible]; exact hg2, by rw [hgr', hsp]; omega⟩,
    ⟨hal16, by omega, by omega, ?_⟩, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro⟩
  · rw [h.fr.accessible, hsp]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · refine dataLoaded_frame (rt := R.rt) (ws := winA s c.W 96 ++ c.ws s) hdl h.reg hro
      (by simpa only [List.append_assoc] using h.fr) ?_
    intro r hr hlt
    simp only [Cx.ws, stkWs, winA, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
    · exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
    · simpa using hqa
    · simpa using hua
    · simpa using hsacc
    · simp only at hlt ⊢
      exact Memory.accessible_mono _ harr (by omega) (by omega)
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr; have := hLs1 r hr
    simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega

end FvModexp.Arm64.DivRec
