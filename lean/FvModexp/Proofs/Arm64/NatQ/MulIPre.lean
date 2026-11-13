import FvModexp.Proofs.Arm64.NatQ.MulLift

set_option autoImplicit false

/-!
# [Q-form copy of Arm64/Nat/MulIPre.lean — TIGHT COSTS, divmc s34] `(*Int).mul` (arm64): the `nat.mul` call's precondition from `IPre` (int.go:197-205)

`z.abs = z.abs.mul(stk, x.abs, y.abs)` is called at `0x1b0cfc` one frame down (`SP - 96`); the callee's window
`W - 96` (`imW = mulW + 96`) sits inside ours, the operands are the three header triples.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA)

set_option maxRecDepth 20000 in
/-- `MPre` at the inner call (`S1.sp = s.sp - 96`, window `W - 96`) from `IPre` -/
theorem ipre_down {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W z st x y : Nat} {s S1 : State}
    (hpre : IPre R b H L W z st x y s)
    (hsp : S1.sp.toNat = s.sp.toNat - 96) (hg : S1.regs 28 = s.regs 28) (hF : MemFrame s.mem S1.mem (winA s W 40))
    (hreg : S1.mem.regions = s.mem.regions) :
    MPre R b H L (W - 96) (hP s.mem z) (hC s.mem z) st (hP s.mem x) (hL s.mem x) (hC s.mem x) (hP s.mem y)
      (hL s.mem y) (hC s.mem y) S1 := by
  obtain ⟨hce, hiw, hsv, hglb, hty, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hops, hstk, hcost, hinv⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce'
  have hW : 96 + 4608 ≤ W := by have := mulW_ge (hL s.mem x) (hL s.mem y); unfold imW at hiw; omega
  have hF1 : MemFrame s.mem S1.mem (R.rt ++ winA s W 40) := hF.mono fun a n h => by
    simp only [outside_append] at h; exact h.2
  have hLF : LiveFrame s.mem S1.mem L [] := lf_win' [] hF hLs
  have hsub := win_sub (ab := 40) hsp (show 96 + (W - 96) ≤ W by omega) (by omega) (by omega) (stk1 := W - 96)
    (above1 := 88)
  obtain ⟨eW, eL, eC⟩ := hdr_keep hstk.2.1 hstk.2.2.1 hF1 hLF
  refine ⟨callEnv_shift hce hLs hF1 hsp hg hreg (show 96 + (W - 96) ≤ W by omega) (by omega) (by omega) (by decide),
    by unfold imW at hiw; omega, hsv, globals_shift hglb hF1 (fun a n h => winA_of_win' h) hsub, hty, ?_,
    stkPre_shift hstk hF1 hLF hg hsub, ⟨by rw [eL]; exact hcost.1, by rw [stkR_congr eC]; exact hcost.2⟩, ?_⟩
  · rw [hg]; exact (hops.mono hsub).move eW eL eC hF.accessible
  · rw [hg]; exact inv_frame_winA hF hout (by omega) (by decide) hinv

end FvModexp.Arm64.Q.NatMul
