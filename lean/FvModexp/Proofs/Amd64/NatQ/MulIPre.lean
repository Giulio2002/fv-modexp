import FvModexp.Proofs.Amd64.NatQ.MulLift

set_option autoImplicit false

/-!
# [amd64 port (divmc s53) of the Q-form Arm64/NatQ/MulIPre.lean — TIGHT COSTS] `(*Int).mul` (amd64): the `nat.mul` call's precondition from `IPre` (int.go:201)

`z.abs = z.abs.mul(stk, x.abs, y.abs)` is called at `0x5e2aa1` one frame down (`PUSHQ BP; SUBQ $0x50`, the callee's
entry `RSP - 96`); the callee's window `W - 96` (`imW64 = mulW64 + 96`) sits inside ours, the operands are the three
header triples.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.IntAS (hNeg hP hL hC intZ wbA)
open FvModexp.Amd64.Q.NatSqr (inv_frame_win globals_frame)

set_option maxRecDepth 20000 in
/-- `MPre` at the inner call (`RSP₁ = RSP - 96`, window `W - 96`) from `IPre` -/
theorem ipre_down {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W z st x y : Nat} {s S1 : State}
    (hpre : IPre R b H L W z st x y s)
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 96) (hg : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hF : MemFrame s.mem S1.mem (win s W 40)) (hreg : S1.mem.regions = s.mem.regions) :
    MPre R b H L (W - 96) (hP s.mem z) (hC s.mem z) st (hP s.mem x) (hL s.mem x) (hC s.mem x) (hP s.mem y)
      (hL s.mem y) (hC s.mem y) S1 := by
  obtain ⟨hce, hiw, hsv, hglb, hty, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hops, hstk, hcost, hadx, hinv⟩ :=
    hpre
  have hce' := hce
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -⟩ := hce'
  simp only [regSP] at hb' ha hw
  have hW : 96 + 4608 ≤ W := by have := mulW64_ge (hL s.mem x) (hL s.mem y); unfold imW64 at hiw; omega
  have hF1 : MemFrame s.mem S1.mem (R.rt ++ win s W 40) := hF.mono fun a n h => by
    simp only [outside_append] at h; exact h.2
  have hLF : LiveFrame s.mem S1.mem L [] := lf_win' [] hF hLs
  have hsub := win_sub (ab := 40) hsp (show 96 + (W - 96) ≤ W by omega) (by omega) (by omega) (stk1 := W - 96)
    (above1 := 88)
  obtain ⟨eW, eL, eC⟩ := hdr_keep hstk.2.1 hstk.2.2.1 hF1 hLF
  have htd : NatSqr.tls S1 = NatSqr.tls s := by simp only [NatSqr.tls]; rw [hfs]
  refine ⟨callEnv_shift hce hLs hF1 hsp hg hfs hreg (show 96 + (W - 96) ≤ W by omega) (by omega) (by decide),
    by unfold imW64 at hiw; omega, hsv,
    globals_frame hglb hF1 (by obtain ⟨-, -, -, -, -, -, -, -, -, hgw, -⟩ := hglb; exact hgw) hsub, hty, ?_,
    stkPre_shift hstk hF1 hLF hg hfs hsub,
    ⟨by rw [eL]; exact hcost.1, by rw [stkR_congr eC]; exact hcost.2⟩, by rw [hF.accessible]; exact hadx, ?_⟩
  · rw [hg, htd]; exact (hops.mono hsub).move eW eL eC hF.accessible
  · rw [hg]; exact inv_frame_win hF hout (by omega) (by decide) hinv

end FvModexp.Amd64.Q.NatMul
