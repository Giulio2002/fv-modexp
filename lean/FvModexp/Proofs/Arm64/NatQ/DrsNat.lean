import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.Nat.StackNatXDefs
import FvModexp.Proofs.Arm64.NatQ.DrsPathB

set_option autoImplicit false

/-! (Q-form copy of Arm64/Nat/DrsNat.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64): `qhat0 := stk.nat(B + 1)` (`fn + 0x104`) — the callee's precondition

`sn_pre`: `StackNat.Pre … 4208 24 st (B + 1)` at the call (one frame of 400 below the entry, memory = the entry's up
to the own frame `fw s`); the budget part from `drsC_big`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxHeartbeats 8000000 in
/-- **`StackNat.Pre` at `stk.nat(B + 1)`** -/
theorem sn_pre {R : RtInv} {b Hq : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s X : State} (hpre : DrsPreW R b L Hq c W qp ql qc st up ul uc vp vl vc s) (hW : 4864 ≤ W)
    (hF : MemFrame s.mem X.mem (fw s)) (hsp : X.sp = s.sp - 400#64) (h28 : X.regs 28 = s.regs 28)
    (hreg : X.mem.regions = s.mem.regions) :
    StackNatX.PreQ R b L Hq 4208 24 st (vl / 2 + 1) X := by
  obtain ⟨hce, hsv, hgl, -, -, -, -, -, -, hv2, ⟨hvl9, -⟩, -, -, -, -, -, -, -, -, -,
    hsti, ⟨hstl, -⟩, -, -, -, hswb, hsf, -, -, hcb, hinv⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce'
  have hspn : X.sp.toNat = s.sp.toNat - 400 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hXacc : ∀ a n w, X.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hF.accessible a n w
  have rdX : ∀ a n, Outside a n (win s W 96) → X.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hF.readLE a n (fw_out (by omega) h)
  obtain ⟨hok, hstw, hstg, harr⟩ := hsti
  have hsw : Outside st 24 (win s W 96) := hstw
  have eW : stW X.mem st = stW s.mem st := rdX _ _ (hsw.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen X.mem st = stLen s.mem st := rdX _ _ (hsw.of_sub (by omega) (by omega))
  have eC : stCap X.mem st = stCap s.mem st := rdX _ _ (hsw.of_sub (by omega) (by omega))
  have hF1 : MemFrame s.mem X.mem (R.rt ++ winA s W 96) := hF.mono fun a n ho => by
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho
    simp only [fw, winA, outside_cons, outside_nil, and_true]; omega
  have hwin : ∀ a n, Outside a n (win s W 96) → Outside a n (win X 4208 24) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hspn]; omega
  refine ⟨callEnv_shift hce hLs hF1 hspn h28 hreg (by omega) (by omega) (by omega) (by omega), hsv,
    stkOK_moveS hok eW eL eC hXacc, hwin _ _ hsw, ?arr, by omega, by rw [eL]; omega, ⟨by rw [eL]; omega, by rw [stkR_congr eC]; omega⟩,
    by rw [h28]; exact RtInv.inv_frame' hF (fun r hr => by
      simp only [fw, winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by simp only; omega) (by simp only; omega))) hinv,
    by rw [hXacc]; exact hgl.2.2.2.2.2.2.2.2.2.2.1, hswb, by rw [eW, eL, eC]; exact hsf⟩
  case arr => rw [eW, eC, h28]; intro hc; obtain ⟨h1, h2⟩ := harr hc; exact ⟨hwin _ _ h1, h2⟩

end FvModexp.Arm64.Q.DivRec
