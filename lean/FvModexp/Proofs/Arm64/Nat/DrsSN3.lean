import FvModexp.Proofs.Arm64.Nat.DrsA2
import FvModexp.Proofs.Arm64.Nat.DrsEnv

/-!
# `divRecursiveStep` (arm64), loop body: `qhatv := stk.nat(3n)` (natdiv.go:829) — the callee's precondition (pure)

`sn3_pre`: `StackNat.Pre … 4208 24 st (3n)` at a call state `X` of the body (`SP = entry SP - 400`) from the
environment `Ev`/`Fp` (stack length `l1`) and a budget `stackNatCost l1 (3n) ≤ bk`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

set_option maxHeartbeats 8000000 in
theorem sn3_pre {R : RtInv} {c : Cx} {s X : State} {Lk : List (Nat × Nat)} {bk : Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk X.mem) (hfp : Fp R c s Lk X.mem (c.l1 s))
    (hsp : X.sp.toNat = s.sp.toNat - 400) (h28 : X.regs 28 = s.regs 28)
    (hbud : stackNatCost (c.l1 s) (3 * c.vl) ≤ bk) :
    StackNat.Pre R bk Lk 4208 24 c.st (3 * c.vl) X := by
  have hW := hcr.hW; have hWg := drsW_ge c.vl
  obtain ⟨hce, hsv, hgl, -, -, -, -, -, -, -, ⟨hvl9, -⟩, -, -, -, -, -, -, -, -, -,
    ⟨-, hstw, hstg, harr⟩, ⟨hstl, -⟩, -, -, -, hswb, -, -, -, -, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, -⟩, -, hout, -, hgr, -, -⟩ := hce
  have hlen := hfp.len
  have hwin : ∀ a n, Outside a n (win s c.W 96) → Outside a n (win X 4208 24) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hfst := hfp.fst
  rw [← hlen] at hfst
  refine ⟨Ev.callEnv hcr hev hsp h28 (by omega) (by omega), hsv, hev.sok, hwin _ _ hstw, ?arr, by omega,
    by rw [hlen]; simp only [Cx.l1, StackNat.rnd]; omega, by rw [hlen]; exact hbud, by rw [h28]; exact hev.inv,
    by rw [hev.fr.accessible]; exact hgl.2.2.2.2.2.2.2.2.2.2.1, hswb, hfst⟩
  case arr =>
    intro hc
    rcases hev.sarr with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e2] at hc; rw [e1, e2]; obtain ⟨a1, a2⟩ := harr hc; exact ⟨hwin _ _ a1, by rw [h28]; exact a2⟩
    · have h1 := FvModexp.Arm64.NatAdd.outside_of_inRanges hout hin
      have h2 := FvModexp.Arm64.NatAdd.outside_of_inRanges hgr hin
      refine ⟨?_, ?_⟩
      · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
      · rw [h28]; unfold Apart; omega

end FvModexp.Arm64.DivRec
