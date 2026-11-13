import FvModexp.Proofs.Amd64.NatQ.DrsA2
import FvModexp.Proofs.Amd64.Nat.StackNatXDefs

set_option autoImplicit false

/-! (amd64 twin (asm s47) of Arm64/NatQ/DrsSN3.lean)
# `divRecursiveStep` (amd64), loop body: `qhatv := stk.nat(3n)` (natdiv.go:829) — the callee's precondition (pure)

`sn3_pre`: `StackNatX.PreQ … 4192 24 st (3n)` at a call state `X` of the body (`RSP = r - 400`) from the
environment `Ev`/`Fp` (stack length `l1`) and a budget `stkR ≤ bk`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

set_option maxHeartbeats 8000000 in
theorem sn3_pre {R : RtInv} {c : Cx} {s X : State} {Lk : List (Nat × Nat)} {bk : Nat}
    (hcr : Cr R c s) (hev : Ev R c s Lk bk X.mem) (hfp : Fp R c s Lk X.mem (c.l1 s))
    (hsp : (X.regs 4).toNat = (s.regs 4).toNat - 400) (h14 : X.regs 14 = s.regs 14) (hfs : X.fsBase = s.fsBase)
    (hbud : stkR c.Hq X.mem c.st ≤ bk) :
    StackNatX.PreQ R bk Lk c.Hq 4192 24 c.st (3 * c.vl) X := by
  have hW := hcr.hW; have hWg := drsW64_ge c.vl
  have hpre := hcr.pre
  have hvl9 := hpre.v9.1
  obtain ⟨-, hstw, -, harr⟩ := hpre.sti
  have hstl := hpre.stl.1
  have hcq := hpre.cost
  obtain ⟨-, ⟨hb', -, -⟩, -, -, hout, -, hgr, -⟩ := hpre.ce
  simp only [regSP] at hb'
  have hlen := hfp.len
  have hwin : ∀ a n, Outside a n (win s c.W 96) → Outside a n (win X 4192 24) := fun a n h => by
    simp only [win, outside_cons, outside_nil, and_true] at h ⊢; rw [hsp]; omega
  have hfst := hfp.fst
  rw [← hlen] at hfst
  refine ⟨Ev.callEnv hcr hev hsp h14 hfs (by omega) (by omega), hpre.sv, hev.sok, hwin _ _ hstw, ?arr, by omega,
    by rw [hlen]; simp only [Cx.l1, StackNat.rnd]; omega,
    ⟨by rw [hlen]; simp only [Cx.l1, StackNat.rnd]; omega, hbud⟩, by rw [h14]; exact hev.inv,
    by rw [hev.fr.accessible]; exact hpre.gl.2.2.2.2.2.2.2.2.2.2.1, hpre.wbap, hfst⟩
  case arr =>
    intro hc
    rcases hev.sarr with ⟨e1, e2⟩ | ⟨hin, -⟩
    · rw [e2] at hc; rw [e1, e2]; obtain ⟨a1, a2⟩ := harr hc; exact ⟨hwin _ _ a1, by rw [h14]; exact a2⟩
    · have h1 := outside_of_inRangesR hout hin
      have h2 := outside_of_inRangesR hgr hin
      refine ⟨?_, ?_⟩
      · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
      · rw [h14]; unfold Apart; omega

end FvModexp.Amd64.Q.DivRec
