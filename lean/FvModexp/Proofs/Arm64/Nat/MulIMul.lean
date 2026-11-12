import FvModexp.Proofs.Arm64.Nat.MulICall

set_option autoImplicit false

/-!
# `(*Int).mul` (arm64): the SCC member (int.go:191-203)

`imul_step`: entry (`0x1b0c50`) → stack check (refuted by `GuardOK`), prologue (`SUB $96`), `x == y` test (`IPre`'s `x ≠ y`:
`BNE` taken; the `nat.sqr` branch is not reached), spills of `x`, `y`, the header loads → `icall`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem imul_step (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (n : Nat) (ih : ∀ j, IH impl R n j) (a : Args) :
    Summary (LibMul.program.link impl) (entryOf (.imul, a)) (fun s => preOf R (.imul, a) s ∧ μ (.imul, a) s = n)
      (postOf R (.imul, a)) := by
  have c4 : CodeIn (Extracted.program.ofImpl impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibMul.names
  have hwb' := WbLiveContract.of_codeIn c4 hwb
  intro s hpc ⟨⟨⟨hl4, hl48, h0, h1, h2, h3, _, _, _, _, _, _⟩, hpre⟩, hμ⟩
  show ReachesRet _ (s.regs 30) s fun s' => Kept s s' ∧ IPost R a.b a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat
    a.a3.toNat s s'
  have hpc' : s.pc = BitVec.ofNat 64 0x1b0c50 := hpc
  have hμ' : μl (hL s.mem a.a2.toNat) (hL s.mem a.a3.toNat) + 4 = n := hμ
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩, hiw, -, -, -, hxy,
    ⟨-, hxa, hx48, hxo, -⟩, ⟨-, hya, hy48, hyo, -⟩, hza, hz48, hzo, -⟩ := hpre'
  have hW4 : 4704 ≤ a.W := Nat.le_trans (Nat.add_le_add_right (mulW_ge _ _) 96) hiw
  simp only [win, outside_cons, outside_nil, and_true] at hzo hxo hyo
  have hne : (s.regs 2).toNat ≠ (s.regs 3).toNat := by rw [h2, h3]; exact hxy
  clear hpc
  janus_run [hne] until [0x1b0cfc]
  refine icall impl R hwb' n ih (stk := a.a1) hpre (by rw [← hμ']; exact μ_imul _ _) hl4 hl48 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?qF ?qreg ?_ ?_ ?_ ?_ ?_
  case qF => simp only [winA]; janus_frame
  case qreg => janus_simp
  all_goals janus_simp

end FvModexp.Arm64.NatMul
