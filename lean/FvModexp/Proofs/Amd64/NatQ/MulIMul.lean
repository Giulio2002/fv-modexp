import FvModexp.Proofs.Amd64.NatQ.MulICall

set_option autoImplicit false

/-!
# [amd64 port (divmc s54) of the Q-form Arm64/NatQ/MulIMul.lean — TIGHT COSTS] `(*Int).mul` (amd64): the member step of the multiplication SCC (int.go:191-203, `x ≠ y`)

`imul_step`: entry `0x5e29e0` — stack check (refuted by `StackGuardOK`), `PUSHQ BP; MOVQ SP, BP; SUBQ $0x50, SP`,
`z` spilled at `0x60(SP)`, `CMPQ DI, CX; JNE` (taken: `x ≠ y`), `x`, `y` spilled at `0x70(SP)` / `0x78(SP)`, the three
headers loaded, `y.abs` stored at `0(SP) .. 0x10(SP)`, `CALL nat.mul` → `icall` at the callee entry `0x5f0840`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.IntAS (hNeg hP hL hC intZ wbA)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem imul_step (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (n : Nat) (ih : ∀ j, IH impl R H n j) (a : Args) :
    Summary (LibMul.program.link impl) (entryOf (.imul, a)) (fun s => preOf R H (.imul, a) s ∧ μ (.imul, a) s = n)
      (postOf R H (.imul, a)) := by
  have c4 : CodeIn64 (Extracted.program.ofImpl impl) (LibMul.program.link impl) := by
    rw [LibMul.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibMul.names
  have hwb' := WbLiveContract64.of_codeIn c4 hwb
  intro s hpc ⟨⟨⟨hra, hx15, hdf, h0, h3, h1, h7⟩, hpre⟩, hμ⟩
  show ReachesRet _ (retAddrOf s) s fun s' => Kept s s' ∧ IPost R a.b H a.L a.W a.a0.toNat a.a1.toNat a.a2.toNat
    a.a3.toNat s s'
  have hpc' : s.rip = BitVec.ofNat 64 0x5e29e0 := hpc
  have hμ' : μl (hL s.mem a.a2.toNat) (hL s.mem a.a3.toNat) + 4 = n := hμ
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, -⟩, hiw, -, -, -, hxy,
    ⟨-, hxa, hx48, hxo, -⟩, ⟨-, hya, hy48, hyo, -⟩, hza, hz48, hzo, -⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hW4 : 4704 ≤ a.W := Nat.le_trans (Nat.add_le_add_right (mulW64_ge _ _) 96) hiw
  simp only [win, outside_cons, outside_nil, and_true] at hzo hxo hyo
  have hne : a.a3 ≠ a.a2 := fun e => hxy (by rw [e])
  clear hpc
  janus64_run [hne] until [0x5f0840]
  refine icall impl R hwb' n ih (stk := a.a1) hpre (by rw [← hμ']; exact μ_imul _ _) hra hx15 hdf _ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?qF ?qreg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case qF => simp only [win]; janus_frame
  case qreg => janus64_simp
  all_goals try janus64_simp
  all_goals first | rfl | omega

end FvModexp.Amd64.Q.NatMul
