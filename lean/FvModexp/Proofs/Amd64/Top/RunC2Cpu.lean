import FvModexp.Proofs.Amd64.Top.RunC2One
import FvModexp.Proofs.Amd64.Top.RunIfaceA
import FvModexp.Spec.RunAmd64X

set_option autoImplicit false

/-! # `Run` (amd64): `hasADX` readable and `natOne`'s word apart from `gA` at the `Mod` / `exp` calls (agent top s49)

From Run's entry facts `Spec.RunAmd64.CpuOne` + `NatOne`, through the memory frame of the code before the call and the
return-address push inside the window (`RunIface.ExpA`, whose first conjunct is `ModSpecA`'s extra fact). -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

theorem expA_ops {R : RtInv} {s : State} {T : Janus.Arm64.Memory} {W a v : Nat}
    (hsW : W ≤ (s.regs 4).toNat) (hW1 : 4800 ≤ W)
    (hone : FvModexp.Spec.RunAmd64.NatOne R s.mem (win s W 40)) (hca : FvModexp.Spec.RunAmd64.CpuOne s.mem)
    (hMF : MemFrame s.mem T (R.rt ++ win s 4800 40))
    (ha : (s.regs 4).toNat - W ≤ a ∧ a + 8 ≤ (s.regs 4).toNat + 40) :
    RunIface.ExpA (T.writeLE a 8 v) := by
  dsimp only [FvModexp.Spec.RunAmd64.NatOne] at hone
  rw [show Extracted.dataAddr.«github.com/ethereum/go-bigmodexpfix/src/math/big.natOne» = RunIface.natOneA from rfl] at hone
  obtain ⟨-, -, -, -, hrt, hwin, -, -, -, -⟩ := hone
  simp only [win, Janus.outside_cons, Janus.outside_nil, and_true] at hwin
  obtain ⟨hadx, hap⟩ := hca
  have hO : Outside RunIface.natOneA 8 (R.rt ++ win s 4800 40) := by
    simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    exact ⟨hrt.of_sub (by omega) (by omega), by omega⟩
  refine ⟨?_, ?_⟩
  · rw [Janus.Arm64.Memory.accessible_writeLE, hMF.accessible]; exact hadx
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hMF.readLE _ _ hO]; exact hap

theorem adx_ops {s : State} {T : Janus.Arm64.Memory} {rs : List (Nat × Nat)} {a v : Nat}
    (hca : FvModexp.Spec.RunAmd64.CpuOne s.mem) (hMF : MemFrame s.mem T rs) :
    (T.writeLE a 8 v).accessible Callees.adxAddr 1 false = true := by
  rw [Janus.Arm64.Memory.accessible_writeLE, hMF.accessible]; exact hca.1

end FvModexp.Amd64.Run
