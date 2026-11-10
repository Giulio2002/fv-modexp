import FvModexp.Proofs.Common.AsmModel
import FvModexp.Proofs.Arm64.AddVVSum
import FvModexp.Proofs.Arm64.SubVVSum
import FvModexp.Proofs.Arm64.CmpSum

/-!
# The arm64 assembly/leaf summaries stated against the mathdiv models (`FvModexp.Mdl`, docs/MODELS.md)

Each `*_summary_model` is the value-level summary (`*Sum.*_summary`) with its postcondition restated through
`FvModexp.Asm.limbs` (memory slice → model `List Nat`): the written limbs are exactly the model's output list.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic FvModexp.Asm

namespace FvModexp.Arm64.AsmModels

/-- `addVV.abi0`: `z[0:n] = (Mdl.addVV x[0:n] y[0:n]).1`, result word `= .2` -/
def AddVVQ (s : State) (m : Memory) : Prop :=
  let z := s.mem.readLE (s.sp.toNat + 8) 8; let n := s.mem.readLE (s.sp.toNat + 16) 8
  let x := s.mem.readLE (s.sp.toNat + 32) 8; let y := s.mem.readLE (s.sp.toNat + 56) 8
  limbs m z n = (Mdl.addVV (limbs s.mem x n) (limbs s.mem y n)).1 ∧
  m.readLE (s.sp.toNat + 80) 8 = (Mdl.addVV (limbs s.mem x n) (limbs s.mem y n)).2 ∧
  MemFrame s.mem m [(z, z + 8 * n), (s.sp.toNat + 80, s.sp.toNat + 88)]

theorem addVV_summary_model :
    Summary0 FvModexp.Lib.AddVVA64.program FvModexp.Lib.AddVVA64.entry AddVVSum.Pre AddVVQ :=
  Summary0.mono AddVVSum.addVV_summary (fun _ h => h) fun s m _ hq => by
    unfold AddVVSum.Q at hq
    obtain ⟨h1, h2, h3⟩ := hq
    obtain ⟨e1, e2⟩ := addVV_model s.mem m _ _ _ _ _ h1 h2
    unfold AddVVQ
    refine ⟨?_, ?_, ?_⟩
    · exact e1
    · exact e2
    · exact h3

/-- `subVV.abi0`: `z[0:n] = (Mdl.subVV x[0:n] y[0:n]).1`, result word (borrow) `= .2` -/
def SubVVQ (s : State) (m : Memory) : Prop :=
  let z := s.mem.readLE (s.sp.toNat + 8) 8; let n := s.mem.readLE (s.sp.toNat + 16) 8
  let x := s.mem.readLE (s.sp.toNat + 32) 8; let y := s.mem.readLE (s.sp.toNat + 56) 8
  limbs m z n = (Mdl.subVV (limbs s.mem x n) (limbs s.mem y n)).1 ∧
  m.readLE (s.sp.toNat + 80) 8 = (Mdl.subVV (limbs s.mem x n) (limbs s.mem y n)).2 ∧
  MemFrame s.mem m [(z, z + 8 * n), (s.sp.toNat + 80, s.sp.toNat + 88)]

theorem subVV_summary_model :
    Summary0 FvModexp.Lib.SubVVA64.program FvModexp.Lib.SubVVA64.entry SubVVSum.Pre SubVVQ :=
  Summary0.mono SubVVSum.subVV_summary (fun _ h => h) fun s m _ hq => by
    unfold SubVVSum.Q at hq
    obtain ⟨h1, h2, h3⟩ := hq
    have hb : m.readLE (s.sp.toNat + 80) 8 ≤ 1 := by rw [h2]; split <;> omega
    obtain ⟨e1, e2⟩ := subVV_model s.mem m _ _ _ _ _ hb h1
    exact ⟨e1, e2, h3⟩

/-- `nat.cmp`: `X0 = Mdl.natCmp x y` as a 64-bit word (`BitVec.ofInt 64`) -/
theorem cmp_res_model (s : State) :
    CmpSum.cmpRes (s.regs 1).toNat (s.regs 4).toNat (lv s.mem (s.regs 0).toNat (s.regs 1).toNat)
        (lv s.mem (s.regs 3).toNat (s.regs 4).toNat) =
      BitVec.ofInt 64 (Mdl.natCmp (limbs s.mem (s.regs 0).toNat (s.regs 1).toNat)
        (limbs s.mem (s.regs 3).toNat (s.regs 4).toNat)) :=
  cmp_model _ _ _ _ _ _ rfl

end FvModexp.Arm64.AsmModels
