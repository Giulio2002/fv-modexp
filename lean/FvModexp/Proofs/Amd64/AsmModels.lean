import FvModexp.Proofs.Common.AsmModel
import FvModexp.Proofs.Amd64.AddVVSum
import FvModexp.Proofs.Amd64.SubVVSum

/-!
# The amd64 assembly/leaf summaries stated against the mathdiv models (`FvModexp.Mdl`, docs/MODELS.md)

Each `*_summary_model` is the value-level summary (`*Sum.*_summary`) with its postcondition restated through
`FvModexp.Asm.limbs` (memory slice → model `List Nat`): the written limbs are exactly the model's output list.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI0 Janus.Amd64.Tactic FvModexp.Asm

namespace FvModexp.Amd64.AsmModels

/-- `addVV.abi0`: `z[0:n] = (Mdl.addVV x[0:n] y[0:n]).1`, result word `= .2` -/
def AddVVQ (s : State) (m : Memory) : Prop :=
  let z := s.mem.readLE ((s.regs 4).toNat + 8) 8; let n := s.mem.readLE ((s.regs 4).toNat + 16) 8
  let x := s.mem.readLE ((s.regs 4).toNat + 32) 8; let y := s.mem.readLE ((s.regs 4).toNat + 56) 8
  limbs m z n = (Mdl.addVV (limbs s.mem x n) (limbs s.mem y n)).1 ∧
  m.readLE ((s.regs 4).toNat + 80) 8 = (Mdl.addVV (limbs s.mem x n) (limbs s.mem y n)).2 ∧
  MemFrame s.mem m [(z, z + 8 * n), ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)]

theorem addVV_summary_model :
    Summary0 FvModexp.Lib.AddVVAmd64.program FvModexp.Lib.AddVVAmd64.entry AddVVSum.Pre AddVVQ :=
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
  let z := s.mem.readLE ((s.regs 4).toNat + 8) 8; let n := s.mem.readLE ((s.regs 4).toNat + 16) 8
  let x := s.mem.readLE ((s.regs 4).toNat + 32) 8; let y := s.mem.readLE ((s.regs 4).toNat + 56) 8
  limbs m z n = (Mdl.subVV (limbs s.mem x n) (limbs s.mem y n)).1 ∧
  m.readLE ((s.regs 4).toNat + 80) 8 = (Mdl.subVV (limbs s.mem x n) (limbs s.mem y n)).2 ∧
  MemFrame s.mem m [(z, z + 8 * n), ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)]

theorem subVV_summary_model :
    Summary0 FvModexp.Lib.SubVVAmd64.program FvModexp.Lib.SubVVAmd64.entry SubVVSum.Pre SubVVQ :=
  Summary0.mono SubVVSum.subVV_summary (fun _ h => h) fun s m _ hq => by
    unfold SubVVSum.Q at hq
    obtain ⟨h1, h2, h3⟩ := hq
    have hb : m.readLE ((s.regs 4).toNat + 80) 8 ≤ 1 := by rw [h2]; split <;> omega
    obtain ⟨e1, e2⟩ := subVV_model s.mem m _ _ _ _ _ hb h1
    exact ⟨e1, e2, h3⟩

end FvModexp.Amd64.AsmModels
