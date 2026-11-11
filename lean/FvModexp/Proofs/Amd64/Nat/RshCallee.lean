import FvModexp.Proofs.Amd64.Nat.Callees
import FvModexp.Proofs.Amd64.RshVUSum

/-!
# `rshVU.abi0` (asm) as a callee (amd64): moved into the restricted programs, `.live` form

The twin of `Callees2`'s `lshVU.abi0` section (Run extraction segment 47).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Callees

/-! ## `rshVU.abi0` -/

def rshVUfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.rshVU.abi0"

def RshVUHyp (impl : List Amd64.Segment) : Prop :=
  Summary0 ((Extracted.program.onlySegments [rshVUfn]).link impl) (segAddr Extracted.program rshVUfn)
    RshVUSum.Pre RshVUSum.Q

theorem rshVUHyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) : RshVUHyp impl := by
  have hseg : FvModexp.Lib.RshVUAmd64.segments = [Extracted.program.segments[47]'(by decide)] := rfl
  have hc := codeIn_single (lp := FvModexp.Lib.RshVUAmd64.program) (ns := [rshVUfn]) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 47) (by decide)) (by decide)
  have he : segAddr Extracted.program rshVUfn = FvModexp.Lib.RshVUAmd64.entry := by decide
  unfold RshVUHyp; rw [he]
  exact Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc RshVUSum.rshVU_summary

/-- `rshVU.abi0` with the runtime invariant, the stack guard and the TLS slot kept. -/
abbrev RshLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  RshVUSum.Pre s ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
    Outside ((s.regs 4).toNat + 64) 8 R.rt ∧
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      ((s.regs 14).toNat + 16) 8 ∧
    Apart ((s.regs 4).toNat + 64) 8 ((s.regs 14).toNat + 16) 8 ∧
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.fsBase.toNat - 8) 8 ∧
    Apart ((s.regs 4).toNat + 64) 8 (s.fsBase.toNat - 8) 8

abbrev RshLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  RshVUSum.Q s m ∧ R.inv b L (s.regs 14).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 ∧
    m.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8

theorem RshVUHyp.live {P : Amd64.Program} (h : Summary0 P (segAddr Extracted.program rshVUfn) RshVUSum.Pre RshVUSum.Q)
    (R : RtInv) (b : Nat) (L : List (Nat × Nat)) :
    Summary0 P (segAddr Extracted.program rshVUfn) (RshLPre R b L) (RshLQ R b L) := by
  refine Summary0.mono (Summary0.live h (fun s => [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 64, (s.regs 4).toNat + 72)]) (fun s m _ hq => hq.2.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2, ha3, ha4⟩
  refine ⟨hp, hi, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega
  · simp only [Outside, and_true]; unfold Apart at ha3 ha4; omega

end FvModexp.Amd64.Callees
