import FvModexp.Proofs.Arm64.Nat.Callees
import FvModexp.Proofs.Arm64.LshVUSum
import FvModexp.Proofs.Arm64.RshVUSum

/-!
# More callees of the mul/div layer (arm64): `lshVU.abi0`, `rshVU.abi0` (asm), two-argument internal calls

`lshVUHyp` / `rshVUHyp`: agent asm's library summaries `LshVUSum.lshVU_summary` / `RshVUSum.rshVU_summary` (proved on the
one-segment library programs whose segment is the Run extraction's `seg44` / `seg47`) moved into the restricted programs
(`codeIn_single`), and their `.live` forms (runtime invariant and stack-guard word kept, `Summary0.live`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Callees

theorem Ensures.toSummaryRegs2 {p0 P : Program} {entry : Nat}
    {pre : W64 → W64 → State → Prop} {post : W64 → W64 → State → State → Prop}
    (h : ∀ a0 a1, Ensures p0 entry [a0, a1] (pre a0 a1) (post a0 a1))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.regs 30).toNat ∧ pre (s.regs 0) (s.regs 1) s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 18 = s.regs 18) ∧ post (s.regs 0) (s.regs 1) s s') := by
  intro s hpc ⟨hret, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 1)) hx hc s hpc ⟨hret, by simp [ArgsFrom], hpre⟩

theorem Ensures.toSummaryRegs9 {p0 P : Program} {entry : Nat}
    {pre : W64 → W64 → W64 → W64 → W64 → W64 → W64 → W64 → W64 → State → Prop}
    {post : W64 → W64 → W64 → W64 → W64 → W64 → W64 → W64 → W64 → State → State → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8, Ensures p0 entry [a0, a1, a2, a3, a4, a5, a6, a7, a8]
      (pre a0 a1 a2 a3 a4 a5 a6 a7 a8) (post a0 a1 a2 a3 a4 a5 a6 a7 a8))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.regs 30).toNat ∧
        pre (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6) (s.regs 7) (s.regs 8) s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 18 = s.regs 18) ∧
        post (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6) (s.regs 7) (s.regs 8) s s') := by
  intro s hpc ⟨hret, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6)
    (s.regs 7) (s.regs 8)) hx hc s hpc ⟨hret, by simp [ArgsFrom], hpre⟩

/-! ## `lshVU.abi0` -/

def lshVUfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.lshVU.abi0"

def LshVUHyp (impl : List Segment) : Prop :=
  Summary0 ((Extracted.program.onlySegments [lshVUfn]).link impl) (segAddr Extracted.program lshVUfn)
    LshVUSum.Pre LshVUSum.Q

theorem lshVUHyp (impl : List Segment) (hap : ImplApart Extracted.program impl) : LshVUHyp impl := by
  have hseg : FvModexp.Lib.LshVUA64.segments = [Extracted.program.segments[44]'(by decide)] := rfl
  have hc := codeIn_single (lp := FvModexp.Lib.LshVUA64.program) (ns := [lshVUfn]) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 44) (by decide)) (by decide)
  have he : segAddr Extracted.program lshVUfn = FvModexp.Lib.LshVUA64.entry := by decide
  unfold LshVUHyp; rw [he]
  exact Janus.Contracts.EqHashModel.Summary.of_codeIn hc LshVUSum.lshVU_summary

/-- `lshVU.abi0` with the runtime invariant and the stack guard kept. -/
abbrev LshLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  LshVUSum.Pre s ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
    Outside (s.sp.toNat + 64) 8 R.rt ∧
    Apart (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ((s.regs 28).toNat + 16) 8 ∧
    Apart (s.sp.toNat + 64) 8 ((s.regs 28).toNat + 16) 8

abbrev LshLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  LshVUSum.Q s m ∧ R.inv b L (s.regs 28).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8

theorem LshVUHyp.live {P : Program} (h : Summary0 P (segAddr Extracted.program lshVUfn) LshVUSum.Pre LshVUSum.Q)
    (R : RtInv) (b : Nat) (L : List (Nat × Nat)) :
    Summary0 P (segAddr Extracted.program lshVUfn) (LshLPre R b L) (LshLQ R b L) := by
  refine Summary0.mono (Summary0.live h (fun s => [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8),
      (s.sp.toNat + 64, s.sp.toNat + 72)]) (fun s m _ hq => hq.2.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2⟩
  refine ⟨hp, hi, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega

/-! ## `rshVU.abi0` -/

def rshVUfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.rshVU.abi0"

def RshVUHyp (impl : List Segment) : Prop :=
  Summary0 ((Extracted.program.onlySegments [rshVUfn]).link impl) (segAddr Extracted.program rshVUfn)
    RshVUSum.Pre RshVUSum.Q

theorem rshVUHyp (impl : List Segment) (hap : ImplApart Extracted.program impl) : RshVUHyp impl := by
  have hseg : FvModexp.Lib.RshVUA64.segments = [Extracted.program.segments[47]'(by decide)] := rfl
  have hc := codeIn_single (lp := FvModexp.Lib.RshVUA64.program) (ns := [rshVUfn]) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 47) (by decide)) (by decide)
  have he : segAddr Extracted.program rshVUfn = FvModexp.Lib.RshVUA64.entry := by decide
  unfold RshVUHyp; rw [he]
  exact Janus.Contracts.EqHashModel.Summary.of_codeIn hc RshVUSum.rshVU_summary

abbrev RshLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  RshVUSum.Pre s ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
    Outside (s.sp.toNat + 64) 8 R.rt ∧
    Apart (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ((s.regs 28).toNat + 16) 8 ∧
    Apart (s.sp.toNat + 64) 8 ((s.regs 28).toNat + 16) 8

abbrev RshLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  RshVUSum.Q s m ∧ R.inv b L (s.regs 28).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8

theorem RshVUHyp.live {P : Program} (h : Summary0 P (segAddr Extracted.program rshVUfn) RshVUSum.Pre RshVUSum.Q)
    (R : RtInv) (b : Nat) (L : List (Nat × Nat)) :
    Summary0 P (segAddr Extracted.program rshVUfn) (RshLPre R b L) (RshLQ R b L) := by
  refine Summary0.mono (Summary0.live h (fun s => [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8),
      (s.sp.toNat + 64, s.sp.toNat + 72)]) (fun s m _ hq => hq.2.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2⟩
  refine ⟨hp, hi, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega

end FvModexp.Arm64.Callees
