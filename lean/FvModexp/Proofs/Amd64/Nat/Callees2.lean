import FvModexp.Proofs.Amd64.Nat.Callees
import FvModexp.Proofs.Amd64.LshVUSum

/-!
# More callees of the mul/div layer (amd64): `lshVU.abi0` (asm), two- and nine-argument internal calls

The amd64 twin of `Arm64/Nat/Callees2.lean`: agent asm's `LshVUSum.lshVU_summary` (library program whose segment is
the Run extraction's `seg44`) moved into the restricted programs (`codeIn_single`), and its `.live` form (runtime
invariant, stack-guard word and TLS slot kept, `Summary0.live`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Callees

theorem Ensures.toSummaryRegs2 {p0 P : Amd64.Program} {entry : Nat}
    {pre : W64 → W64 → State → Prop} {post : W64 → W64 → State → State → Prop}
    (h : ∀ a0 a1, Ensures p0 entry [a0, a1] (pre a0 a1) (post a0 a1))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn64 p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.mem.readLE (s.regs regSP).toNat 8) ∧ s.xmm xmmZero = 0 ∧ s.df = false ∧
        pre (s.regs 0) (s.regs 3) s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧
        s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧ post (s.regs 0) (s.regs 3) s s') := by
  intro s hpc ⟨hret, hz, hdf, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 3))
    hx (by simp [numIntRegs]) hc s hpc ⟨hret, hz, by simp [ArgsFrom64, argReg, intArgRegs], hdf, hpre⟩

theorem Ensures.toSummaryRegs9 {p0 P : Amd64.Program} {entry : Nat}
    {pre : W64 → W64 → W64 → W64 → W64 → W64 → W64 → W64 → W64 → State → Prop}
    {post : W64 → W64 → W64 → W64 → W64 → W64 → W64 → W64 → W64 → State → State → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8, Ensures p0 entry [a0, a1, a2, a3, a4, a5, a6, a7, a8]
      (pre a0 a1 a2 a3 a4 a5 a6 a7 a8) (post a0 a1 a2 a3 a4 a5 a6 a7 a8))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn64 p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.mem.readLE (s.regs regSP).toNat 8) ∧ s.xmm xmmZero = 0 ∧ s.df = false ∧
        pre (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11) s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧
        s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        post (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11)
          s s') := by
  intro s hpc ⟨hret, hz, hdf, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9)
    (s.regs 10) (s.regs 11)) hx (by simp [numIntRegs]) hc s hpc
    ⟨hret, hz, by simp [ArgsFrom64, argReg, intArgRegs], hdf, hpre⟩

/-! ## `lshVU.abi0` -/

def lshVUfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.lshVU.abi0"

def LshVUHyp (impl : List Amd64.Segment) : Prop :=
  Summary0 ((Extracted.program.onlySegments [lshVUfn]).link impl) (segAddr Extracted.program lshVUfn)
    LshVUSum.Pre LshVUSum.Q

theorem lshVUHyp (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) : LshVUHyp impl := by
  have hseg : FvModexp.Lib.LshVUAmd64.segments = [Extracted.program.segments[44]'(by decide)] := rfl
  have hc := codeIn_single (lp := FvModexp.Lib.LshVUAmd64.program) (ns := [lshVUfn]) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 44) (by decide)) (by decide)
  have he : segAddr Extracted.program lshVUfn = FvModexp.Lib.LshVUAmd64.entry := by decide
  unfold LshVUHyp; rw [he]
  exact Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc LshVUSum.lshVU_summary

/-- `lshVU.abi0` with the runtime invariant, the stack guard and the TLS slot kept. -/
abbrev LshLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  LshVUSum.Pre s ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
    Outside ((s.regs 4).toNat + 64) 8 R.rt ∧
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      ((s.regs 14).toNat + 16) 8 ∧
    Apart ((s.regs 4).toNat + 64) 8 ((s.regs 14).toNat + 16) 8 ∧
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.fsBase.toNat - 8) 8 ∧
    Apart ((s.regs 4).toNat + 64) 8 (s.fsBase.toNat - 8) 8

abbrev LshLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  LshVUSum.Q s m ∧ R.inv b L (s.regs 14).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 ∧
    m.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8

theorem LshVUHyp.live {P : Amd64.Program} (h : Summary0 P (segAddr Extracted.program lshVUfn) LshVUSum.Pre LshVUSum.Q)
    (R : RtInv) (b : Nat) (L : List (Nat × Nat)) :
    Summary0 P (segAddr Extracted.program lshVUfn) (LshLPre R b L) (LshLQ R b L) := by
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
