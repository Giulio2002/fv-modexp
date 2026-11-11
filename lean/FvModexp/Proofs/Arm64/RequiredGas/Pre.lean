import Extracted
import FvModexp.Spec
import FvModexp.Proofs.Common.Calldata
import FvModexp.Proofs.Common.BitArith
import FvModexp.Proofs.Common.RgSpec
import FvModexp.Proofs.Arm64.RequiredGas.Mv
import FvModexp.Proofs.Arm64.RequiredGas.Sb
import FvModexp.Proofs.Arm64.RequiredGas.Og

/-! The precondition and postcondition of `(*bigModExp).RequiredGas` (arm64), and the frame invariant at the join points of the proof. -/

namespace FvModexp.Arm64.RG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts EthLib.Execution.Evm.Precompiles.Modexp

/-- The call: receiver `c` (Osaka flags), input slice `(ptr, len, cap)`, the stack window `[SP - 504, SP + 40)`, the stack guard
`464` bytes below `SP`, the input and the receiver readable and apart from the window. -/
def RgPre (c ptr len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 464 ∧ StackOK s 504 40 ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
    cap.toNat < 2 ^ 48 ∧ Ptr s.mem ptr len.toNat false ∧ Ptr s.mem c 3 false ∧ Spec.OsakaReceiver s.mem c.toNat ∧
    Disjoint ptr.toNat len.toNat (s.sp.toNat - 504) 544 ∧ Disjoint c.toNat 3 (s.sp.toNat - 504) 544 ∧
    Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 504) 544

/-- The result: for every fork from Fusaka on, when the lengths pass EIP-7823, the `uint64` result is EthLib's `requiredGas`. -/
def RgPost (ptr len : BitVec 64) (s s' : State) : Prop :=
  ∀ fork, Spec.PostFusaka fork → Spec.LengthsPass (Spec.bytesAt s.mem ptr.toNat len.toNat) →
    Spec.u64 (s'.regs 0) = requiredGas fork (Spec.bytesAt s.mem ptr.toNat len.toNat)
      (parseLengths (Spec.bytesAt s.mem ptr.toNat len.toNat))

theorem returns_mono {p : Program} {s : State} {Q Q' : State → Prop} (h : Returns p s Q) (hQ : ∀ s', Q s' → Q' s') :
    Returns p s Q' := by
  obtain ⟨f, s', h1, h2⟩ := h
  exact ⟨f, s', h1, hQ _ h2⟩

theorem reaches_of_returns {p : Program} {s : State} {Q Q' : State → Prop} (h : Returns p s Q) (hQ : ∀ s', Q s' → Q' s') :
    Reaches p s (IsReturn Q') := by
  obtain ⟨f, s', h1, h2⟩ := h
  exact ⟨f, _, h1, hQ _ h2⟩

theorem regs0_ret (o j : Nat → W64) (v a b : W64) :
    setReg (setReg (callRegs o j [v]) 29 a) 30 b 0 = v := by
  simp [setReg, callRegs]

theorem L4_of {m : Memory} {z v : Nat}
    (h : m.readLE z 8 + 18446744073709551616 * m.readLE (z + 8) 8 + 340282366920938463463374607431768211456 * m.readLE (z + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * m.readLE (z + 24) 8 = v) :
    L4 (m.readLE z 8) (m.readLE (z + 8) 8) (m.readLE (z + 16) 8) (m.readLE (z + 24) 8) = v := by
  rw [← h, L4]

theorem fromBE_eq_of {f g : Nat → Nat} {n n' : Nat} (hn : n = n') (h : ∀ i, i < n' → f i = g i) :
    Aux.fromBE f n = Aux.fromBE g n' := by
  subst hn; exact Calldata.fromBE_congr n h

/-- Read one byte of the input through a frame: the byte of `s.mem`. -/
theorem rd_frame {m0 m : Memory} {rs : List (Nat × Nat)} (hf : MemFrame m0 m rs) {a : Nat} (ho : Outside a 1 rs) :
    m.readLE a 1 = (m0.bytes a).toNat := by
  rw [hf.readLE a 1 ho, Memory.readLE_one]

/-- The final value of the run is EthLib's `requiredGas` (when the lengths pass). -/
theorem rgPost_of (ptr len B E M : BitVec 64) (s s' : State)
    (hB : B.toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 0))
    (hE : E.toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 32))
    (hM : M.toNat = RgSpec.sat (Calldata.word s.mem ptr.toNat len.toNat 64))
    (hres : s'.regs 0 = BitVec.ofNat 64 (Geth.osakaModexpGas B.toNat E.toNat M.toNat
      (RgSpec.expHead s.mem ptr.toNat len.toNat B.toNat E.toNat))) : RgPost ptr len s s' := by
  intro fork hf hl
  have hg := RgSpec.gas_eq fork hf s.mem ptr.toNat len.toNat hl
  rw [← hB, ← hE, ← hM] at hg
  have hlt := (Spec.lengthsPass_iff _).1 hl
  rw [RgSpec.parse] at hlt
  rw [RgSpec.parse] at hg ⊢
  unfold requiredGas at hg ⊢
  have hlt2 := Geth.osaka_gas_lt fork hf _ _ _
    (exponentHead (Spec.bytesAt s.mem ptr.toNat len.toNat) ⟨Calldata.word s.mem ptr.toNat len.toNat 0,
      Calldata.word s.mem ptr.toNat len.toNat 32, Calldata.word s.mem ptr.toNat len.toNat 64⟩) hlt.1 hlt.2.1 hlt.2.2 (RgSpec.exponentHead_lt _ _ _ _)
  rw [Spec.u64, hres, BitVec.toNat_ofNat, hg, Nat.mod_eq_of_lt hlt2]

end FvModexp.Arm64.RG
