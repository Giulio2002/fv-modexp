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

theorem rd_out {C m : Memory} {lo hi a : Nat} (fr : MemFrame C m [(lo, hi)]) (h : a + 1 ≤ lo ∨ hi ≤ a) :
    m.readLE a 1 = C.readLE a 1 :=
  fr.readLE a 1 (by simp only [outside_cons, outside_nil, and_true]; exact h)

theorem copy_rd {C m : Memory} {b src n i : Nat} (h : ∀ j, j < n → m.bytes (b + j) = C.bytes (src + j)) (hi : i < n) :
    m.readLE (b + i) 1 = C.readLE (src + i) 1 := by
  rw [Memory.readLE_one, Memory.readLE_one, h i hi]

/-- `Uint64()` with `MaxUint64` when `!IsUint64()`, as the machine code computes it from the limbs. -/
theorem sat_bv (m : Memory) (z : Nat) :
    (if m.readLE (z + 24) 8 ||| (m.readLE (z + 16) 8 ||| m.readLE (z + 8) 8) = 0 then BitVec.ofNat 64 (m.readLE z 8)
      else 18446744073709551615#64).toNat = RgSpec.sat (val256 m z) := by
  have h0 := Util.readLE8_lt m z; have h1 := Util.readLE8_lt m (z + 8); have h2 := Util.readLE8_lt m (z + 16)
  have := Calldata.sat_limbs (m.readLE z 8) (m.readLE (z + 8) 8) (m.readLE (z + 16) 8) (m.readLE (z + 24) 8) h0 h1 h2
  rw [val256_limbs, RgSpec.sat, ← this]
  split
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0]
  · rfl

theorem rd_frame' {m0 m : Memory} {rs : List (Nat × Nat)} (hf : MemFrame m0 m rs) {a b : Nat} (ho : Outside a 1 rs)
    (h : a = b) : m.readLE a 1 = (m0.bytes b).toNat := by
  subst h; exact rd_frame hf ho

theorem rd_self {m : Memory} {a b : Nat} (h : a = b) : m.readLE a 1 = (m.bytes b).toNat := by
  subst h; exact Memory.readLE_one m a

theorem val256_frame {m0 m : Memory} {rs : List (Nat × Nat)} (hf : MemFrame m0 m rs) {a : Nat} (ho : Outside a 32 rs) :
    val256 m a = val256 m0 a := hf.readLE a 32 ho

set_option hygiene false in
/-- One byte of a `getData` + `SetBytes` source: the zero-padded call-data byte. Goal
`X.readLE (a + i) 1 = if off + i < len then (s.mem.bytes (ptr + (off + i))).toNat else 0`; `hf` relates `s.mem` to the frame base
(or is absent when the base is `s.mem`). -/
macro "rg_byte" : tactic => `(tactic| (
  unfold Calldata.pad
  split
  · first
      | (exfalso; omega)
      | (refine (copy_rd (by assumption) (by omega)).trans ?_
         simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
         first
           | exact rd_frame' hf (by simp only [outside_cons, outside_nil, and_true]; omega) (by omega)
           | exact rd_self (by omega))
      | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
         first
           | exact rd_frame' hf (by simp only [outside_cons, outside_nil, and_true]; omega) (by omega)
           | exact rd_self (by omega))
  · first
      | (exfalso; omega)
      | (refine (rd_out (by assumption) (by omega)).trans ?_
         rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) by omega) with hq | hq | hq | hq <;>
           simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_inside, Nat.zero_div,
             Nat.zero_mod])
      | (rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) by omega) with hq | hq | hq | hq <;>
           simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_inside, Nat.zero_div,
             Nat.zero_mod])))

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
