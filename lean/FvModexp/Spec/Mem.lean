import Janus
import EthLib.Base.Bytes

/-! SPECIFICATION part (reviewed by a human, docs/HUMAN-REVIEW.md §1): how the bytes of a Go `[]byte` in the Janus memory model are read as the
EthLib `ByteArray` that the MODEXP specification takes. -/

namespace FvModexp.Spec

open Janus.Arm64

/-- The byte at address `a` of the memory, as a `UInt8`. -/
def byteOf (m : Memory) (a : Nat) : UInt8 := UInt8.ofNat (m.bytes a).toNat

/-- The `n` bytes at address `p` (a Go slice `(ptr = p, len = n)`), as a `ByteArray`: `data[i] = m.bytes (p + i)` for `i < n`.
This is the call data `data` of the EthLib specification (the machine code reads exactly these bytes; `cap` is irrelevant). -/
def bytesAt (m : Memory) (p n : Nat) : ByteArray :=
  ⟨((List.range n).map fun i => byteOf m (p + i)).toArray⟩

theorem bytesAt_size (m : Memory) (p n : Nat) : (bytesAt m p n).size = n := by
  simp [bytesAt, ByteArray.size]

/-- Bridge to EthLib's total read `byteAt`: in range it is the memory byte, past the end it is `0`. -/
theorem byteAt_bytesAt (m : Memory) (p n i : Nat) :
    EthLib.Base.byteAt (bytesAt m p n) i = if i < n then byteOf m (p + i) else 0 := by
  unfold EthLib.Base.byteAt
  by_cases h : i < n
  · have h' : i < (bytesAt m p n).size := by rw [bytesAt_size]; exact h
    rw [dif_pos h', if_pos h]
    show ((List.map (fun i => byteOf m (p + i)) (List.range n)).toArray)[i]'(by simpa [bytesAt_size] using h') = _
    simp
  · have h' : ¬ i < (bytesAt m p n).size := by rw [bytesAt_size]; exact h
    rw [dif_neg h', if_neg h]

end FvModexp.Spec
