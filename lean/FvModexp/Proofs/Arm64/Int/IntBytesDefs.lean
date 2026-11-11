import FvModexp.Proofs.Arm64.Top.RunIface
import FvModexp.Proofs.Common.BytesOutMath

/-!
# `(*Int).Bytes` (arm64): statement pieces and the loop-head invariant

`int.go:527`: `buf := make([]byte, len(x.abs)*_S); return buf[x.abs.bytes(buf):]` with `nat.bytes` (`nat.go:1628`)
inlined. Frame 64 bytes (`MOVD.W R30, -64(RSP)`), spill of `X0` at `72(RSP)` = caller `SP + 8` (`above = 16`), one runtime
call (`makeslice(uint8, n, n)`, 4096 bytes): `stk = 64 + 4096 = 4160`.

Loop heads (offsets in the function): outer `for _, d := range z` `+0x5c` (`CMP R4, R2`), inner `for j < 8` `+0x78`
(`CMP $8, R8`), the zero-skip loop `+0xb4` (`CMP R5<<3, R6`). After the outer loop `+0xa4` (`TBZ $63, R6`).
Every byte index `i = N-1 … 0` is written exactly once (`N = 8·len`), so `i ≥ 0` and `i < N` always hold (the panics are
unreachable).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.RunIface

namespace FvModexp.Arm64.IntBytes

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Bytes"
def uint8T : Nat := Extracted.dataAddr.«type:uint8#6a8c7679»

abbrev hOuter : Nat := segAddr Extracted.program fn + 0x5c
abbrev hInner : Nat := segAddr Extracted.program fn + 0x78
abbrev hAfter : Nat := segAddr Extracted.program fn + 0xa4
abbrev hSkip : Nat := segAddr Extracted.program fn + 0xb4

/-- The precondition (`RunIface.BytesSpec` at `stk = 4160`, `above = 16`). -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) (s : State) : Prop :=
  IntPre R b (BytesBudget (lenW s.mem x.toNat)) L 4160 16 [x.toNat] s ∧ IntLenLe s.mem x.toNat maxW

/-- The postcondition (`RunIface.BytesSpec` at `stk = 4160`, `above = 16`). -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) (s s' : State) : Prop :=
  ∃ p n c : Nat, (s'.regs 0).toNat = p ∧ (s'.regs 1).toNat = n ∧ (s'.regs 2).toNat = c ∧ n ≤ c ∧
    beVal s'.mem p n = IntV s.mem x.toNat ∧ (n = 0 ∨ (s'.mem.bytes p).toNat ≠ 0) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - (BytesBudget (lenW s.mem x.toNat)) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ (0 < n → InRanges p n L' ∧ InRanges p n R.rt ∧
        ApartAll p n L ∧ s'.mem.accessible p n true = true ∧ p + n ≤ 2 ^ 48) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4160 16) ∧ LiveFrame s.mem s'.mem L []

/-- The loop-head facts about the memory `m`, for the buffer `[q, q + N)` (`N = 8·al > 0`) and the `abs` array
`[ap, ap + N)`: frame record, `abs` unchanged, the buffer a fresh runtime object, the first `t` bytes of `abs` stored
reversed at the end of the buffer, the runtime invariant, the frames. -/
def Inv (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) (s : State) (ret q ap N t : Nat)
    (L' : List (Nat × Nat)) (b' : Nat) (m : Memory) : Prop :=
  m.readLE (s.sp.toNat - 64) 8 = ret ∧ m.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat ∧
    (∀ a k, ap ≤ a → a + k ≤ ap + N → m.readLE a k = s.mem.readLE a k) ∧
    0 < N ∧ q + N ≤ 2 ^ 48 ∧ m.accessible q N true = true ∧ Apart q N ap N ∧
    Apart q N (s.sp.toNat - 4160) (4160 + 16) ∧
    InRanges q N L' ∧ InRanges q N R.rt ∧ ApartAll q N L ∧
    (∀ i, i < t → (m.bytes (q + (N - 1 - i))).toNat = (s.mem.bytes (ap + i)).toNat) ∧
    LiveExt R L L' ∧ b - BytesBudget (N / 8) ≤ b' ∧ R.inv b' L' (s.regs 28).toNat (view R.rt L' m) ∧
    MemFrame s.mem m (R.rt ++ winA s 4160 16) ∧ LiveFrame s.mem m L []

/-- Storing byte `t` of `abs` (`v % 256 = abs byte t`) at buffer index `N - 1 - t` extends the invariant. -/
theorem Inv.store {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {x : BitVec 64} {s : State} {ret q ap N t : Nat}
    {L' : List (Nat × Nat)} {b' : Nat} {m : Memory} (h : Inv R b L x s ret q ap N t L' b' m) (ht : t < N) (v : Nat)
    (hv : v % 256 = (s.mem.bytes (ap + t)).toNat) :
    Inv R b L x s ret q ap N (t + 1) L' b' (m.writeLE (q + (N - 1 - t)) 1 v) := by
  obtain ⟨hm1, hm2, habs, hN, hq48, hqacc, hqa, hqw, hqL, hqR, hqA, hw, hext, hb', hinv, hfr, hlf⟩ := h
  unfold Apart at hqa hqw
  refine ⟨?_, ?_, ?_, hN, hq48, ?_, by unfold Apart; omega, by unfold Apart; omega, hqL, hqR, hqA, ?_, hext, hb', ?_, ?_, ?_⟩
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hm1
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hm2
  · intro a k ha hk
    by_cases hk0 : k = 0
    · subst hk0; rfl
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact habs a k ha hk
  · simpa only [Memory.accessible_writeLE] using hqacc
  · intro i hi
    by_cases hit : i = t
    · subst hit
      rw [← Memory.readLE_one, Memory.readLE_writeLE_self, ← hv]
    · rw [← Memory.readLE_one, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_one]
      exact hw i (by omega)
  · exact inv_store_held (a := q + (N - 1 - t)) (n := 1) hinv (Or.inl (InRanges.sub (a := q + (N - 1 - t)) (n := 1) hqL (by omega) (by omega)))
  · exact MemFrame.writeLE_inRanges (a := q + (N - 1 - t)) (k := 1) hfr v
      (InRanges.append_left (InRanges.sub (a := q + (N - 1 - t)) (n := 1) hqR (by omega) (by omega)) _)
  · exact LiveFrame.writeLE (a := q + (N - 1 - t)) (k := 1) hlf v (ApartAll.outside (fun r hr => by
      have := hqA r hr; unfold Apart at this ⊢; omega))

end FvModexp.Arm64.IntBytes
