import FvModexp.Proofs.Amd64.Top.RunIface
import FvModexp.Proofs.Common.BytesOutMath

/-!
# `(*Int).Bytes` (amd64): statement pieces and the loop-head invariant

`int.go:527`: `buf := make([]byte, len(x.abs)*_S); return buf[x.abs.bytes(buf):]` with `nat.bytes` (`nat.go:1628`)
inlined. Frame: `PUSHQ BP; SUBQ $0x20, SP` (40 bytes below the entry `RSP`), spill of `RAX` at `0x30(SP)` = entry
`RSP + 8` (the window includes the return address at `[RSP]`: `above = 16`), `8·len` at `0x18(SP)` = entry `RSP - 16`,
one runtime call (`makeslice(uint8, n, n)`, 4096 bytes and its return address): `stk = 4160` (as on arm64).

Loop heads (offsets in the function): outer `+0x4f` (`CMPQ BX, DX`), inner `+0x67` (`CMPQ R9, $8`), zero-skip loop
`+0x95` (`CMPQ DI, CX`). Registers: `RAX` = `buf`, `RCX` = `len(buf) = N`, `RDX` = `len(abs)`, `RBX` = word index `k`,
`RSI` = `abs`, `RDI` = byte index `i`, `R8` = word `d`, `R9` = `j`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.RunIface

namespace FvModexp.Amd64.IntBytes

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.(*Int).Bytes"
def uint8T : Nat := Extracted.dataAddr.«type:uint8#6a8c7679»

abbrev hOuter : Nat := segAddr Extracted.program fn + 0x4f
abbrev hInner : Nat := segAddr Extracted.program fn + 0x67
abbrev hSkip : Nat := segAddr Extracted.program fn + 0x95

/-- The precondition (`RunIface.BytesSpec` at `stk = 4160`, `above = 16`). -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) (s : State) : Prop :=
  IntPre R b (BytesBudget (lenW s.mem x.toNat)) L 4160 16 [x.toNat] s ∧ IntLenLe s.mem x.toNat maxW

/-- The postcondition (`RunIface.BytesSpec` at `stk = 4160`, `above = 16`). -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ ∃ p n c : Nat, (s'.regs 0).toNat = p ∧ (s'.regs 3).toNat = n ∧ (s'.regs 1).toNat = c ∧ n ≤ c ∧
    beVal s'.mem p n = IntV s.mem x.toNat ∧ (n = 0 ∨ (s'.mem.bytes p).toNat ≠ 0) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - (BytesBudget (lenW s.mem x.toNat)) ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ (0 < n → InRanges p n L' ∧ InRanges p n R.rt ∧
        ApartAll p n L ∧ s'.mem.accessible p n true = true ∧ p + n ≤ 2 ^ 48) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4160 16) ∧ LiveFrame s.mem s'.mem L []

/-- The loop-head facts about the memory `m` (as on arm64): the return address and saved `BP` slots, `abs` unchanged,
the buffer `[q, q + N)` a fresh runtime object, the first `t` bytes of `abs` stored reversed at its end, the runtime
invariant, the frames. -/
def Inv (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (x : BitVec 64) (s : State) (ret q ap N t : Nat)
    (L' : List (Nat × Nat)) (b' : Nat) (m : Janus.Arm64.Memory) : Prop :=
  m.readLE (s.regs 4).toNat 8 = ret ∧ m.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
    (∀ a k, ap ≤ a → a + k ≤ ap + N → m.readLE a k = s.mem.readLE a k) ∧
    0 < N ∧ q + N ≤ 2 ^ 48 ∧ m.accessible q N true = true ∧ Apart q N ap N ∧
    Apart q N ((s.regs 4).toNat - 4160) (4160 + 16) ∧
    InRanges q N L' ∧ InRanges q N R.rt ∧ ApartAll q N L ∧
    (∀ i, i < t → (m.bytes (q + (N - 1 - i))).toNat = (s.mem.bytes (ap + i)).toNat) ∧
    LiveExt R L L' ∧ b - BytesBudget (N / 8) ≤ b' ∧ R.inv b' L' (s.regs 14).toNat (view R.rt L' m) ∧
    MemFrame s.mem m (R.rt ++ win s 4160 16) ∧ LiveFrame s.mem m L []

/-- Storing byte `t` of `abs` (`v % 256 = abs byte t`) at buffer index `N - 1 - t` extends the invariant. -/
theorem Inv.store {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {x : BitVec 64} {s : State} {ret q ap N t : Nat}
    {L' : List (Nat × Nat)} {b' : Nat} {m : Janus.Arm64.Memory} (h : Inv R b L x s ret q ap N t L' b' m) (ht : t < N)
    (v : Nat) (hv : v % 256 = (s.mem.bytes (ap + t)).toNat) :
    Inv R b L x s ret q ap N (t + 1) L' b' (m.writeLE (q + (N - 1 - t)) 1 v) := by
  obtain ⟨hm1, hm2, habs, hN, hq48, hqacc, hqa, hqw, hqL, hqR, hqA, hw, hext, hb', hinv, hfr, hlf⟩ := h
  unfold Apart at hqa hqw
  refine ⟨?_, ?_, ?_, hN, hq48, ?_, by unfold Apart; omega, by unfold Apart; omega, hqL, hqR, hqA, ?_, hext, hb', ?_, ?_, ?_⟩
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hm1
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hm2
  · intro a k ha hk
    by_cases hk0 : k = 0
    · subst hk0; rfl
    · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact habs a k ha hk
  · simpa only [Janus.Arm64.Memory.accessible_writeLE] using hqacc
  · intro i hi
    by_cases hit : i = t
    · subst hit
      rw [← Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_writeLE_self, ← hv]
    · rw [← Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_one]
      exact hw i (by omega)
  · exact inv_store_held (a := q + (N - 1 - t)) (n := 1) hinv
      (Or.inl (InRanges.sub (a := q + (N - 1 - t)) (n := 1) hqL (by omega) (by omega)))
  · exact MemFrame.writeLE_inRanges (a := q + (N - 1 - t)) (k := 1) hfr v
      (InRanges.append_left (InRanges.sub (a := q + (N - 1 - t)) (n := 1) hqR (by omega) (by omega)) _)
  · exact LiveFrame.writeLE (a := q + (N - 1 - t)) (k := 1) hlf v (ApartAll.outside (fun r hr => by
      have := hqA r hr; unfold Apart at this ⊢; omega))

/-- The `Extracted` program restricted to its data segment 0 (holds the `uint8` descriptor at `7231264`): `janus64_data`
on it installs ONE segment instead of 49 (asm s84: three full calls in `ens`'s context cost ≈ 25 s). -/
def u8ProgB : Janus.Amd64.Program := { Extracted.program with data := Extracted.program.data.take 1 }

theorem u8ProgB_loaded {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) : u8ProgB.DataLoaded m :=
  fun d h => hd d (List.mem_of_mem_take h)

set_option maxRecDepth 20000 in
/-- The `uint8` type descriptor (size 1, ptrdata 0, readable) read by `makeslice`. -/
theorem u8B {m : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded m) :
    m.readLE 7231264 8 = 1 ∧ m.readLE 7231272 8 = 0 ∧ m.accessible 7231264 16 false = true := by
  have hd1 := u8ProgB_loaded hd
  janus64_data hd1
  exact ⟨by rw [h_rodata _ _ (by decide)]; decide, by rw [h_rodata _ _ (by decide)]; decide,
    Janus.Arm64.Memory.accessible_mono _ h_data0 (by omega) (by omega)⟩

end FvModexp.Amd64.IntBytes
