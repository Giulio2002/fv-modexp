import FvModexp.Proofs.Arm64.Top.RunDRel
import FvModexp.Proofs.Arm64.Top.RunCMath

/-!
# `Run` (arm64): the compute part — definitions

From `D3` (`fn + 0x760`, the three operands read, `X0`/`X1` = `mod.abs` pointer/length) `Run` computes

* `mod.BitLen() == 0` (`fn + 0x760 .. 0x7a0`): return `LeftPadBytes([]byte{}, modLen)` (`0x7a4 .. 0x804`);
* else (`C2` = `fn + 0x808`) `base.BitLen() == 1`: `v = base.Mod(base, mod).Bytes()`, otherwise
  `v = base.Exp(base, exp, mod).Bytes()` (`(*Int).exp(base, base, exp, mod, false)`);
* `V` = `fn + 0x880`: `LeftPadBytes(v, modLen)` and return.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

/-- `D3`: the three operands are read. -/
abbrev pcC1 : Nat := segAddr Extracted.program fn + 0x760
/-- `C2`: `mod ≠ 0`, `base.BitLen()` next. -/
abbrev pcC2 : Nat := segAddr Extracted.program fn + 0x808
/-- `V`: `v` returned by `Bytes()`, `LeftPadBytes(v, modLen)` next. -/
abbrev pcCV : Nat := segAddr Extracted.program fn + 0x880

/-- The result EthLib's `compute` encodes: `0` for a zero modulus, else `base ^ exp mod modulus`. -/
def resV (s : State) (p len : BitVec 64) : Nat :=
  if opV s p len 2 = 0 then 0 else opV s p len 0 ^ opV s p len 1 % opV s p len 2

/-- `Run` returned `(out, nil)`: the nil `error` (type word `X3 = 0`), `len(out) = n`, `out` holds `V` big-endian. -/
def OkRet (s' : State) (V n : Nat) : Prop :=
  s'.regs 3 = 0#64 ∧ (s'.regs 1).toNat = n ∧ beVal s'.mem (s'.regs 0).toNat n = V

/-- The frame of a successful return with window `W` below `SP`: as `RunFrame`, and the `n` output bytes at `q` are
the program's (a live object of the new live set, or outside the runtime-owned ranges). -/
def OkFrame (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (W : Nat) (s s' : State) (q n : Nat) : Prop :=
  ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - B ≤ b' ∧
    R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ (0 < n → Held R L' q n) ∧
    MemFrame s.mem s'.mem (R.rt ++ win s W 40) ∧ LiveFrame s.mem s'.mem L []

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

/-- All-zero bytes have big-endian value `0`. -/
theorem beVal_zeros {m : Memory} {q n : Nat} (h : ∀ i, i < n → (m.bytes (q + i)).toNat = 0) : beVal m q n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [beVal_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64

/-- A frame of the segment window `winA s 4800 40` is a frame of the bigger window `win s W 40`. -/
theorem memFrame_win {m m' : Memory} {rt : List (Nat × Nat)} {s : State} {W : Nat} (hW : 4800 ≤ W)
    (h : MemFrame m m' (rt ++ winA s 4800 40)) : MemFrame m m' (rt ++ win s W 40) :=
  h.mono fun a n hh => by
    simp only [winA, win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at hh ⊢
    exact ⟨hh.1, by omega, by omega⟩

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

/-- The block of a `make([]byte, n)` with `n ≤ 1024` fits the budget left after the operands. -/
theorem bs_le {n b b1 B : Nat} (hn : n ≤ 1024) (hB : 3 * makeCost 4 + 3 * dCost + allocCost 1024 ≤ B) (hbB : B ≤ b)
    (hbud : b - (3 * makeCost 4 + 3 * dCost) ≤ b1) :
    blockSize n true ≤ b1 ∧ b - B ≤ b1 - blockSize n true := by
  have := blockSize_le_allocCost n true
  simp only [allocCost] at this hB ⊢; omega

end FvModexp.Arm64.Run
