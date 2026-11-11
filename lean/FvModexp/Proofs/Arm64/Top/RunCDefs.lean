import FvModexp.Proofs.Arm64.Top.RunDRel
import FvModexp.Proofs.Arm64.Top.RunCMath
import FvModexp.Proofs.Arm64.Top.RunIface

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

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- The word count bound of operand `j` from its byte length: `⌈len / 8⌉`. -/
@[reducible] def opW (s : State) (p len : BitVec 64) (j : Nat) : Nat := (hdrV s p len j + 7) / 8

/-- The largest operand word count bound. -/
@[reducible] def wMax (s : State) (p len : BitVec 64) : Nat := max (max (opW s p len 0) (opW s p len 1)) (opW s p len 2)

/-- The budget of the compute calls (`Mod` or `exp`, then `Bytes`), from the operand lengths. -/
def callB (s : State) (p len : BitVec 64) : Nat :=
  RunIface.ModBudget (wMax s p len) + RunIface.ExpBudget (wMax s p len) (opW s p len 1) +
    RunIface.BytesBudget RunIface.maxW

/-- The state at `V` (`fn + 0x880`): `v = (X0, X1, X2)` returned by `Bytes()` holds the result, minimal, at most `modLen`
bytes, a fresh live object; the frame slots `LeftPadBytes` and the epilogue read; the frames with window `W`. -/
def RelV (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (p len : BitVec 64) (s : State) (ret W : Nat)
    (Lk : List (Nat × Nat)) (bk : Nat) (V : State) : Prop :=
  V.sp = s.sp - 624#64 ∧ V.regs 28 = s.regs 28 ∧ V.regs 29 = s.sp - 632#64 ∧ V.regs 18 = s.regs 18 ∧
  V.mem.readLE (s.sp.toNat - 624) 8 = ret ∧ V.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat ∧
  V.mem.readLE (s.sp.toNat - 464) 8 = hdrV s p len 2 ∧ hdrV s p len 2 ≤ 1024 ∧
  Extracted.program.DataLoaded V.mem ∧
  (V.regs 1).toNat ≤ hdrV s p len 2 ∧ beVal V.mem (V.regs 0).toNat (V.regs 1).toNat = resV s p len ∧
  (0 < (V.regs 1).toNat → InRanges (V.regs 0).toNat (V.regs 1).toNat Lk ∧
    InRanges (V.regs 0).toNat (V.regs 1).toNat R.rt ∧
    V.mem.accessible (V.regs 0).toNat (V.regs 1).toNat true = true ∧ (V.regs 0).toNat + (V.regs 1).toNat ≤ 2 ^ 48) ∧
  LiveExt R L Lk ∧ b - (3 * makeCost 4 + 3 * dCost + callB s p len) ≤ bk ∧
  R.inv bk Lk (s.regs 28).toNat (view R.rt Lk V.mem) ∧ LiveSep Lk (win s W 40) ∧
  MemFrame s.mem V.mem (R.rt ++ win s W 40) ∧ LiveFrame s.mem V.mem L []

/-- The budget of the whole success path: the operands, the compute calls, the `LeftPadBytes` buffer. -/
def okB (s : State) (p len : BitVec 64) : Nat := 3 * makeCost 4 + 3 * dCost + callB s p len + allocCost 1024

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64

theorem outW_w {rt : List (Nat × Nat)} {s : State} {W a n : Nat} (h : Outside a n (rt ++ win s W 40)) :
    Outside a n (win s W 40) := (Janus.outside_append _ _ _ _ |>.mp h).2

/-- The runtime callee stack of a call from `Run`'s frame (`SP - 624`, 4096 below, 3 words above) is inside `Run`'s window. -/
theorem outW_cs {rt : List (Nat × Nat)} {s : State} {W a n : Nat} (hW : 4800 ≤ W)
    (h : Outside a n (rt ++ win s W 40)) :
    Outside a n (rt ++ [(s.sp.toNat - 624 - 4096, s.sp.toNat - 624 - 8),
      (s.sp.toNat - 624 + 8, s.sp.toNat - 624 + 8 + 24)]) := by
  simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
  exact ⟨h.1, by omega, by omega⟩

/-- The object `[d, d + k)` of the runtime is in the frame `R.rt` already. -/
theorem outW_csd {rt : List (Nat × Nat)} {s : State} {W a n d k : Nat} (hW : 4800 ≤ W) (hd : InRanges d k rt)
    (h : Outside a n (rt ++ win s W 40)) :
    Outside a n (rt ++ [(s.sp.toNat - 624 - 4096, s.sp.toNat - 624 - 8),
      (s.sp.toNat - 624 + 8, s.sp.toNat - 624 + 8 + 24)] ++ [(d, d + k)]) := by
  have h1 := outW_cs hW h
  simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h h1 ⊢
  have := InRanges.apart hd h.1
  unfold Apart at this
  exact ⟨h1, by omega⟩

/-- The budget of the `LeftPadBytes` buffer. -/
theorem bud_pad {b b1 n : Nat} {s : State} {p len : BitVec 64} (hn : n ≤ 1024) (hbB : okB s p len ≤ b)
    (hbud : b - (3 * makeCost 4 + 3 * dCost + callB s p len) ≤ b1) :
    blockSize n true ≤ b1 ∧ b - okB s p len ≤ b1 - blockSize n true := by
  have := blockSize_le_allocCost n true
  have h2 : allocCost n ≤ allocCost 1024 := by simp only [allocCost]; omega
  simp only [okB] at hbB ⊢; omega

/-- Without the pad buffer the budget is that of the operands and the calls. -/
theorem bud_nopad {b b1 : Nat} {s : State} {p len : BitVec 64}
    (hbud : b - (3 * makeCost 4 + 3 * dCost + callB s p len) ≤ b1) : b - okB s p len ≤ b1 := by
  simp only [okB]; omega

end FvModexp.Arm64.Run
