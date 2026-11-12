import FvModexp.Proofs.Amd64.Top.RunDJDefs
import FvModexp.Proofs.Amd64.Top.RunCMath
import FvModexp.Proofs.Amd64.Top.RunIface

/-!
# `Run` (amd64): the compute part — definitions (twin of the arm64 `RunCDefs`)

From `D3` (`fn + 0xa3b`, the three operands read, `AX`/`BX` = `mod.abs` pointer/length) `Run` computes

* `mod.BitLen() == 0` (`fn + 0xa3b .. 0xaa7`): return `LeftPadBytes([]byte{}, modLen)` (`0xaa9 .. 0xafd`);
* else (`C2` = `fn + 0xafe`) `base.BitLen() == 1`: `v = base.Mod(base, mod).Bytes()`, otherwise
  `v = base.Exp(base, exp, mod).Bytes()` (`(*Int).exp(base, base, exp, mod, false)`);
* `V` = `fn + 0xbc5`: `LeftPadBytes(v, modLen)` and return.

Frame (`e` = entry `RSP`): `RSP' = e - 608`, `modLen` at `e - 472` (`0x88(SP)`), base / exp / mod `big.Int`s at
`e - 136` / `e - 168` / `e - 200`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

/-- `D3`: the three operands are read. -/
abbrev pcC1 : Nat := segAddr Extracted.program fn + 0xa3b
/-- `C2`: `mod ≠ 0`, `base.BitLen()` next. -/
abbrev pcC2 : Nat := segAddr Extracted.program fn + 0xafe
/-- `V`: `v` returned by `Bytes()`, `LeftPadBytes(v, modLen)` next. -/
abbrev pcCV : Nat := segAddr Extracted.program fn + 0xbc5

/-- The result EthLib's `compute` encodes: `0` for a zero modulus, else `base ^ exp mod modulus`. -/
def resV (s : State) (p len : BitVec 64) : Nat :=
  if opV s p len 2 = 0 then 0 else opV s p len 0 ^ opV s p len 1 % opV s p len 2

/-- `Run` returned `(out, nil)`: the nil `error` (type word `DI = 0`), `len(out) = BX = n`, `out` (at `AX`) holds `V`
big-endian. -/
def OkRet (s' : State) (V n : Nat) : Prop :=
  s'.regs 7 = 0#64 ∧ (s'.regs 3).toNat = n ∧ beVal s'.mem (s'.regs 0).toNat n = V

/-- The frame of a successful return with window `W` below `RSP`: as `RunFrame`, and the `n` output bytes at `q` are
the program's (a live object of the new live set, or outside the runtime-owned ranges). -/
def OkFrame (R : RtInv) (b B : Nat) (L : List (Nat × Nat)) (W : Nat) (s s' : State) (q n : Nat) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - B ≤ b' ∧
    R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ (0 < n → Held R L' q n) ∧
    MemFrame s.mem s'.mem (R.rt ++ win s W 40) ∧ LiveFrame s.mem s'.mem L []

/-- All-zero bytes have big-endian value `0`. -/
theorem beVal_zeros {m : Janus.Arm64.Memory} {q n : Nat} (h : ∀ i, i < n → (m.bytes (q + i)).toNat = 0) :
    beVal m q n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [beVal_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- A frame of the segment window `win s 4800 40` is a frame of the bigger window `win s W 40`. -/
theorem memFrame_win {m m' : Janus.Arm64.Memory} {rt : List (Nat × Nat)} {s : State} {W : Nat} (hW : 4800 ≤ W)
    (h : MemFrame m m' (rt ++ win s 4800 40)) : MemFrame m m' (rt ++ win s W 40) :=
  h.mono fun a n hh => by
    simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at hh ⊢
    exact ⟨hh.1, by omega⟩

/-- The block of a `make([]byte, n)` with `n ≤ 1024` fits the budget left after the operands. -/
theorem bs_le {n b b1 B : Nat} (hn : n ≤ 1024) (hB : 3 * makeCost 4 + 3 * dCost + allocCost 1024 ≤ B) (hbB : B ≤ b)
    (hbud : b - (3 * makeCost 4 + 3 * dCost) ≤ b1) :
    blockSize n true ≤ b1 ∧ b - B ≤ b1 - blockSize n true := by
  have := blockSize_le_allocCost n true
  simp only [allocCost] at this hB ⊢; omega

/-- The word count bound of operand `j` from its byte length: `⌈len / 8⌉`. -/
@[reducible] def opW (s : State) (p len : BitVec 64) (j : Nat) : Nat := (hdrV s p len j + 7) / 8

/-- The largest operand word count bound. -/
@[reducible] def wMax (s : State) (p len : BitVec 64) : Nat := max (max (opW s p len 0) (opW s p len 1)) (opW s p len 2)

/-- The budget of the compute calls (`Mod` or `exp`, then `Bytes`), from the operand lengths. -/
def callB (s : State) (p len : BitVec 64) : Nat :=
  RunIface.ModBudget (wMax s p len) + RunIface.ExpBudget (wMax s p len) (opW s p len 1) +
    RunIface.BytesBudget RunIface.maxW

/-- The state at `V` (`fn + 0xbc5`): `v = (AX, BX, CX)` returned by `Bytes()` holds the result, minimal, at most
`modLen` bytes, a fresh live object; the frame slots `LeftPadBytes` and the epilogue read; the frames with window `W`. -/
def RelV (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (p len : BitVec 64) (s : State) (ret W : Nat)
    (Lk : List (Nat × Nat)) (bk : Nat) (V : State) : Prop :=
  V.regs 4 = s.regs 4 - 608#64 ∧ V.regs 14 = s.regs 14 ∧ V.regs 5 = s.regs 4 - 8#64 ∧ V.xmm 15 = s.xmm 15 ∧
  V.fsBase = s.fsBase ∧ V.df = s.df ∧
  V.mem.readLE (s.regs 4).toNat 8 = ret ∧ V.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
  V.mem.readLE ((s.regs 4).toNat - 472) 8 = hdrV s p len 2 ∧ hdrV s p len 2 ≤ 1024 ∧
  Extracted.program.DataLoaded V.mem ∧
  (V.regs 3).toNat ≤ hdrV s p len 2 ∧ beVal V.mem (V.regs 0).toNat (V.regs 3).toNat = resV s p len ∧
  (0 < (V.regs 3).toNat → InRanges (V.regs 0).toNat (V.regs 3).toNat Lk ∧
    InRanges (V.regs 0).toNat (V.regs 3).toNat R.rt ∧
    V.mem.accessible (V.regs 0).toNat (V.regs 3).toNat true = true ∧ (V.regs 0).toNat + (V.regs 3).toNat ≤ 2 ^ 48) ∧
  LiveExt R L Lk ∧ b - (3 * makeCost 4 + 3 * dCost + callB s p len) ≤ bk ∧
  R.inv bk Lk (s.regs 14).toNat (view R.rt Lk V.mem) ∧ LiveSep Lk (win s W 40) ∧
  MemFrame s.mem V.mem (R.rt ++ win s W 40) ∧ LiveFrame s.mem V.mem L []

/-- The budget of the whole success path: the operands, the compute calls, the `LeftPadBytes` buffer. -/
def okB (s : State) (p len : BitVec 64) : Nat := 3 * makeCost 4 + 3 * dCost + callB s p len + allocCost 1024

theorem outW_w {rt : List (Nat × Nat)} {s : State} {W a n : Nat} (h : Outside a n (rt ++ win s W 40)) :
    Outside a n (win s W 40) := (Janus.outside_append _ _ _ _ |>.mp h).2

/-- The runtime callee stack of a call from `Run`'s frame (`RSP = e - 608`, return slot `e - 616`) is inside `Run`'s
window. -/
theorem outW_cs {rt : List (Nat × Nat)} {s : State} {W a n : Nat} (hW : 4800 ≤ W)
    (h : Outside a n (rt ++ win s W 40)) :
    Outside a n (rt ++ ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
      ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
      [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)])) := by
  simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
  refine ⟨h.1, ?_⟩; omega

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

end FvModexp.Amd64.Run
