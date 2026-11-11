import FvModexp.Proofs.Arm64.Top.RunCDefs
import FvModexp.Proofs.Arm64.Top.RunD2Lem

/-!
# `Run` (arm64): `LeftPadBytes(v, modLen)` — the cut after `makeslice`

`P` (`fn + 0x8a8`) is the return of `makeslice(uint8, modLen, modLen)` when `len(v) < modLen`: `X0` = the fresh zeroed
buffer `buf`; `v`'s pointer and length are spilled at `384(RSP)` and `64(RSP)`. From `P` the code copies `v` to the tail
of `buf` (`memmove`, skipped when source and destination coincide) and returns `(buf, modLen, modLen)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Run

abbrev pcP : Nat := segAddr Extracted.program fn + 0x8a8

/-- The state at `P`. -/
def JoinP (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (p len : BitVec 64) (s : State) (ret W : Nat)
    (Lk : List (Nat × Nat)) (bk vp vn buf : Nat) (U : State) : Prop :=
  U.sp = s.sp - 624#64 ∧ U.regs 28 = s.regs 28 ∧ U.regs 29 = s.sp - 632#64 ∧ U.regs 18 = s.regs 18 ∧
  U.mem.readLE (s.sp.toNat - 624) 8 = ret ∧ U.mem.readLE (s.sp.toNat - 632) 8 = (s.regs 29).toNat ∧
  U.mem.readLE (s.sp.toNat - 464) 8 = hdrV s p len 2 ∧ hdrV s p len 2 ≤ 1024 ∧
  U.mem.readLE (s.sp.toNat - 240) 8 = vp ∧ U.mem.readLE (s.sp.toNat - 560) 8 = vn ∧ vn < hdrV s p len 2 ∧
  (U.regs 0).toNat = buf ∧ buf + hdrV s p len 2 ≤ 2 ^ 48 ∧ s.mem.accessible buf (hdrV s p len 2) true = true ∧
  (∀ j, j < hdrV s p len 2 → (U.mem.bytes (buf + j)).toNat = 0) ∧
  InRanges buf (hdrV s p len 2) Lk ∧ InRanges buf (hdrV s p len 2) R.rt ∧ LiveSep L [(buf, buf + hdrV s p len 2)] ∧
  beVal U.mem vp vn = resV s p len ∧
  (0 < vn → vp + vn ≤ 2 ^ 48 ∧ s.mem.accessible vp vn false = true ∧ Apart vp vn buf (hdrV s p len 2) ∧
    (vp + vn ≤ s.sp.toNat - W ∨ s.sp.toNat + 40 ≤ vp)) ∧
  Extracted.program.DataLoaded U.mem ∧
  LiveExt R L Lk ∧ b - okB s p len ≤ bk ∧ R.inv bk Lk (s.regs 28).toNat (view R.rt Lk U.mem) ∧
  LiveSep Lk (win s W 40) ∧ MemFrame s.mem U.mem (R.rt ++ win s W 40) ∧ LiveFrame s.mem U.mem L []

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

/-- The destination offset `LeftPadBytes` computes: `modLen - len(v)` masked to `0` when `len(v) = 0`. -/
theorem padMask (L vn : Nat) (hvn : vn < L) (hL : L ≤ 1024) :
    (BitVec.ofNat 64 L - BitVec.ofNat 64 vn &&&
      (BitVec.ofNat 64 L - (BitVec.ofNat 64 L + BitVec.ofNat 64 vn)).sshiftRight 63) =
      BitVec.ofNat 64 (if vn = 0 then 0 else L - vn) := by
  by_cases h0 : vn = 0
  · subst h0; simp
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have e1 : (BitVec.ofNat 64 L - BitVec.ofNat 64 vn).toNat = L - vn := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := L) (by omega), Nat.mod_eq_of_lt (a := vn) (by omega)]; omega
    rw [e1, sliceMask_lt (L - vn) (BitVec.ofNat 64 L) (BitVec.ofNat 64 L + BitVec.ofNat 64 vn)
      (by rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega)
      (by rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega) (by omega)]
    simp only [h0, if_false, BitVec.toNat_ofNat]; omega

/-- The copy length `min(len(v), modLen - (modLen - len(v)))` is `len(v)`. -/
theorem padLen (L vn : Nat) (hvn : vn < L) (hL : L ≤ 1024) :
    (if (vn : Int) < (((18446744073709551616 - L + (L + vn)) % 18446744073709551616 : Nat) : Int) then BitVec.ofNat 64 vn
      else BitVec.ofNat 64 L + BitVec.ofNat 64 vn - BitVec.ofNat 64 L) = BitVec.ofNat 64 vn := by
  have : (18446744073709551616 - L + (L + vn)) % 18446744073709551616 = vn := by omega
  rw [this, if_neg (by omega)]
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run

open Janus Janus.Arm64

/-- Equal bytes at two addresses give equal big-endian values. -/
theorem beVal_congr' {m m' : Memory} {p p' n : Nat} (h : ∀ i, i < n → m'.bytes (p' + i) = m.bytes (p + i)) :
    beVal m' p' n = beVal m p n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [beVal_succ, beVal_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

end FvModexp.Arm64.Run
