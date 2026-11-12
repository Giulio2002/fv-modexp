import FvModexp.Proofs.Amd64.Top.RunCDefs

/-!
# `Run` (amd64): `LeftPadBytes(v, modLen)` — the cut after `makeslice`

`P` (`fn + 0xbf5`) is the return of `makeslice(uint8, modLen, modLen)` when `len(v) < modLen`: `AX` = the fresh zeroed
buffer `buf`; `v`'s pointer and length are spilled at `0x170(SP)` (`e - 240`) and `0x30(SP)` (`e - 560`). From `P` the
code copies `v` to the tail of `buf` (`memmove`, skipped when source and destination coincide) and returns
`(buf, modLen, modLen)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

abbrev pcP : Nat := segAddr Extracted.program fn + 0xbf5

/-- The state at `P`. -/
def JoinP (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (p len : BitVec 64) (s : State) (ret W : Nat)
    (Lk : List (Nat × Nat)) (bk vp vn buf : Nat) (U : State) : Prop :=
  U.regs 4 = s.regs 4 - 608#64 ∧ U.regs 14 = s.regs 14 ∧ U.regs 5 = s.regs 4 - 8#64 ∧ U.xmm 15 = s.xmm 15 ∧
  U.fsBase = s.fsBase ∧ U.df = s.df ∧
  U.mem.readLE (s.regs 4).toNat 8 = ret ∧ U.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
  U.mem.readLE ((s.regs 4).toNat - 472) 8 = hdrV s p len 2 ∧ hdrV s p len 2 ≤ 1024 ∧
  U.mem.readLE ((s.regs 4).toNat - 240) 8 = vp ∧ U.mem.readLE ((s.regs 4).toNat - 560) 8 = vn ∧ vn < hdrV s p len 2 ∧
  (U.regs 0).toNat = buf ∧ buf + hdrV s p len 2 ≤ 2 ^ 48 ∧ s.mem.accessible buf (hdrV s p len 2) true = true ∧
  (∀ j, j < hdrV s p len 2 → (U.mem.bytes (buf + j)).toNat = 0) ∧
  InRanges buf (hdrV s p len 2) Lk ∧ InRanges buf (hdrV s p len 2) R.rt ∧ LiveSep L [(buf, buf + hdrV s p len 2)] ∧
  beVal U.mem vp vn = resV s p len ∧
  (0 < vn → vp + vn ≤ 2 ^ 48 ∧ s.mem.accessible vp vn false = true ∧ Apart vp vn buf (hdrV s p len 2) ∧
    (vp + vn ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 40 ≤ vp)) ∧
  Extracted.program.DataLoaded U.mem ∧
  LiveExt R L Lk ∧ b - okB s p len ≤ bk ∧ R.inv bk Lk (s.regs 14).toNat (view R.rt Lk U.mem) ∧
  LiveSep Lk (win s W 40) ∧ MemFrame s.mem U.mem (R.rt ++ win s W 40) ∧ LiveFrame s.mem U.mem L []

/-- The destination offset `LeftPadBytes` computes (amd64: `SI = L - vn`, `R8 = SI & ((SI - L) >> 63)`): `L - vn`, masked
to `0` when `len(v) = 0`. -/
theorem padMask64 (L vn : Nat) (hvn : vn < L) (hL : L ≤ 1024) :
    (BitVec.ofNat 64 L - BitVec.ofNat 64 vn &&&
      (BitVec.ofNat 64 L - BitVec.ofNat 64 vn - BitVec.ofNat 64 L).sshiftRight 63) =
      BitVec.ofNat 64 (if vn = 0 then 0 else L - vn) := by
  by_cases h0 : vn = 0
  · subst h0; simp
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have e1 : (BitVec.ofNat 64 L - BitVec.ofNat 64 vn).toNat = L - vn := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := L) (by omega), Nat.mod_eq_of_lt (a := vn) (by omega)]; omega
    rw [e1, sliceMask_lt (L - vn) (BitVec.ofNat 64 L - BitVec.ofNat 64 vn) (BitVec.ofNat 64 L)
      (by rw [e1]; simp only [BitVec.toNat_ofNat]; omega)
      (by simp only [BitVec.toNat_ofNat]; omega) (by omega)]
    simp only [h0, if_false, BitVec.toNat_ofNat]; omega

/-- `padMask64` in the form `janus64_run` normalises the mask operand to (`L - (vn + L)`). -/
theorem padMask64' (L vn : Nat) (hvn : vn < L) (hL : L ≤ 1024) :
    (BitVec.ofNat 64 L - BitVec.ofNat 64 vn &&&
      (BitVec.ofNat 64 L - BitVec.ofNat 64 (vn + L)).sshiftRight 63) =
      BitVec.ofNat 64 (if vn = 0 then 0 else L - vn) := by
  by_cases h0 : vn = 0
  · subst h0; simp
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have e1 : (BitVec.ofNat 64 L - BitVec.ofNat 64 vn).toNat = L - vn := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := L) (by omega), Nat.mod_eq_of_lt (a := vn) (by omega)]; omega
    rw [e1, sliceMask_lt (L - vn) (BitVec.ofNat 64 L) (BitVec.ofNat 64 (vn + L))
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega) (by omega)]
    simp only [h0, if_false, BitVec.toNat_ofNat]; omega

/-- The copy length `L - (L - vn)` is `len(v)`. -/
theorem padLen64 (L vn : Nat) (hvn : vn < L) (hL : L ≤ 1024) :
    BitVec.ofNat 64 L - (BitVec.ofNat 64 L - BitVec.ofNat 64 vn) = BitVec.ofNat 64 vn := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega

/-- Equal bytes at two addresses give equal big-endian values. -/
theorem beVal_congr' {m m' : Janus.Arm64.Memory} {p p' n : Nat} (h : ∀ i, i < n → m'.bytes (p' + i) = m.bytes (p + i)) :
    beVal m' p' n = beVal m p n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [beVal_succ, beVal_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- The object `[d, d + k)` of the runtime is in the frame `R.rt` already. -/
theorem outW_csd {rt : List (Nat × Nat)} {s : State} {W a n d k : Nat} (hW : 4800 ≤ W) (hd : InRanges d k rt)
    (h : Outside a n (rt ++ win s W 40)) :
    Outside a n (rt ++ ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
      ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
      [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) ++ [(d, d + k)]) := by
  have h1 := outW_cs hW h
  simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h h1 ⊢
  have := InRanges.apart hd h.1
  unfold Apart at this
  exact ⟨h1, by omega⟩

end FvModexp.Amd64.Run
