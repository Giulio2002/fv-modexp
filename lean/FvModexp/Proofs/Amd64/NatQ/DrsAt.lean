import FvModexp.Proofs.Amd64.NatQ.DrsPro1

set_option autoImplicit false

/-!
# `divRecursiveStep` (amd64): the state at the dispatch `dTest` (after `u.norm()`, `v.norm()`)

`AtE2 s P …`: `P` is at `TESTQ R8, R8` (`0x5ef910`) with the frame facts `Fr s P`, the eight register arguments (with the
normalised `len u` in `R8`), `v = (vp, vl, vc)` in `DX`, `R11`, `R12`, and the spills / defer slots written by the
prologue. Shared by the entry composition and every path (segment modules import this, not each other).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `Fr` is a property of the registers `RSP`, `RBP`, `R14`, `fsBase`, `DF` and the memory -/
theorem Fr.congr {s P P' : State} (hF : Fr s P) (hm : P'.mem = P.mem) (h4 : P'.regs 4 = P.regs 4)
    (h5 : P'.regs 5 = P.regs 5) (h14 : P'.regs 14 = P.regs 14) (hfs : P'.fsBase = P.fsBase) (hdf : P'.df = P.df) :
    Fr s P' :=
  ⟨h4.trans hF.sp, h5.trans hF.r5, h14.trans hF.r14, hfs.trans hF.fs, hdf.trans hF.df, by rw [hm]; exact hF.reg,
    by rw [hm]; exact hF.fr, by rw [hm]; exact hF.ra, by rw [hm]; exact hF.bp, by rw [hm]; exact hF.vp,
    by rw [hm]; exact hF.vl, by rw [hm]; exact hF.vc⟩

/-- the state at the dispatch (`R8` = normalised `len u`) -/
structure AtE2 (s P : State) (qp ql qc st up ul uc vp vl vc d : Nat) : Prop where
  pc : P.rip = BitVec.ofNat 64 dTest
  fr : Fr s P
  x15 : P.xmm 15 = 0#128
  r0 : P.regs 0 = BitVec.ofNat 64 qp
  r3 : P.regs 3 = BitVec.ofNat 64 ql
  r1 : P.regs 1 = BitVec.ofNat 64 qc
  r7 : P.regs 7 = BitVec.ofNat 64 st
  r6 : P.regs 6 = BitVec.ofNat 64 up
  r8 : P.regs 8 = BitVec.ofNat 64 ul
  r9 : P.regs 9 = BitVec.ofNat 64 uc
  r10 : P.regs 10 = BitVec.ofNat 64 d
  r2 : P.regs 2 = BitVec.ofNat 64 vp
  r11 : P.regs 11 = BitVec.ofNat 64 vl
  r12 : P.regs 12 = BitVec.ofNat 64 vc
  sq : P.mem.readLE ((s.regs 4).toNat + 32) 8 = qp
  su : P.mem.readLE ((s.regs 4).toNat + 64) 8 = up
  d16 : P.mem.readLE ((s.regs 4).toNat - 16) 8 = 0
  d297 : P.mem.readLE ((s.regs 4).toNat - 297) 1 = 0

/-- a value whose top word is nonzero is at least `2^(64·(n-1))` (= arm64 NatQ/DrsPro `natVal_ge`) -/
theorem natVal_ge (m : Memory) (p n : Nat) (hn : 1 ≤ n) (ht : m.readLE (p + 8 * (n - 1)) 8 ≠ 0) :
    2 ^ (64 * (n - 1)) ≤ natVal m p n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at ht ⊢
  rw [natVal_succ]
  have : 1 ≤ m.readLE (p + 8 * k) 8 := Nat.pos_of_ne_zero ht
  calc 2 ^ (64 * k) = 2 ^ (64 * k) * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ (64 * k) * m.readLE (p + 8 * k) 8 := Nat.mul_le_mul_left _ this
    _ ≤ _ := Nat.le_add_left _ _

/-- a normalised divisor whose top word is set keeps its length -/
theorem norm_v {M : Memory} {vp vl n' : Nat} (h2 : 1 ≤ vl) (htop : 2 ^ 63 ≤ M.readLE (vp + 8 * (vl - 1)) 8)
    (hle : n' ≤ vl) (hv : natVal M vp n' = natVal M vp vl) : n' = vl := by
  refine Nat.le_antisymm hle (Nat.not_lt.1 fun hlt => ?_)
  have h1 := natVal_lt M vp n'
  have h3 := natVal_ge M vp vl h2 (by omega)
  have h4 : 2 ^ (64 * n') ≤ 2 ^ (64 * (vl - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end FvModexp.Amd64.Q.DivRec
