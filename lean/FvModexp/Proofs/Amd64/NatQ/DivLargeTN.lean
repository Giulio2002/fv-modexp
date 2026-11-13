import FvModexp.Proofs.Amd64.NatQ.DivLargeDRel

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeTN.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): the two inlined `norm()` loops of the tail (pattern of asm's `Rsh.norm`), and `AtR`

`q = q.norm()` (natdiv.go:632): head `fn + 0x68b` (`TESTQ CX, CX`, `RAX` = array, `RCX` = length; loop-back `+0x688
DECQ CX`), exit `fn + 0x69a`. `r = u.norm()` (natdiv.go:638): head `fn + 0x728` (`TESTQ DI, DI`, `RAX` = array, `RDI` =
length; loop-back `+0x725`), exit `fn + 0x737`. `AtR`: the state at `rJoin = fn + 0x716` (after `rshVU` + the TLS reload
of `R14`, or directly when `shift = 0`). Port of `Arm64/Nat/DivLargeTN.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (natVal_drop_zero)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

abbrev qHead : Nat := segAddr Extracted.program fn + 0x68b
abbrev qExit : Nat := segAddr Extracted.program fn + 0x69a
abbrev rHead : Nat := segAddr Extracted.program fn + 0x728
abbrev rExit : Nat := segAddr Extracted.program fn + 0x737

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `q.norm()`: from the loop head with length `i` (`RCX`) to the exit with the normalised length `n' ≤ i` -/
theorem qnorm (impl : List Amd64.Segment) (r : W64) (M : Memory) (p n0 V : Nat) (SP F G : W64) (FB : W64)
    (X15 : BitVec 128) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 qExit → s'.mem = M → s'.regs 0 = BitVec.ofNat 64 p →
      s'.regs 1 = BitVec.ofNat 64 n' → s'.regs 4 = SP → s'.regs 5 = F → s'.regs 14 = G → s'.fsBase = FB →
      s'.xmm 15 = X15 → s'.df = false → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDivL.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 qHead → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 4 = SP → S.regs 5 = F → S.regs 14 = G → S.fsBase = FB →
      S.xmm 15 = X15 → S.df = false → S.mem = M → natVal M p i = V → ReachesRet (LibDivL.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h0 hsp h5 h14 hfs hx15 hdf hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [qExit]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hx15 | exact hdf | rfl
  | succ i ih =>
    intro S hi hpc h1 h0 hsp h5 h14 hfs hx15 hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, key, BitVec.msb_eq_decide] until [qHead, qExit]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by first | (janus64_simp; done) | (janus64_simp; exact hfs))
        (by first | (janus64_simp; done) | (janus64_simp; exact hx15))
        (by first | exact hdf | (janus64_simp; done) | (janus64_simp; exact hdf)) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    next =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hi hv (Or.inr hz)
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hx15 | exact hdf | rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `u.norm()`: from the loop head with length `i` (`RDI`) to the exit with the normalised length `n' ≤ i` -/
theorem rnorm (impl : List Amd64.Segment) (r : W64) (M : Memory) (p n0 V : Nat) (SP F G : W64) (FB : W64)
    (X15 : BitVec 128) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.rip = BitVec.ofNat 64 rExit → s'.mem = M → s'.regs 0 = BitVec.ofNat 64 p →
      s'.regs 7 = BitVec.ofNat 64 n' → s'.regs 4 = SP → s'.regs 5 = F → s'.regs 14 = G → s'.fsBase = FB →
      s'.xmm 15 = X15 → s'.df = false → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' →
      ReachesRet (LibDivL.program.link impl) r s' Q)
    (hn0 : n0 < 2 ^ 40) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.rip = BitVec.ofNat 64 rHead → S.regs 7 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 4 = SP → S.regs 5 = F → S.regs 14 = G → S.fsBase = FB →
      S.xmm 15 = X15 → S.df = false → S.mem = M → natVal M p i = V → ReachesRet (LibDivL.program.link impl) r S Q := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h0 hsp h5 h14 hfs hx15 hdf hm hv
    janus64_run [hm, BitVec.msb_eq_decide] until [rExit]
    refine hfin _ 0 rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    all_goals try janus64_simp
    all_goals first | exact hfs | exact hx15 | exact hdf | rfl
  | succ i ih =>
    intro S hi hpc h1 h0 hsp h5 h14 hfs hx15 hdf hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [hm, key, BitVec.msb_eq_decide] until [rHead, rExit]
    case h =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * i by omega] at hz
      exact ih _ (by omega) rfl (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp)
        (by janus64_simp) (by first | (janus64_simp; done) | (janus64_simp; exact hfs))
        (by first | (janus64_simp; done) | (janus64_simp; exact hx15))
        (by first | exact hdf | (janus64_simp; done) | (janus64_simp; exact hdf)) rfl
        ((natVal_drop_zero hz).symm.trans hv)
    next =>
      have hz := hbr
      rw [show p + (i + 1) * 8 - 8 = p + 8 * (i + 1 - 1) by omega] at hz
      refine hfin _ (i + 1) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hi hv (Or.inr hz)
      all_goals try janus64_simp
      all_goals first | exact hfs | exact hx15 | exact hdf | rfl

/-- the join after `rshVU(u, u, shift)` + the TLS reload (natdiv.go:636; `fn + 0x716`) -/
abbrev rJoin : Nat := segAddr Extracted.program fn + 0x716

/-- the state at `rJoin`: `q` normalised (`ql` words, stored in its slots), `u = U mod V` -/
structure AtR (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat)
    (s : State) (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (Lq : List (Nat × Nat)) (P C sh qp qc : Nat)
    (L2 : List (Nat × Nat)) (b2 w2 c2 ql : Nat) (S : State) : Prop where
  pc : S.rip = BitVec.ofNat 64 rJoin
  sp : S.regs 4 = s.regs 4 - 304#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  x15 : S.xmm 15 = 0#128
  df : S.df = false
  mem : MemU R L zp zc st up uc ip il vp vl s t w2 c2 L2 b2 P C sh S.mem
  sq0 : S.mem.readLE ((s.regs 4).toNat - 64) 8 = qp
  sq1 : S.mem.readLE ((s.regs 4).toNat - 56) 8 = ql
  sq2 : S.mem.readLE ((s.regs 4).toNat - 48) 8 = qc
  ua : UArr R zp zc st up uc ip il vp vl s t w1 c1 L1 Lq P C S.mem
  qa : QArr R zp zc st vp vl il s t w1 c1 L1 L2 (stLen s.mem st + StackNat.rnd vl) P C qp qc S.mem
  ext3 : LiveExt R L1 Lq
  ext4 : LiveExt R Lq L2
  bud : b - (c + stkR H s.mem st) + (stkRes H - potK * c2) ≤ b2
  arr2 : (w2 = w1 ∧ c2 = c1) ∨ (InRanges w2 (8 * c2) R.rt ∧ ApartAll w2 (8 * c2) Lq)
  live2 : NatLive S.mem R L2 w2 c2
  c2len : stLen s.mem st + StackNat.rnd vl ≤ c2
  c2b : c2 < 2 ^ 40
  qle : ql ≤ il - vl + 1
  qval : natVal S.mem qp ql = natVal s.mem ip il / natVal s.mem vp vl
  qnrm : NatNorm S.mem qp ql
  rval : natVal S.mem P (il + 1) = natVal s.mem ip il % natVal s.mem vp vl
  reg : S.mem.regions = s.mem.regions
  arrL2 : ¬(w2 = w1 ∧ c2 = c1) → (w2, w2 + 8 * c2) ∈ L2 ∧ 0 < c2
  /-- `q`'s array is held by `Lq` (as `AtD.qL`) -/
  qL : Held R Lq qp (8 * qc)

end FvModexp.Amd64.Q.DivLarge
