import FvModexp.Proofs.Arm64.Exp.SubMod2NSeg
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.GenReg

/-!
# `nat.subMod2N` (arm64): entry → `J1` (agent infra)

`x.bitLen()` (inline: the OR-smear + `CLZ`, `BitLenA64`), and when it exceeds `n`, `x = x.trunc(x, n)` (`x = z`, so
`alias(z, x)` holds; `TruncHyp`, in place since `cap z ≥ ⌈n/64⌉`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp


set_option maxRecDepth 20000 in
/-- `J1` reached by stack-only stores (`x` not truncated: `X < 2^n`) -/
theorem j1_stack {impl : List Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k1 : J1 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s) (S : State)
    (hF : MemFrame s.mem S.mem (winA s K A)) (hreg : S.mem.regions = s.mem.regions)
    (hpc : S.pc = BitVec.ofNat 64 (1805584 + 0xfc)) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144))
    (h28 : S.regs 28 = s.regs 28) (h18 : S.regs 18 = s.regs 18)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 zp) (h4 : S.regs 4 = BitVec.ofNat 64 zl) (h5 : S.regs 5 = BitVec.ofNat 64 zc)
    (h6 : S.regs 6 = BitVec.ofNat 64 yp) (h7 : S.regs 7 = BitVec.ofNat 64 yl) (h8 : S.regs 8 = BitVec.ofNat 64 yc)
    (h9 : S.regs 9 = BitVec.ofNat 64 n) (hfw : Fw s S.mem zp zl zc yp n) (hv : natVal s.mem zp zl < 2 ^ n) :
    Goal impl R b L zp zl zc yp yl n s S := by
  have hzw : Outside zp (8 * zl) (winA s K A) := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h8 := hpre.2.2.2.2.2.2.2.2.1
    simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢
    omega
  refine k1 S zl L b hpre hpc hsp h28 h18 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hfw (rt_stack hpre 1 hF hreg) ?_ ?_
    hpre.2.2.2.2.2.2.2.2.1
  · rw [natVal_frame hF hzw, Nat.mod_eq_of_lt hv]
  · exact natNorm_frame hF hzw hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem s1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : TruncHyp impl R ns stkT aboveT)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 1805584)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc)
    (h3 : s.regs 3 = BitVec.ofNat 64 zp) (h4 : s.regs 4 = BitVec.ofNat 64 zl) (h5 : s.regs 5 = BitVec.ofNat 64 zc)
    (h6 : s.regs 6 = BitVec.ofNat 64 yp) (h7 : s.regs 7 = BitVec.ofNat 64 yl) (h8 : s.regs 8 = BitVec.ofNat 64 yc)
    (h9 : s.regs 9 = BitVec.ofNat 64 n)
    (hpre : Pre R b L op zp zl zc yp yl yc n s) (k1 : J1 impl R b L op zp zl zc yp yl yc n s) :
    Goal impl R b L zp zl zc yp yl n s s := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, hzl',
    hyl, hyc, hyl', hzlive, hzw, -⟩ := hpre'
  simp only [W] at hW
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hza : s.mem.accessible zp (8 * zl) false = true :=
    Memory.accessible_sub _ (hzlive (by omega)).2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw hout
  simp only [K, A] at hw hout hzw hg3 hb' ha hga
  unfold Goal
  by_cases hz0 : zl = 0
  · subst hz0
    janus_run until [1805836]
    refine j1_stack k1 hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [winA, K, A]; janus_frame
    all_goals try janus_simp
    · exact Expmc.sp_sub _ _ (by omega) (by omega)
    · simp only [Fw]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp
    · exact Nat.lt_of_lt_of_le (natVal_lt _ _ _) (Nat.one_le_two_pow)
  have e1 : (zp + 8 * (18446744073709551615 + zl)) % 18446744073709551616 = zp + 8 * (zl - 1) := by omega
  have h63 : (BitVec.ofNat 64 zl - 1#64).getLsbD 63 = false := by
    have e : (BitVec.ofNat 64 zl - 1#64).toNat = zl - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    show (BitVec.ofNat 64 zl - 1#64).toNat.testBit 63 = false
    rw [e]; exact Nat.testBit_lt_two_pow (by omega)
  janus_run [e1, h63] until [1805636]
  generalize hxd : BitVec.ofNat 64 (s.mem.readLE (zp + 8 * (zl - 1)) 8) = x
  janus_run until [1805660]
  trace_state
  gen_reg 11 as t with hT
  janus_run until [1805676]
  gen_reg 10 as bl with hBl
  have hbl : bl.toNat = 64 * (zl - 1) + Aux.bitLen (s.mem.readLE (zp + 8 * (zl - 1)) 8) := by
    rw [← hBl, ← hT, ← BitLenA64.smearBV, BitLenA64.clz_smear, ← hxd, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Util.readLE8_lt _ _)]
    exact BitLenA64.bl_exact _ _ (Util.readLE8_lt _ _) (by omega) (by omega)
  by_cases hc : bl.toNat ≤ n
  · janus_run [hc] until [1805836]
    refine j1_stack k1 hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [winA, K, A]; janus_frame
    all_goals try janus_simp
    · exact Expmc.sp_sub _ _ (by omega) (by omega)
    · simp only [Fw]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp
    · refine Nat.lt_of_lt_of_le (BitLenA64.natVal_lt_bl _ _ _ (by omega)) (Nat.pow_le_pow_right (by omega) ?_)
      omega
  · janus_run [hc] until [1786000]
    sorry

end FvModexp.Arm64.SubMod2N
