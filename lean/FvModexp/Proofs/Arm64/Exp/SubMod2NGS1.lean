import FvModexp.Proofs.Arm64.Exp.SubMod2NGC
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.GenReg

/-!
# `nat.subMod2N` (arm64), general form: entry → `J1G` (agent infra)

`x.bitLen()` (inline: the OR-smear + `CLZ`, `BitLenA64`), and when it exceeds `n`, `x = x.trunc(x, n)` (`x = z`, so
`alias(z, x)` holds; `TruncHyp`, in place: `len x > ⌈n/64⌉`... `x.bitLen() > n` gives `len x ≥ ⌈n/64⌉`).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp


set_option maxRecDepth 20000 in
/-- `J1` reached by stack-only stores (`x` not truncated: `X < 2^n`) -/
theorem j1G_stack {impl : List Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k1 : J1G impl R b L op zp zl zc yp yl yc n s) (hpre : PreG R b L op zp zl zc yp yl yc n s) (S : State)
    (hF : MemFrame s.mem S.mem (winA s K A)) (hreg : S.mem.regions = s.mem.regions)
    (hpc : S.pc = BitVec.ofNat 64 (1805584 + 0xfc)) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 144))
    (h28 : S.regs 28 = s.regs 28) (h18 : S.regs 18 = s.regs 18)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 zp) (h4 : S.regs 4 = BitVec.ofNat 64 zl) (h5 : S.regs 5 = BitVec.ofNat 64 zc)
    (h6 : S.regs 6 = BitVec.ofNat 64 yp) (h7 : S.regs 7 = BitVec.ofNat 64 yl) (h8 : S.regs 8 = BitVec.ofNat 64 yc)
    (h9 : S.regs 9 = BitVec.ofNat 64 n) (hfw : Fw s S.mem zp zl zc yp n) (hv : natVal s.mem zp zl < 2 ^ n) :
    GoalG impl R b L zp zl zc yp yl n s S := by
  have hzw : Outside zp (8 * zl) (winA s K A) := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h8 := hpre.2.2.2.2.2.2.2.2.1
    simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢
    omega
  refine k1 S zl L b hpre hpc hsp h28 h18 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hfw (rtG_stack hpre 1 hF hreg) ?_ ?_
    hpre.2.2.2.2.2.2.2.2.1
  · rw [natVal_frame hF hzw, Nat.mod_eq_of_lt hv]
  · exact natNorm_frame hF hzw hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- after `x = x.trunc(x, n)` returns (at `+0xbc`): reload `y`, `n`, `z`, move the result to `X3..X5`, `J1` -/
theorem s1Gt (impl : List Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k1 : J1G impl R b L op zp zl zc yp yl yc n s) (hpre : PreG R b L op zp zl zc yp yl yc n s)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (M0 : Memory) (hrt0 : Rt R b L s zp zc n 0 M0 L b)
    (hfw0 : Fw s M0 zp zl zc yp n) (r64 : M0.readLE (s.sp.toNat + 64) 8 = yl)
    (r72 : M0.readLE (s.sp.toNat + 72) 8 = yc) (hv0 : natVal M0 zp zl = natVal s.mem zp zl)
    (S0 : State) (hS0 : S0.mem = M0) (hsp0 : S0.sp = BitVec.ofNat 64 (s.sp.toNat - 144)) (h280 : S0.regs 28 = s.regs 28)
    (s' : State) (hpc' : s'.pc = BitVec.ofNat 64 (1805584 + 4 * 47)) (hsp' : s'.sp = S0.sp)
    (h28' : s'.regs 28 = S0.regs 28) (h18' : s'.regs 18 = s.regs 18) (hreg' : s'.mem.regions = S0.mem.regions)
    (hpost : TruncPost R b L stkT aboveT zp zc zp zl n S0 s') :
    GoalG impl R b L zp zl zc yp yl n s s' := by
  obtain ⟨⟨⟨-, -, -⟩, ⟨hal, hb', ha, hw⟩, -, hout, -, -, -, -⟩, -, -, -, -, -, -, -, hzl, -, hzc, -, -, -, -, -,
    hzw, -⟩ := id hpre
  obtain ⟨p', l', c', e0, e1, e2, L', b', ⟨hv, hnorm, hlc, -, hlive, hreuse, -⟩, -, ⟨hLE, hbud, hinv⟩, hF, hLF⟩ := hpost
  obtain ⟨rfl, rfl⟩ := hreuse (by unfold truncNeed; omega)
  have hspT : S0.sp.toNat = s.sp.toNat - 144 := by rw [hsp0]; exact tN (by omega)
  simp only [winA, hspT] at hF
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hacc' : s'.mem.accessible (s.sp.toNat - 4608) (4608 + 88) true = true := by
    rw [hF.accessible, hS0, hrt0.2.1.accessible]; exact hw
  have rd : ∀ a, s.sp.toNat - 152 ≤ a → a + 8 ≤ s.sp.toNat + 88 → (a + 8 ≤ s.sp.toNat - 136 ∨ s.sp.toNat - 56 ≤ a) →
      s'.mem.readLE a 8 = M0.readLE a 8 := by
    intro a h1 h2 h3
    rw [← hS0]
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw0
  have r8 := (rd (s.sp.toNat + 8) (by omega) (by omega) (by omega)).trans f3
  have r16 := (rd (s.sp.toNat + 16) (by omega) (by omega) (by omega)).trans f4
  have r24 := (rd (s.sp.toNat + 24) (by omega) (by omega) (by omega)).trans f5
  have r56 := (rd (s.sp.toNat + 56) (by omega) (by omega) (by omega)).trans f6
  have r64' := (rd (s.sp.toNat + 64) (by omega) (by omega) (by omega)).trans r64
  have r72' := (rd (s.sp.toNat + 72) (by omega) (by omega) (by omega)).trans r72
  have r80 := (rd (s.sp.toNat + 80) (by omega) (by omega) (by omega)).trans f7
  have rl := (rd (s.sp.toNat - 144) (by omega) (by omega) (by omega)).trans f1
  have rf := (rd (s.sp.toNat - 152) (by omega) (by omega) (by omega)).trans f2
  have hsp'' : s'.sp = BitVec.ofNat 64 (s.sp.toNat - 144) := hsp'.trans hsp0
  unfold GoalG
  janus_run [r8, r16, r24, r56, r64', r72', r80] until [1805836]
  refine k1 _ l' L' b' hpre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hlc
  all_goals try janus_simp
  · rw [show BitVec.toNat s.sp - 144 + 152 = BitVec.toNat s.sp + 8 by omega, f3]
  · rw [show BitVec.toNat s.sp - 144 + 160 = BitVec.toNat s.sp + 16 by omega, f4]
  · rw [show BitVec.toNat s.sp - 144 + 168 = BitVec.toNat s.sp + 24 by omega, f5]
  · rw [show BitVec.toNat s.sp - 144 + 200 = BitVec.toNat s.sp + 56 by omega, f6]
  · rw [show BitVec.toNat s.sp - 144 + 208 = BitVec.toNat s.sp + 64 by omega, r64]
  · rw [show BitVec.toNat s.sp - 144 + 216 = BitVec.toNat s.sp + 72 by omega, r72]
  · rw [show BitVec.toNat s.sp - 144 + 224 = BitVec.toNat s.sp + 80 by omega, f7]
  · exact ⟨rl, rf, r8, r16, r24, r56, r80⟩
  · rw [hS0] at hF hreg' hLF
    rw [h280] at hinv
    exact rt_call hrt0 (by omega) hkT (by omega) (Or.inl rfl) hreg' hF hLF hLE hbud (truncNeed_le_w _ _) hinv hlive
  · rw [hv, hS0, hv0]
  · exact hnorm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem s1G (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4464) (haT : aboveT ≤ 88) (htr : Trunc.Hyp2 impl R ns stkT aboveT)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 1805584)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc)
    (h3 : s.regs 3 = BitVec.ofNat 64 zp) (h4 : s.regs 4 = BitVec.ofNat 64 zl) (h5 : s.regs 5 = BitVec.ofNat 64 zc)
    (h6 : s.regs 6 = BitVec.ofNat 64 yp) (h7 : s.regs 7 = BitVec.ofNat 64 yl) (h8 : s.regs 8 = BitVec.ofNat 64 yc)
    (h9 : s.regs 9 = BitVec.ofNat 64 n)
    (hpre : PreG R b L op zp zl zc yp yl yc n s) (k1 : J1G impl R b L op zp zl zc yp yl yc n s) :
    GoalG impl R b L zp zl zc yp yl n s s := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, hzl',
    hyl, hyc, hyl', hzlive, hzw, -⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hzw hout
  simp only [K, A] at hw hout hzw hg3 hb' ha hga
  unfold GoalG
  by_cases hz0 : zl = 0
  · subst hz0
    janus_run until [1805836]
    refine j1G_stack k1 hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [winA, K, A]; janus_frame
    all_goals try janus_simp
    · exact Expmc.sp_sub _ _ (by omega) (by omega)
    · simp only [Fw]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp
    · exact Nat.lt_of_lt_of_le (natVal_lt _ _ _) (Nat.one_le_two_pow)
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hza : s.mem.accessible zp (8 * zl) false = true :=
    Memory.accessible_sub _ (hzlive (by omega)).2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega)
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
    refine j1G_stack k1 hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [winA, K, A]; janus_frame
    all_goals try janus_simp
    · exact Expmc.sp_sub _ _ (by omega) (by omega)
    · simp only [Fw]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp
    · refine Nat.lt_of_lt_of_le (BitLenA64.natVal_lt_bl _ _ _ (by omega)) (Nat.pow_le_pow_right (by omega) ?_)
      omega
  · janus_run [hc] until [1786000]
    have hzw' : Outside zp (8 * zl) (winA s K A) := by simp only [winA, K, A, outside_cons, outside_nil, and_true]; omega
    refine truncCall hap hns htr (zp := zp) (zl := zl) (zc := zc) (x := zp) (xl := zl) (xc := zc) (n := n)
      (ra_of hap hnf 47 (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
      (truncPreG_self hpre hpre.costB (rtG_stack hpre 0 ?_ ?_) (by omega) rfl ?_ ?_ hkT haT hzl (by omega) ?_
        (by omega) ((hzlive (by omega)).2.1.sub (Nat.le_refl _) (by omega)) (by omega) (by omega) (Or.inl rfl))
      (Or.inr (by have := bitLen_le64 (s.mem.readLE (zp + 8 * (zl - 1)) 8) (Util.readLE8_lt _ _); omega))
      (Or.inl rfl)
      fun s' hpc' hsp' h28' h29' h18' hreg' hpost => ?qK
    case qK =>
      refine s1Gt impl k1 hpre hkT haT _ (rtG_stack hpre 0 ?_ ?_) ?_ ?_ ?_ ?_ _ rfl ?_ ?_ s' hpc' hsp' h28' ?_ hreg' hpost
      · simp only [winA, K, A]; janus_frame
      · janus_simp
      · simp only [Fw]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus_simp
      · janus_simp
      · janus_simp
      · exact natVal_frame (by simp only [winA, K, A]; janus_frame) hzw'
      · janus_simp; exact Expmc.sp_sub _ _ (by omega) (by omega)
      · janus_simp
      · rw [h18']; janus_simp
    all_goals try janus_simp
    · simp only [winA, K, A]; janus_frame
    · exact Expmc.sp_sub _ _ (by omega) (by omega)
    · exact hza

end FvModexp.Arm64.SubMod2N
