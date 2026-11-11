import FvModexp.Proofs.Amd64.Exp.SubMod2NCall
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.GenReg

/-!
# `nat.subMod2N` (amd64): entry → `J1` (agent infra)

`x.bitLen()` (inline: the OR-smear, `BSR`, `CMOVE`; `BitLenA64.bl_exact64`), and when it exceeds `n`,
`x = x.trunc(x, n)` (`x = z`, so `alias(z, x)` holds; `TruncHyp`, in place since `cap z ≥ ⌈n/64⌉`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

theorem ent_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) : Ent s zp zc n :=
  hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

set_option maxRecDepth 20000 in
/-- `J1` reached by stack-only stores (`x` not truncated: `X < 2^n`) -/
theorem j1_stack {impl : List Amd64.Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {op zp zl zc yp yl yc n : Nat}
    {s : State} (k1 : J1 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s) (S : State)
    (hF : MemFrame s.mem S.mem (win s K A)) (hreg : S.mem.regions = s.mem.regions)
    (hpc : S.rip = BitVec.ofNat 64 6216183) (hsp : S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128))
    (hab : Abi s S)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 zp) (h6 : S.regs 6 = BitVec.ofNat 64 zl) (h8 : S.regs 8 = BitVec.ofNat 64 zc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yp) (h10 : S.regs 10 = BitVec.ofNat 64 yl) (h11 : S.regs 11 = BitVec.ofNat 64 yc)
    (h12 : S.regs 12 = BitVec.ofNat 64 n) (hfw : Fw s S.mem zp zl zc yp n) (hv : natVal s.mem zp zl < 2 ^ n) :
    Goal impl R b L zp zl zc yp yl n s S := by
  have hzw : Outside zp (8 * zl) (win s K A) := by
    have := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h8 := hpre.2.2.2.2.2.2.2.2.1
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢
    omega
  refine k1 S zl L b hpre hpc hsp hab h0 h3 h1 h7 h6 h8 h9 h10 h11 h12 hfw (rt_stack hpre 1 hF hreg) ?_ ?_
    hpre.2.2.2.2.2.2.2.2.1
  · rw [natVal_frame hF hzw, Nat.mod_eq_of_lt hv]
  · exact natNorm_frame hF hzw hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- after `x = x.trunc(x, n)` returns (at `+0x105`): reload `y`, `n`, `z`, move the result to `RDI, RSI, R8`, `J1` -/
theorem s1t (impl : List Amd64.Segment) {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {s : State} (k1 : J1 impl R b L op zp zl zc yp yl yc n s) (hpre : Pre R b L op zp zl zc yp yl yc n s)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (M0 : Memory) (hrt0 : Rt R b L s zp zc n 0 M0 L b)
    (hfw0 : Fw s M0 zp zl zc yp n) (r72 : M0.readLE ((s.regs 4).toNat + 72) 8 = yl)
    (r80 : M0.readLE ((s.regs 4).toNat + 80) 8 = yc) (hv0 : natVal M0 zp zl = natVal s.mem zp zl)
    (S0 : State) (hS0 : S0.mem = M0) (hsp0 : (S0.regs 4).toNat = (s.regs 4).toNat - 136)
    (h140 : S0.regs 14 = s.regs 14) (hfs0 : S0.fsBase = s.fsBase) (hx0 : S0.xmm 15 = s.xmm 15)
    (hdf0 : S0.df = false)
    (s' : State) (hpc' : s'.rip = BitVec.ofNat 64 6216101) (hsp' : s'.regs 4 = S0.regs 4 + 8)
    (h14' : s'.regs 14 = S0.regs 14) (hx' : s'.xmm 15 = S0.xmm 15) (hreg' : s'.mem.regions = S0.mem.regions)
    (hpost : TruncPost R b L stkT aboveT zp zc zp zl n S0 s') :
    Goal impl R b L zp zl zc yp yl n s s' := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, -, hout, -, -, -, -, -⟩, -, -, -, -, -, -, -, hzl, -, hzc, -, -, -, -, -,
    hzw, -⟩ := id hpre
  obtain ⟨hfs, hdf, p', l', c', e0, e1, e2, L', b', ⟨hv, hnorm, hlc, -, hlive, hreuse, -⟩, -, ⟨hLE, hbud, hinv⟩, hF,
    hLF⟩ := hpost
  obtain ⟨rfl, rfl⟩ := hreuse (by unfold truncNeed; omega)
  simp only [win, hsp0] at hF
  simp only [win, K, A, regSP, outside_cons, outside_nil, and_true] at hzw hout hb' ha hw
  have hacc' : s'.mem.accessible ((s.regs 4).toNat - 4576) (4576 + 88) true = true := by
    rw [hF.accessible, hS0, hrt0.2.1.accessible]; exact hw
  have rd : ∀ a, (s.regs 4).toNat - 56 ≤ a → a + 8 ≤ (s.regs 4).toNat + 88 → s'.mem.readLE a 8 = M0.readLE a 8 := by
    intro a h1 h2
    rw [← hS0]
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega⟩
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfw0
  have hsp'' : s'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) := by
    rw [hsp']; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp0]; omega
  have q16 := (rd _ (by omega) (by omega)).trans f3
  have q24 := (rd _ (by omega) (by omega)).trans f4
  have q32 := (rd _ (by omega) (by omega)).trans f5
  have q64 := (rd _ (by omega) (by omega)).trans f6
  have q72 := (rd _ (by omega) (by omega)).trans r72
  have q80 := (rd _ (by omega) (by omega)).trans r80
  have q8 := (rd _ (by omega) (by omega)).trans f7
  have q0 := (rd _ (by omega) (by omega)).trans f1
  have qbp := (rd _ (by omega) (by omega)).trans f2
  have a16 : (s.regs 4).toNat - 128 + 144 = (s.regs 4).toNat + 16 := by omega
  have a24 : (s.regs 4).toNat - 128 + 152 = (s.regs 4).toNat + 24 := by omega
  have a32 : (s.regs 4).toNat - 128 + 160 = (s.regs 4).toNat + 32 := by omega
  have a64 : (s.regs 4).toNat - 128 + 192 = (s.regs 4).toNat + 64 := by omega
  have a72 : (s.regs 4).toNat - 128 + 200 = (s.regs 4).toNat + 72 := by omega
  have a80 : (s.regs 4).toNat - 128 + 208 = (s.regs 4).toNat + 80 := by omega
  have a8 : (s.regs 4).toNat - 128 + 136 = (s.regs 4).toNat + 8 := by omega
  unfold Goal
  janus64_run [hsp'', a16, a24, a32, a64, a72, a80, a8, q16, q24, q32, q64, q72, q80, q8] until [6216183]
  have hent := ent_of hpre
  refine k1 _ l' L' b' hpre ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hlc
  all_goals try janus64_simp
  all_goals first
    | exact hsp'.symm.trans hsp'' | (rw [h14', h140]) | (rw [hfs, hfs0]) | (rw [hx', hx0]) | (rw [hdf, hdf0])
    | exact ⟨q0, qbp, q16, q24, q32, q64, q8⟩
    | (rw [hS0] at hF hreg' hLF; rw [h140] at hinv
       exact rt_call hrt0 (by omega) hkT (by omega) (Or.inl rfl) hreg' hF hLF hLE hbud (truncNeed_le_w _ _) hinv hlive)
    | (rw [hv, hS0, hv0]) | exact hnorm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem s1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : TruncHyp impl R ns stkT aboveT)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 6215840)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h3 : s.regs 3 = BitVec.ofNat 64 zl) (h1 : s.regs 1 = BitVec.ofNat 64 zc)
    (h7 : s.regs 7 = BitVec.ofNat 64 zp) (h6 : s.regs 6 = BitVec.ofNat 64 zl) (h8 : s.regs 8 = BitVec.ofNat 64 zc)
    (h9 : s.regs 9 = BitVec.ofNat 64 yp) (h10 : s.regs 10 = BitVec.ofNat 64 yl) (h11 : s.regs 11 = BitVec.ofNat 64 yc)
    (hpre : Pre R b L op zp zl zc yp yl yc n s) (k1 : J1 impl R b L op zp zl zc yp yl yc n s) :
    Goal impl R b L zp zl zc yp yl n s s := by
  have hpre' := hpre
  obtain ⟨⟨⟨hgN, hgR, hgB⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -, -, -, -⟩, -, -, -, -, -, hn1, hn2, hzl, hW, hzc, hzl',
    hyl, hyc, hyl', hzlive, hzw, -⟩ := hpre'
  obtain ⟨hzf, hra, hn8, hx15, hdf⟩ := ent_of hpre
  simp only [W] at hW
  simp only [win, outside_cons, outside_nil, and_true] at hzw hout
  simp only [K, A, regG, regSP, stackguard0Offset, stackguard0] at hw hout hzw hgB hb' ha hga hgN hgR
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := (hzlive (by omega)).2.2.2
  have hza : s.mem.accessible zp (8 * zl) false = true :=
    Janus.Arm64.Memory.accessible_sub _ (hzlive (by omega)).2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega)
  unfold Goal
  by_cases hz0 : zl = 0
  · subst hz0
    have hmA : (BitVec.ofNat 64 0 + 18446744073709551615#64).msb = true := by decide
    have hmB : (BitVec.ofNat 64 0 - 1#64).msb = true := by decide
    have hmC : (18446744073709551615#64).msb = true := by decide
    janus64_run [hmA, hmB, hmC] until [6216183]
    refine j1_stack k1 hpre _ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [win, K, A]; janus_frame
    all_goals try janus64_simp
    all_goals first
      | exact Expmc.sp_sub _ _ (by omega) (by omega)
      | (simp only [Fw]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp)
      | exact Nat.lt_of_lt_of_le (natVal_lt _ _ _) (Nat.one_le_two_pow)
      | skip
  have e0 : (BitVec.ofNat 64 zl + 18446744073709551615#64).toNat = zl - 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have e0' : (BitVec.ofNat 64 zl - 1#64).toNat = zl - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hm0 : (BitVec.ofNat 64 zl + 18446744073709551615#64).msb = false := by
    rw [BitVec.msb_eq_decide, e0]; simp; omega
  have hm1 : (BitVec.ofNat 64 zl - 1#64).msb = false := by
    rw [BitVec.msb_eq_decide, e0']; simp; omega
  have e1 : (zp % 18446744073709551616 + (zl - 1) * 8) % 18446744073709551616 = zp + 8 * (zl - 1) := by omega
  janus64_run [hm0, hm1] until [6215891]
  janus64_run [e1] until [6215896]
  generalize hxd : BitVec.ofNat 64 (s.mem.readLE (zp + zl * 8 - 8) 8) = x
  janus64_run until [6215959]
  gen_reg 13 as t with hT
  have hts : t = BitLenA64.smearBV x := by rw [← hT, BitVec.or_comm]; rfl
  have hx0 : x.toNat ≠ 0 := by
    have hn := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rcases hn with h | h
    · omega
    · rw [← hxd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Util.readLE8_lt _ _),
        show zp + zl * 8 - 8 = zp + 8 * (zl - 1) by omega]; exact h
  have ht0 : t.toNat ≠ 0 := by rw [hts]; exact (BitLenA64.smearBV_log2 x hx0).1
  have ht0' : (t.toNat = 0) = False := by simp [ht0]
  janus64_run [ht0, ht0'] until [6215982]
  gen_reg 2 as bl with hBl
  have hbl : bl.toNat = 64 * (zl - 1) + Aux.bitLen (s.mem.readLE (zp + 8 * (zl - 1)) 8) := by
    rw [← hBl]
    refine BitLenA64.bl_exact64 _ _ _ (Util.readLE8_lt _ _) ?_ ?_ (by omega) (by omega)
    · intro h; apply hx0; rw [← hxd, BitVec.toNat_ofNat, show zp + zl * 8 - 8 = zp + 8 * (zl - 1) by omega, h]
    · rw [hts, BitLenA64.clz_smear, ← hxd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Util.readLE8_lt _ _),
        show zp + zl * 8 - 8 = zp + 8 * (zl - 1) by omega]
  by_cases hc : bl.toNat ≤ n
  · janus64_run [hc] until [6216183]
    refine j1_stack k1 hpre _ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [win, K, A]; janus_frame
    all_goals try janus64_simp
    all_goals first
      | exact Expmc.sp_sub _ _ (by omega) (by omega)
      | (simp only [Fw]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp)
      | (refine Nat.lt_of_lt_of_le (BitLenA64.natVal_lt_bl _ _ _ (by omega)) (Nat.pow_le_pow_right (by omega) ?_)
         omega)
      | skip
  · have a8 : (s.regs 4).toNat - 128 + 136 = (s.regs 4).toNat + 8 := by omega
    have hcz : (zc = 0) = False := by simp; omega
    janus64_run [hc, a8, hn8, hcz] until [6188320]
    have hzw' : Outside zp (8 * zl) (win s K A) := by simp only [win, K, A, outside_cons, outside_nil, and_true]; omega
    have hzh : Held R L zp (8 * zl) := (hzlive (by omega)).2.1.sub (Nat.le_refl _) (by omega)
    refine truncCall hap hns htr (zp := zp) (zl := zl) (zc := zc) (x := zp) (xl := zl) (xc := zc) (n := n)
      (ra := 6216101) (ra_of hap hnf 0x105 (by omega)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (truncPre_of hpre (rt_stack hpre 0 ?_ ?_) (by omega) rfl ?_ ?_ ?_ hkT haT (Or.inl ⟨rfl, rfl⟩) hzl (by omega) ?_
        (by omega) hzh (by omega) (by omega) (Or.inl rfl))
      fun s' hpc' hsp' h14' hx' hreg' hpost => ?qK
    case qK =>
      refine s1t impl k1 hpre hkT haT _ (rt_stack hpre 0 ?_ ?_) ?_ ?_ ?_ ?_ _ rfl ?_ ?_ ?_ ?_ ?_ s' hpc' hsp' h14' hx'
        hreg' hpost
      · simp only [win, K, A]; janus_frame
      · janus64_simp
      · simp only [Fw]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> janus64_simp
      · janus64_simp <;> omega
      · janus64_simp <;> omega
      · exact natVal_frame (by simp only [win, K, A]; janus_frame) hzw'
      · janus64_simp <;> omega
      · janus64_simp
      · janus64_simp
      · janus64_simp
      · janus64_simp <;> exact hdf
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp
    · janus64_simp <;> exact hx15
    · janus64_simp <;> exact hdf
    · simp only [win, K, A]; janus_frame
    · janus64_simp
    · janus64_simp <;> omega
    · janus64_simp
    · janus64_simp
    · janus64_simp <;> exact hza

end FvModexp.Amd64.SubMod2N
