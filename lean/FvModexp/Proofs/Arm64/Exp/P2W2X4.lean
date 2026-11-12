import FvModexp.Proofs.Arm64.Exp.P2W2X3
import FvModexp.Proofs.Arm64.Exp.P2W2LO

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the loop exit (`KI 0 0`, agent infra)

At `LT` with no window and no word left: the test's stores `280/112`, `TBZ` (not taken), `CBZ i` (taken) →
`0x1b69dc`: `TBNZ $0, kk - 2` (nat.go:1259): `kk` odd ⇔ `u` (`z` is U-class) → `norm` + tail (`nmT`); `kk` even
(`z` is `zz`'s stack buffer) → `z.set(zz)` into the U-class `zz` (`cap ≥ n`: reuse → `xJ`; else `make` →
`xA1`/`xA2`). The value is `outerLoop … 0 yi 0 Z = Z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

open FvModexp.Arm64.ExpHyp

theorem bit0_kk (kk : Nat) :
    (BitVec.ofNat 64 kk - 2#64).getLsbD 0 = decide (kk % 2 = 1) := by
  simp only [BitVec.getLsbD, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.testBit_zero]
  congr 1; apply propext; omega

section
variable {impl : List Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat}
    {s : State} {r29 : BitVec 64} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} {zzp bp kk cst FV : Nat}


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the exit's reuse path (`n ≤ cap zz`), from the join -/
theorem xEvR (hap : ImplApart Extracted.program impl)
    (hmv : MemmoveLive (LibExp.program.link impl) P2Pre.mvE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hr4 : (s.regs 30).toNat % 4 = 0)
    (hr48 : (s.regs 30).toNat < 2 ^ 48) {M0 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hBF : BF R L K g sp st zp zc xp xl xc yp yl lm (s.regs 30).toNat s M0 L1 b1 zzp bp) {pA lA cA pB cB Z : Nat}
    (hA : BC R L K g sp st zp zc M0 L1 zzp bp lm false pA cA) (hAn : NV M0 pA lA cA Z)
    (hB : BC R L K g sp st zp zc M0 L1 zzp bp lm true pB cB) (hcB0 : 0 < cB) (hnd : lA ≤ cB)
    (hbud : b - cst ≤ b1)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 xJE) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h18 : T.regs 18 = s.regs 18)
    (hF : MemFrame M0 T.mem [(sp + 280, sp + 280 + 8), (sp + 112, sp + 112 + 8)]) (hrg : T.mem.regions = M0.regions)
    (h0 : T.regs 0 = BitVec.ofNat 64 pB) (h1 : T.regs 1 = BitVec.ofNat 64 lA) (h15 : T.regs 15 = BitVec.ofNat 64 cB)
    (h2 : T.regs 2 = BitVec.ofNat 64 lA) (h3 : T.regs 3 = BitVec.ofNat 64 pA) :
    ReachesRet (LibExp.program.link impl) (s.regs 30) T (FQ R b L K zp zc st Z cst s) := by
  have hlA := len_pos hAn.2.1 hAn.2.2.2
  obtain ⟨hB', -, hkeep⟩ := BF.win hP hBF hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [SW] <;> omega)
  obtain ⟨e1, e2⟩ := hA
  rw [e1, e2] at hAn
  obtain ⟨-, hAk⟩ := hkeep false zzp (2 * W lm) ⟨rfl, rfl⟩ (by have := hAn.1; omega)
  obtain ⟨hB2, -⟩ := hkeep true pB cB hB hcB0
  exact xJ hap hmv hP hB'.wc hB'.esl hr4 hr48 hB'.tz hB2 hnd hlA (NV.keep hAn hAk) hbud T hpc hsp h28 h18 rfl h0
    h1 h15 h2 (e1 ▸ h3)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the exit's `make(nat, n, n + 4)` path, from the `makeslice` call -/
theorem xEv2 (hap : ImplApart Extracted.program impl)
    (hmv : MemmoveLive (LibExp.program.link impl) P2Pre.mvE 4096 R)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hr4 : (s.regs 30).toNat % 4 = 0)
    (hr48 : (s.regs 30).toNat < 2 ^ 48) {M0 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hBF : BF R L K g sp st zp zc xp xl xc yp yl lm (s.regs 30).toNat s M0 L1 b1 zzp bp) {pA lA cA Z : Nat}
    (hA : BC R L K g sp st zp zc M0 L1 zzp bp lm false pA cA) (hAn : NV M0 pA lA cA Z) (hla : lA ≤ W lm)
    (hbud : b + P2Pre.tC lm ≤ b1 + cst) (hcb : cst ≤ b)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 mkE) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h18 : T.regs 18 = s.regs 18)
    (hF : MemFrame M0 T.mem [(sp + 280, sp + 280 + 8), (sp + 112, sp + 112 + 8), (sp + 96, sp + 96 + 8)])
    (hrg : T.mem.regions = M0.regions)
    (r112 : T.mem.readLE (sp + 112) 8 = lA) (r280 : T.mem.readLE (sp + 280) 8 = pA)
    (r96 : T.mem.readLE (sp + 96) 8 = lA + 4)
    (h0 : T.regs 0 = 2641088#64) (h1 : T.regs 1 = BitVec.ofNat 64 lA) (h2 : T.regs 2 = BitVec.ofNat 64 (lA + 4))
    (h30 : T.regs 30 = BitVec.ofNat 64 1796664) :
    ReachesRet (LibExp.program.link impl) (s.regs 30) T (FQ R b L K zp zc st Z cst s) := by
  have hlA := len_pos hAn.2.1 hAn.2.2.2
  obtain ⟨hB', -, hkeep⟩ := BF.win hP hBF hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [SW] <;> omega)
  obtain ⟨e1, e2⟩ := hA
  rw [e1, e2] at hAn
  obtain ⟨-, hAk⟩ := hkeep false zzp (2 * W lm) ⟨rfl, rfl⟩ (by have := hAn.1; omega)
  exact xA2 hap hmv hmk hP hB' hr4 hr48 hlA hla (NV.keep hAn hAk) r112 (e1 ▸ r280) r96 hbud hcb T hpc hsp h28 h18 rfl h0 h1
    h2 h30

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the exit with an even number of swaps: `z` is U-class, straight to `norm` -/
theorem xOd (hap : ImplApart Extracted.program impl)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hr4 : (s.regs 30).toNat % 4 = 0)
    (hr48 : (s.regs 30).toNat < 2 ^ 48) {M0 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hBF : BF R L K g sp st zp zc xp xl xc yp yl lm (s.regs 30).toNat s M0 L1 b1 zzp bp) {pA lA cA Z : Nat}
    (hA : BC R L K g sp st zp zc M0 L1 zzp bp lm true pA cA) (hAn : NV M0 pA lA cA Z) (hbud : b - cst ≤ b1)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 nmE) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h18 : T.regs 18 = s.regs 18)
    (hF : MemFrame M0 T.mem [(sp + 280, sp + 280 + 8), (sp + 112, sp + 112 + 8)]) (hrg : T.mem.regions = M0.regions)
    (h0 : T.regs 0 = BitVec.ofNat 64 pA) (h1 : T.regs 1 = BitVec.ofNat 64 lA)
    (h15 : T.regs 15 = BitVec.ofNat 64 cA) :
    ReachesRet (LibExp.program.link impl) (s.regs 30) T (FQ R b L K zp zc st Z cst s) := by
  have hlA := len_pos hAn.2.1 hAn.2.2.2
  obtain ⟨hB', -, hkeep⟩ := BF.win hP hBF hF hrg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [SW] <;> omega)
  obtain ⟨hA2, hAk⟩ := hkeep true pA cA hA (by have := hAn.1; omega)
  exact nmT hap hP hB'.wc hB'.esl hr4 hr48 hA2 (NV.keep hAn hAk) hbud T hpc hsp h28 h18 rfl h0 h1 h15

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the loop exit** (premise `hexit` of `loopKL`) -/
theorem exitKI (hap : ImplApart Extracted.program impl)
    (hmv : MemmoveLive (LibExp.program.link impl) P2Pre.mvE 4096 R)
    (hmk : MakesliceLiveContract (LibExp.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s) (hr4 : (s.regs 30).toNat % 4 = 0)
    (hr48 : (s.regs 30).toNat < 2 ^ 48) (hcb : cst ≤ b) :
    KI impl (s.regs 30) (FQ R b L K zp zc st FV cst s) R b L K g sp st zp zc xp xl xc yp yl lm (s.regs 30).toNat s r29
      sqC mlC zzp bp kk cst FV 0 0 := by
  intro S M L1 b1 yi Z pA lA cA pB lB cB u h
  have hZ : Z = FV := by have := h.hfv; simp only [Exp.outerLoop, Exp.wordLoop] at this; exact this
  subst hZ
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.1
  have hW128 : W lm ≤ 128 := by simp only [W]; omega
  have hmacc : M.accessible (sp - K) (K + 560) true = true := by
    rw [h.li.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hb := h.hb
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hb
  have hbud : b - cst ≤ b1 := by omega
  have hlA := len_pos h.li.va h.li.zo
  have hlac := h.li.lac
  have hla := h.li.la
  have hcB0 := h.li.cb0
  have hlbc := h.li.lbc
  have hBF : BF R L K g sp st zp zc xp xl xc yp yl lm (s.regs 30).toNat s M L1 b1 zzp bp := ⟨h.li.wc, h.li.esl, h.li.tz⟩
  have hcA : 0 < cA := by omega
  have hAf := BC.facts hP hBF h.li.ca hcA
  have hA40 := hAf.1
  have hA48 := (hAf.2.1 hcA).2.2.2
  have hBf := BC.facts hP hBF h.li.cb hcB0
  have hB40 := hBf.1
  have hB48 := (hBf.2.1 hcB0).2.2.2
  have hu := h.hu
  have h' := h
  obtain ⟨epc, esp, e28, e29, e18, em, e3, e1, e14, e0, e13, e15, e8, e7, e4, e9, e10, e11, e12, e2, -, -, -, -, -,
    -, -⟩ := h
  subst em
  cases u
  · -- `kk` even: `z.set(zz)`
    have hk : ¬ kk % 2 = 1 := by simp at hu; omega
    have hbit : (BitVec.ofNat 64 kk - 2#64).getLsbD 0 = false := by rw [bit0_kk]; exact decide_eq_false hk
    have t1 := toInt_small lA (by omega)
    have t2 := toInt_small cB (by omega)
    janus_run [m1_63, hbit, hmacc, t1, t2] until [xJE, mkE]
    · -- `make(nat, n, n + 4)` (`n = 1` is refuted: `cap zz ≥ 1`)
      have e4 : BitVec.ofNat 64 lA + 4#64 = BitVec.ofNat 64 (lA + 4) := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      refine xEv2 hap hmv hmk hP hr4 hr48 hBF h'.li.ca ⟨hlac, h'.li.va, h'.li.na, h'.li.zo⟩ hla hb hcb _ ?_ ?_ ?_ ?_
        ?hF ?hrg ?_ ?_ ?_ ?_ ?_ ?_ ?_
      case hF => janus_frame
      case hrg => simp only [Memory.regions_writeLE]
      all_goals (janus_simp [e4] <;> omega)
    · -- reuse
      refine xEvR hap hmv hP hr4 hr48 hBF h'.li.ca ⟨hlac, h'.li.va, h'.li.na, h'.li.zo⟩ h'.li.cb hcB0 (by omega) hbud
        _ ?_ ?_ ?_ ?_ ?hF ?hrg ?_ ?_ ?_ ?_ ?_
      case hF => janus_frame
      case hrg => simp only [Memory.regions_writeLE]
      all_goals (janus_simp <;> omega)
  · -- `kk` odd: `z` is U-class
    have hk : kk % 2 = 1 := by simp at hu; omega
    have hbit : (BitVec.ofNat 64 kk - 2#64).getLsbD 0 = true := by rw [bit0_kk]; exact decide_eq_true hk
    janus_run [m1_63, hbit, hmacc] until [nmE]
    refine xOd hap hP hr4 hr48 hBF h'.li.ca ⟨hlac, h'.li.va, h'.li.na, h'.li.zo⟩ hbud _ ?_ ?_ ?_ ?_ ?hF ?hrg ?_ ?_ ?_
    case hF => janus_frame
    case hrg => simp only [Memory.regions_writeLE]
    all_goals (janus_simp <;> omega)

end

end FvModexp.Arm64.P2W2
