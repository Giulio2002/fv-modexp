import FvModexp.Proofs.Amd64.Exp.P2W2X3
import FvModexp.Proofs.Amd64.Exp.P2W2LK

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize2` (amd64): the loop exit `KI 0 0` (agent divmc s74; amd64 twin of agent infra's
`Arm64.P2W2X4`)

From `LT` with `c = 0`, `i = 0`: the stores `[0x118] := R9`, `[0x68] := SI`, `TESTQ R10` (`-1`: no body), `TESTQ R11`
(`0`: no outer step) → fn+0x805: `BTL $0, [0xc0]` (`kk - 2`, i.e. the parity of `kk`; nat.go:1259):
* `kk` odd (`u = true`, `z` U-class): `R15 := R12`, `R8 := R9` → `nH` (`nmT`);
* `kk` even (`u = false`, `z` = `zz`'s stack buffer): `z.set(zz)` into the U-class `zz` buffer: `n ≤ cap` → reuse
  (`AX := SI`, the join `xJ`), else `make(nat, n, n + 4)` (`xA2`; `n = 1` is refuted: `cap ≥ 1`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2

open FvModexp.Amd64.ExpHyp

/-- (copy of agent asm's `P2D.bit0_iff`, Amd64/Exp/P2DEnt, without its import) -/
theorem bit0W (v : Nat) : (BitVec.setWidth 32 (BitVec.ofNat 64 v)).getLsbD 0 = true ↔ v % 2 = 1 := by
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit_zero]; simp

theorem bit0W' (v : Nat) : ¬(BitVec.setWidth 32 (BitVec.ofNat 64 v)).getLsbD 0 = true ↔ v % 2 = 0 := by
  rw [bit0W]; omega

section
variable {impl : List Amd64.Segment} {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State} {r5 : W64} {zzp tp kk cst FV : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the exit with `kk` odd: `z` is U-class, straight to `norm` -/
theorem xOd (hap : Amd64.ImplApart Extracted.program impl)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M0 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hBF : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M0 L1 b1 zzp tp) {pA lA cA Z : Nat}
    (hA : BC R L K g sp st zp zc M0 L1 zzp tp lm true pA cA) (hlac : lA ≤ cA) (hcA : 0 < cA)
    (hv : natVal M0 pA lA = Z) (hbud : b - cst ≤ b1)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 nH) (hsp : T.regs 4 = BitVec.ofNat 64 sp)
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0) (hdf : T.df = false)
    (hF : MemFrame M0 T.mem [(sp + 0x118, sp + 0x118 + 8), (sp + 0x68, sp + 0x68 + 8)])
    (hrg : T.mem.regions = M0.regions)
    (h8 : T.regs 8 = BitVec.ofNat 64 pA) (h6 : T.regs 6 = BitVec.ofNat 64 lA)
    (h15 : T.regs 15 = BitVec.ofNat 64 cA) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) T (FQ R b L K zp zc st Z cst s) := by
  obtain ⟨hB', -, hkeep⟩ := BF.win hP hBF hF hrg (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp only [SW] <;> omega)
  obtain ⟨hA2, hAk⟩ := hkeep true pA cA hA hcA
  have hv2 : natVal T.mem pA lA = Z := by
    show T.mem.readLE pA (8 * lA) = Z
    rw [hAk _ _ (Nat.le_refl _) (by omega)]; exact hv
  exact nmT hap hP hB'.wc hB'.esl hA2 hlac hv2 hbud T hpc hsp h14 hfs hx15 hdf rfl h8 h6 h15

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the exit's reuse path (`n ≤ cap zz`), from the join -/
theorem xEvR (hap : Amd64.ImplApart Extracted.program impl)
    (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M0 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hBF : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M0 L1 b1 zzp tp) {pA lA cA pB cB Z : Nat}
    (hA : BC R L K g sp st zp zc M0 L1 zzp tp lm false pA cA) (hla : lA ≤ W lm) (hlA : 0 < lA)
    (hv : natVal M0 pA lA = Z)
    (hB : BC R L K g sp st zp zc M0 L1 zzp tp lm true pB cB) (hcB0 : 0 < cB) (hnd : lA ≤ cB)
    (hbud : b - cst ≤ b1)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 XJ) (hsp : T.regs 4 = BitVec.ofNat 64 sp)
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0) (hdf : T.df = false)
    (hF : MemFrame M0 T.mem [(sp + 0x118, sp + 0x118 + 8), (sp + 0x68, sp + 0x68 + 8)])
    (hrg : T.mem.regions = M0.regions)
    (h8 : T.regs 8 = BitVec.ofNat 64 pB) (h9 : T.regs 9 = BitVec.ofNat 64 pA) (h6 : T.regs 6 = BitVec.ofNat 64 lA)
    (h0 : T.regs 0 = BitVec.ofNat 64 lA) (h15 : T.regs 15 = BitVec.ofNat 64 cB) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) T (FQ R b L K zp zc st Z cst s) := by
  obtain ⟨hB', -, hkeep⟩ := BF.win hP hBF hF hrg (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp only [SW] <;> omega)
  have hlm2 := hP.2.2.2.2.1
  obtain ⟨e1, -⟩ := hA
  rw [e1] at hv h9
  obtain ⟨-, hAk⟩ := hkeep false zzp (2 * W lm) ⟨rfl, rfl⟩ (by simp only [W]; omega)
  obtain ⟨hB2, -⟩ := hkeep true pB cB hB hcB0
  have hv2 : natVal T.mem zzp lA = Z := by
    show T.mem.readLE zzp (8 * lA) = Z
    rw [hAk _ _ (Nat.le_refl _) (by omega)]; exact hv
  exact xJ hap hmv hP hB'.wc hB'.esl hB'.tz hB2 hnd hlA (by omega) hv2 hbud T hpc hsp h14 hfs hx15 hdf rfl h8 h9 h6
    h0 h15

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the exit's `make(nat, n, n + 4)` path, from the `makeslice` call -/
theorem xEv2 (hap : Amd64.ImplApart Extracted.program impl)
    (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M0 : Memory} {L1 : List (Nat × Nat)} {b1 : Nat}
    (hBF : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M0 L1 b1 zzp tp) {pA lA cA Z : Nat}
    (hA : BC R L K g sp st zp zc M0 L1 zzp tp lm false pA cA) (hla : lA ≤ W lm) (hlA : 0 < lA)
    (hv : natVal M0 pA lA = Z) (hbud : b + P2Pre.tC lm ≤ b1 + cst) (hcb : cst ≤ b)
    {M1 : Memory} (hF : MemFrame M0 M1 [(sp + 0x118, sp + 0x118 + 8), (sp + 0x68, sp + 0x68 + 8),
      (sp + 0x58, sp + 0x58 + 8)]) (hrg : M1.regions = M0.regions)
    (r118 : M1.readLE (sp + 0x118) 8 = pA) (r68 : M1.readLE (sp + 0x68) 8 = lA)
    (r58 : M1.readLE (sp + 0x58) 8 = lA + 4)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 mkE) (hsp : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = BitVec.ofNat 64 g) (hfs : T.fsBase = s.fsBase) (hx15 : T.xmm 15 = 0) (hdf : T.df = false)
    (hm : T.mem = M1.writeLE (sp - 8) 8 6203025)
    (h0 : T.regs 0 = BitVec.ofNat 64 7233184) (h3 : T.regs 3 = BitVec.ofNat 64 lA)
    (h1 : T.regs 1 = BitVec.ofNat 64 (lA + 4)) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) T (FQ R b L K zp zc st Z cst s) := by
  obtain ⟨hB1, -, hkeep⟩ := BF.win hP hBF hF hrg (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp only [SW] <;> omega)
  have hlm2 := hP.2.2.2.2.1
  obtain ⟨e1, -⟩ := hA
  rw [e1] at hv r118
  obtain ⟨-, hAk⟩ := hkeep false zzp (2 * W lm) ⟨rfl, rfl⟩ (by simp only [W]; omega)
  obtain ⟨hB2, hrd2, hkeep2⟩ := BF.push hP hB1 6203025
  obtain ⟨-, hAk2⟩ := hkeep2 false zzp (2 * W lm) ⟨rfl, rfl⟩ (by simp only [W]; omega)
  have hv2 : natVal (M1.writeLE (sp - 8) 8 6203025) zzp lA = Z := by
    show (M1.writeLE (sp - 8) 8 6203025).readLE zzp (8 * lA) = Z
    rw [hAk2 _ _ (Nat.le_refl _) (by omega), hAk _ _ (Nat.le_refl _) (by omega)]; exact hv
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  exact xA2 hap hmv hmk hP hB2 hlA hla hv2 ((hrd2 _ _ (by omega)).trans r118) ((hrd2 _ _ (by omega)).trans r68)
    ((hrd2 _ _ (by omega)).trans r58) (Janus.Arm64.Memory.readLE_writeLE_self ..) hbud hcb
    T hpc hsp h14 hfs hx15 hdf hm h0 h3 h1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **the loop exit** (premise `hexit` of `loopKL`) -/
theorem exitKI (hap : Amd64.ImplApart Extracted.program impl)
    (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hcb : cst ≤ b) :
    KI impl (BitVec.ofNat 64 r) (FQ R b L K zp zc st FV cst s) R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5
      zzp tp kk cst FV 0 0 := by
  intro S M L1 b1 yi Z pA lA cA pB lB cB u h
  have hZ : Z = FV := by have := h.hfv; simp only [Exp.outerLoop, Exp.wordLoop] at this; exact this
  subst hZ
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 8 := hP.cenv0.2.1
  have hlm := hP.2.2.2.2.2.1
  have hW128 : W lm ≤ 128 := by simp only [W]; omega
  have hb := h.hb
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hb
  have hbud : b - cst ≤ b1 := by omega
  have hlA := len_pos h.li.va h.li.zo
  have hlac := h.li.lac
  have hla := h.li.la
  have hcB0 := h.li.cb0
  have hva := h.li.va
  have hBF : BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp := ⟨h.li.wc, h.li.esl, h.li.tz⟩
  have hcA : 0 < cA := by omega
  have hA40 := (BC.facts hP hBF h.li.ca hcA).1
  have hB40 := (BC.facts hP hBF h.li.cb hcB0).1
  have hpA := ((BC.facts hP hBF h.li.ca hcA).2.1 hcA).2.2.2
  have hwacc : M.accessible (sp - 8 - K) (K + 0x238) true = true := (h.li.wc.cenv hP).2.2.2.1
  have hwaccF : M.accessible (sp - 8 - K) (K + 0x238) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have r0c0 := h.li.sc0
  have hu := h.hu
  have hcaH : HdM (BC R L K g sp st zp zc M L1 zzp tp lm u pA cA) := ⟨h.li.ca⟩
  have hcbH : HdM (BC R L K g sp st zp zc M L1 zzp tp lm (!u) pB cB) := ⟨h.li.cb⟩
  have hBH : HdM (BF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) := ⟨hBF⟩
  have hm1 : (BitVec.ofNat 64 0 - 1#64).msb = true := by decide
  have hm2 : (18446744073709551615#64).msb = true := by decide
  obtain ⟨epc, esp, e14, e5, efs, ex, edf, em, e9, e6, e12, e8, e1, e15, e3, e10, e13, e7, e11, e2, e0, -, -, -, -,
    -, -, -⟩ := h
  clear hBF
  subst em
  have t1 : (BitVec.ofNat 64 lA).toInt = (lA : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have t2 : (BitVec.ofNat 64 cB).toInt = (cB : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  janus64_run [hm1, hm2, r0c0, hwacc, hwaccF, t1, t2] until [XJ, mkE, nH]
  · -- `kk` odd
    have hk := (bit0W _).1 (by janus_assumption)
    have hu1 : u = true := hu.2 (by omega)
    subst hu1
    refine xOd hap hP hBH.h hcaH.h hlac hcA hva hbud _ ?_ ?_ ?_ ?_ ?_ ?_ ?hF ?hrg ?_ ?_ ?_
    case hF => janus_frame
    case hrg => simp only [Janus.Arm64.Memory.regions_writeLE]
    all_goals first | exact efs | (janus64_simp; done)
  · -- `kk` even, `make`
    have hk := (bit0W' _).1 (by janus_assumption)
    have hu1 : u = false := by cases u <;> simp_all <;> omega
    subst hu1
    have e4 : BitVec.ofNat 64 lA + 4#64 = BitVec.ofNat 64 (lA + 4) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have es8 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    refine xEv2 hap hmv hmk hP hBH.h hcaH.h hla hlA hva hb hcb ?hF ?hrg ?r1 ?r2 ?r3 _ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
    case hF => janus_frame
    case hrg => simp only [Janus.Arm64.Memory.regions_writeLE]
    case r1 =>
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
    case r2 =>
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
    case r3 => rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega
    all_goals first | exact efs | (janus64_simp [e4, es8]; done)
  · -- `kk` even, reuse
    have hk := (bit0W' _).1 (by janus_assumption)
    have hu1 : u = false := by cases u <;> simp_all <;> omega
    subst hu1
    refine xEvR hap hmv hP hBH.h hcaH.h hla hlA hva hcbH.h hcB0 (by omega) hbud _ ?_ ?_ ?_ ?_ ?_ ?_ ?hF ?hrg ?_
      ?_ ?_ ?_ ?_
    case hF => janus_frame
    case hrg => simp only [Janus.Arm64.Memory.regions_writeLE]
    all_goals first | exact efs | (janus64_simp; done)

end

end FvModexp.Amd64.P2W2
