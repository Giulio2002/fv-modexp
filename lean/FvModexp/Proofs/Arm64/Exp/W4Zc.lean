import FvModexp.Proofs.Arm64.Exp.W4PowAll
import FvModexp.Proofs.Common.BitLenA64
import FvModexp.Proofs.Common.GenReg

/-!
# window-4 prologue (arm64): `zz.make(2n)`, the first window, `copy(z, powers[yi>>4k])` (nat.go:1427-1446)

From `zj` (fn+0x774, the join after `z = z.make(2n)`: X0 = z, X14 = cap z) to the loop test (fn+0xaa0).
`zz` (the `lsh` result, cap ≥ 2n+1) is reused; `bitLen(y[len-1])` by smear + `CLZ` (Common/BitLenA64);
`k = (bitLen+3)/4 - 1`, `copy(z, powers[yi >> 4k])` (memmove), `yi <<= 64 - 4k`, `k--`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- the join after `z = z.make(2n)` (`CMP R14, R13`, fn+0x774) -/
abbrev zj : Nat := 1800420
/-- the loop test literal (`W4Loop.test`) -/
abbrev testL : Nat := 1801232

/-- the frame words `zj → test` writes besides `z[0:n]` and `R.rt` (memmove's window, spills) -/
@[reducible] def cw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4096, sp - 8), (sp + 8, sp + 32), (sp + 144, sp + 152), (sp + 184, sp + 192), (sp + 232, sp + 248),
    (sp + 296, sp + 304), (sp + 328, sp + 336), (sp + 368, sp + 376), (sp + 872, sp + 880)]

/-- the index of the most significant non-zero window of the top word (`k`, nat.go:1438) -/
abbrev kTop (yi : Nat) : Nat := (Exp.bitLen yi + 3) / 4 - 1

theorem lsr2 (x : BitVec 64) :
    x.rotateRight 2 &&& 18446744073709551615#64 &&& 4611686018427387903#64 = x >>> 2 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (4611686018427387903#64)[i] = decide (i < 62) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_ushiftRight, c1 i hi, c2 i hi]
  by_cases h : i < 62
  · simp [h]; rw [BitVec.getLsbD_eq_getElem (by omega)]
  · simp [h]; exact BitVec.getLsbD_of_ge x _ (by omega)

theorem lsl2 (x : BitVec 64) :
    x.rotateRight 62 &&& 18446744073709551612#64 &&& 18446744073709551615#64 = x <<< 2 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551612#64)[i] = decide (2 ≤ i) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_shiftLeft, c1 i hi, c2 i hi]
  by_cases h : i < 2
  · simp [h]
  · simp [h]; omega

theorem lsl3 (x : BitVec 64) :
    x.rotateRight 61 &&& 18446744073709551608#64 &&& 18446744073709551615#64 = x <<< 3 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551608#64)[i] = decide (3 ≤ i) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_shiftLeft, c1 i hi, c2 i hi]
  by_cases h : i < 3
  · simp [h]
  · simp [h]; omega

theorem e8n (n : Nat) (hn : n ≤ 2 ^ 16) : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem bitLen_pos (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) : 1 ≤ Exp.bitLen yi ∧ Exp.bitLen yi ≤ 64 := by
  unfold Exp.bitLen
  rw [if_neg (by omega)]
  have := Nat.log2_lt (show yi ≠ 0 by omega) |>.2 h
  omega

theorem e21 (bl : BitVec 64) (yi : Nat) (hb : bl.toNat = Exp.bitLen yi) (h0 : 0 < yi) (h : yi < 2 ^ 64) :
    (bl + 3#64) >>> 2 = BitVec.ofNat 64 (kTop yi + 1) := by
  have := bitLen_pos yi h0 h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, hb, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kTop,
    Nat.reducePow]
  omega

theorem kTop_le (yi : Nat) (h0 : 0 < yi) (h : yi < 2 ^ 64) : kTop yi ≤ 15 ∧ yi / 2 ^ (kTop yi * 4) < 16 := by
  have hb := bitLen_pos yi h0 h
  refine ⟨by unfold kTop; omega, ?_⟩
  have h1 : yi < 2 ^ Exp.bitLen yi := by
    unfold Exp.bitLen; rw [if_neg (by omega)]; exact Nat.lt_log2_self
  have h2 : 2 ^ Exp.bitLen yi ≤ 2 ^ (kTop yi * 4) * 16 := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by omega) (by unfold kTop; omega)
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [Nat.mul_comm]; omega)

theorem e23 (k : Nat) (hk : k ≤ 15) : BitVec.ofNat 64 k <<< 2 = BitVec.ofNat 64 (k * 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem ed (yi k : Nat) (h : yi < 2 ^ 64) :
    BitVec.ofNat 64 yi >>> (k * 4) = BitVec.ofNat 64 (yi / 2 ^ (k * 4)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
theorem zcopy (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibExp.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen bp zp zc zzp zzc : Nat) (tbl : Nat → Nat) (M : Memory)
    (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hz : Buf R L g sp n M zp zc) (hzzc : 2 * n ≤ zzc)
    (hzzc' : zzc < 2 ^ 40) (hy : Inp R L sp ylen M yp) (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40)
    (hyi : 0 < M.readLE (yp + 8 * (ylen - 1)) 8)
    (hent : ∀ d, d < 16 → Ent sp n bp tbl M d) (hbuf : ∀ d, d < 16 → Inp R L sp n M (bp + 8 * (d * n)))
    (hzb : ∀ d, d < 16 → Apart zp (8 * zc) (bp + 8 * (d * n)) (8 * n))
    (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (r1000 : M.readLE (sp + 1000) 8 = ylen) (r992 : M.readLE (sp + 992) 8 = yp)
    (r1024 : M.readLE (sp + 1024) 8 = n) (r224 : M.readLE (sp + 224) 8 = k0) (r1016 : M.readLE (sp + 1016) 8 = mp)
    (r1032 : M.readLE (sp + 1032) 8 = mc)
    (hok : ∀ d, R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, d, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 zj) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h13 : S.regs 13 = BitVec.ofNat 64 n) (h14 : S.regs 14 = BitVec.ofNat 64 zc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KT : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 testL → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 13 = BitVec.ofNat 64 n → S'.regs 14 = BitVec.ofNat 64 zc →
      S'.regs 1 = BitVec.ofNat 64 zzp → S'.regs 3 = BitVec.ofNat 64 n → S'.regs 15 = BitVec.ofNat 64 zzc →
      S'.regs 2 = BitVec.ofNat 64 n → S'.regs 9 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 mc →
      S'.regs 12 = BitVec.ofNat 64 k0 → S'.regs 16 = BitVec.ofNat 64 ylen →
      S'.regs 17 = BitVec.ofNat 64 (ylen - 1) → S'.regs 19 = BitVec.ofNat 64 yp →
      S'.regs 20 = BitVec.ofNat 64 ((M.readLE (yp + 8 * (ylen - 1)) 8 * 2 ^ (64 - kTop (M.readLE (yp + 8 * (ylen - 1)) 8) * 4)) % 2 ^ 64) →
      S'.regs 21 = BitVec.ofNat 64 (kTop (M.readLE (yp + 8 * (ylen - 1)) 8)) - 1#64 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      MemFrame M M' (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) → LiveFrame M M' L [(zp, zp + 8 * n)] →
      R.inv b L g (view R.rt L M') → M'.regions = M.regions →
      M'.readLE zp (8 * n) = tbl (M.readLE (yp + 8 * (ylen - 1)) 8 / 2 ^ (kTop (M.readLE (yp + 8 * (ylen - 1)) 8) * 4)) →
      M'.readLE (sp + 240) 8 = ylen - 1 →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := hz
  have hya := hy.1
  generalize hY : M.readLE (yp + 8 * (ylen - 1)) 8 = yi at hyi KT
  have e17 : BitVec.ofNat 64 ylen - 1#64 = BitVec.ofNat 64 (ylen - 1) := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  have hyw := hy.2.2.2
  unfold Apart at hyw
  have ry : ((M.writeLE (sp + 144) 8 zc).writeLE (sp + 368) 8 zp).readLE (yp + (ylen - 1) * 8) 8 = yi := by
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [← hY, Nat.mul_comm]
  have hyi64 : yi < 2 ^ 64 := by rw [← hY]; exact Util.readLE8_lt _ _
  janus_run [r168, r400, r1000, r992, r1024, r224, r1016, r1032, e17, ry] until [1800548]
  gen_reg 21 as t with hT
  janus_run until [1800560]
  gen_reg 21 as bl with hBl
  have hbl : bl.toNat = Exp.bitLen yi := by
    rw [← hBl, ← hT, ← BitLenA64.smearBV, BitLenA64.clz_smear, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hyi64]
    have hc := Util.clz_bl 64 yi hyi64
    have hb : Aux.bitLen yi = Exp.bitLen yi := rfl
    generalize Janus.Arm64.clzNat 64 yi = c at hc ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have hk := e21 bl yi hbl hyi hyi64
  have hkb := bitLen_pos yi hyi hyi64
  have e22 : BitVec.ofNat 64 (kTop yi + 1) - 1#64 = BitVec.ofNat 64 (kTop yi) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, kTop]; omega
  obtain ⟨hk15, hd16⟩ := kTop_le yi hyi hyi64
  have h63 : (BitVec.ofNat 64 (kTop yi * 4)).getLsbD 63 = false := by
    show (BitVec.ofNat 64 (kTop yi * 4)).toNat.testBit 63 = false
    rw [BitVec.toNat_ofNat]; exact Nat.testBit_lt_two_pow (by omega)
  have hk4 : kTop yi * 4 % 18446744073709551616 = kTop yi * 4 := by omega
  have hk4' : kTop yi * 4 % 64 = kTop yi * 4 := by omega
  have hk64 : kTop yi * 4 < 64 := by omega
  have hdm : yi / 2 ^ (kTop yi * 4) % 18446744073709551616 = yi / 2 ^ (kTop yi * 4) := Nat.mod_eq_of_lt (by omega)
  janus_run [lsr2, hk, e22, lsl2, e23 _ hk15, h63, hk4, hk4', ed yi _ hyi64, hk64, hdm] until [1800640]
  generalize hdd : yi / 2 ^ (kTop yi * 4) = d at hd16 hdm KT ⊢
  obtain ⟨eE1, eE2, eE3, eE4⟩ := hent d hd16
  have eh1 : M.readLE (sp + 432 + (8 * d + 2 * (8 * d))) 8 = bp + 8 * (d * n) := by
    rw [← eE2]; congr 1; omega
  have eh2 : M.readLE (sp + 432 + (8 * d + 2 * (8 * d)) + 8) 8 = n := by
    rw [← eE3]; congr 1; omega
  have hlt : ((n : Int) < (n : Int)) = False := by simp
  have hpd := hbuf d hd16
  have hzd := hzb d hd16
  unfold Apart at hzd
  have hne : zp ≠ bp + 8 * (d * n) := by
    intro e; rw [e] at hzd; omega
  have hLs' : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ sp - 4096 ∨ sp - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ sp + 8 ∨ sp + 8 + 24 ≤ r.1) := by
    intro r hr
    have := hLs r hr
    simp only [Outside, and_true] at this
    omega
  have hok1 := hok (bp + 8 * (d * n))
  have htoi : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  clear hent hbuf hzb
  have hpa := hpd.1
  have hz8n : InRanges zp (8 * n) L ∨ Outside zp (8 * n) R.rt :=
    z5.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
  have hza : M.accessible zp (8 * n) true = true := Memory.accessible_mono _ z3 (Nat.le_refl _) (by omega)
  have hpb := hpd.2.2.2
  unfold Apart at hpb
  janus_run [eh1, eh2, hlt, hne, htoi, lsl3, e8n n hn16] until [1800680] calls [hmv L b]
  rename_i _ _ _ m1 _ _ hF1 hL1 hI1 hC1
  have e64 : 64#64 - BitVec.ofNat 64 (kTop yi * 4) = BitVec.ofNat 64 (64 - kTop yi * 4) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have h63b : (BitVec.ofNat 64 (64 - kTop yi * 4)).getLsbD 63 = false := by
    show (BitVec.ofNat 64 (64 - kTop yi * 4)).toNat.testBit 63 = false
    rw [BitVec.toNat_ofNat]; exact Nat.testBit_lt_two_pow (by omega)
  janus_run [r168, r400, r1000, r992, r1024, r224, r1016, r1032, e23 _ hk15, e64, h63b, lsl2] until [testL]
  trace_state
  sorry

end FvModexp.Arm64.W4Pro
