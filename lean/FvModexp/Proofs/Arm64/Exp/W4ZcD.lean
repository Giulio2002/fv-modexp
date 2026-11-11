import FvModexp.Proofs.Arm64.Exp.W4ZcB

/-!
# window-4 prologue (arm64): `CLZ` of the smeared top word (fn+0x7f4) → the first-window copy (`W4ZcB.zs`)

`bitLen(y[len-1])`, `k = (bitLen+3)/4 - 1`, `d = yi >> 4k` (< 16), the table header loads, `min(n, len powers[d])`,
the `z == powers[d]` test (refuted), then `zcB`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

/-- the `CLZ` of the smeared top word (fn+0x7f4) -/
abbrev zclz : Nat := 1800548

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zcD (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibExp.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen bp zp zc zzp zzc yi : Nat) (tbl : Nat → Nat)
    (M : Memory) (r18 r29 t : BitVec 64)
    (he : Env R L g sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hz : Buf R L g sp n M zp zc)
    (hzzc' : zzc < 2 ^ 40) (hzzp : zzp < 2 ^ 64) (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40)
    (hyi : 0 < yi) (hyi64 : yi < 2 ^ 64)
    (hent : ∀ d, d < 16 → Ent sp n bp tbl M d) (hbuf : ∀ d, d < 16 → Inp R L sp n M (bp + 8 * (d * n)))
    (hzb : ∀ d, d < 16 → Apart zp (8 * zc) (bp + 8 * (d * n)) (8 * n))
    (r1000 : M.readLE (sp + 1000) 8 = ylen) (r992 : M.readLE (sp + 992) 8 = yp)
    (r1024 : M.readLE (sp + 1024) 8 = n) (r224 : M.readLE (sp + 224) 8 = k0) (r1016 : M.readLE (sp + 1016) 8 = mp)
    (r1032 : M.readLE (sp + 1032) 8 = mc)
    (hok : ∀ d, R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, d, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 zclz) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zzp) (h13 : S.regs 13 = BitVec.ofNat 64 n)
    (h15 : S.regs 15 = BitVec.ofNat 64 zzc) (h17 : S.regs 17 = BitVec.ofNat 64 (ylen - 1))
    (h20 : S.regs 20 = BitVec.ofNat 64 yi) (h21 : S.regs 21 = t) (hT : BitLenA64.smearBV (BitVec.ofNat 64 yi) = t)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29)
    (hmem : S.mem = (M.writeLE (sp + 144) 8 zc).writeLE (sp + 368) 8 zp)
    (KT : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 testL → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 13 = BitVec.ofNat 64 n → S'.regs 14 = BitVec.ofNat 64 zc →
      S'.regs 1 = BitVec.ofNat 64 zzp → S'.regs 3 = BitVec.ofNat 64 n → S'.regs 15 = BitVec.ofNat 64 zzc →
      S'.regs 2 = BitVec.ofNat 64 n → S'.regs 9 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 mc →
      S'.regs 12 = BitVec.ofNat 64 k0 → S'.regs 16 = BitVec.ofNat 64 ylen →
      S'.regs 17 = BitVec.ofNat 64 (ylen - 1) → S'.regs 19 = BitVec.ofNat 64 yp →
      S'.regs 20 = BitVec.ofNat 64 ((yi * 2 ^ (64 - kTop yi * 4)) % 2 ^ 64) →
      S'.regs 21 = BitVec.ofNat 64 (kTop yi) - 1#64 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      MemFrame M M' (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) → LiveFrame M M' L [(zp, zp + 8 * n)] →
      R.inv b L g (view R.rt L M') → M'.regions = M.regions →
      M'.readLE zp (8 * n) = tbl (yi / 2 ^ (kTop yi * 4)) → M'.readLE (sp + 240) 8 = ylen - 1 →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hz0 := hz
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := hz0
  janus_run until [1800560]
  gen_reg 21 as bl with hBl
  have hbl : bl.toNat = Exp.bitLen yi := by
    rw [← hBl, ← hT, BitLenA64.clz_smear, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hyi64]
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
  have hkp1 : (kTop yi + 1) % 18446744073709551616 = kTop yi + 1 := by omega
  janus_run [lsr2, hk, e22, lsl2, e23 _ hk15, h63, hk4, hk4', ed yi _ hyi64, hk64, hdm] until [1800640]
  generalize hdd : yi / 2 ^ (kTop yi * 4) = d at hd16 hdm KT ⊢
  obtain ⟨eE1, eE2, eE3, eE4⟩ := hent d hd16
  have eh1 : M.readLE (sp + 432 + (8 * d + 2 * (8 * d))) 8 = bp + 8 * (d * n) := by
    rw [← eE2]; congr 1; omega
  have eh2 : M.readLE (sp + 432 + (8 * d + 2 * (8 * d)) + 8) 8 = n := by
    rw [← eE3]; congr 1; omega
  have hlt : ((n : Int) < (n : Int)) = False := by simp
  have hpd := hbuf d hd16
  have hzd' := hzb d hd16
  have hzd := hzd'
  unfold Apart at hzd
  have hne : zp ≠ bp + 8 * (d * n) := by
    intro e; rw [e] at hzd; omega
  have htoi : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  clear hent hbuf hzb
  janus_run [eh1, eh2, hlt, hne, htoi] until [zs]
  refine zcB impl R hmv ret hret Q b L g sp n mp mc k0 yp ylen zp zc zzp zzc yi (kTop yi) (bp + 8 * (d * n)) (tbl d) M
    r18 r29 he hn hn16 hz hk15 hzzc' hzzp hyl hyl' hyi64 hpd hzd' eE1 r1000 r992 r1024 r224 r1016 r1032
    (hok _) hinv _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ KT
  all_goals janus_simp

end FvModexp.Arm64.W4Pro
