import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2ZcD

/-!
# window-2 prologue (arm64): `zz.make(2n)`, the first window, `copy(z, powers[yi>>2k])` (nat.go:1427-1446)

From `zj` (fn+0x774, the join after `z = z.make(2n)`: X0 = z, X14 = cap z) to the loop test (fn+0xaa0).
`zz` (the `lsh` result, cap ≥ 2n+1) is reused; `bitLen(y[len-1])` by smear + `CLZ` (Common/BitLenA64);
`k = (bitLen+1)/2 - 1`, `copy(z, powers[yi >> 2k])` (memmove, `W2ZcB`), `yi <<= 64 - 2k`, `k--` (`W2ZcC`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf)

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zcopy (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibW.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen bp zp zc zzp zzc : Nat) (tbl : Nat → Nat) (M : Memory)
    (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hz : Buf R L g sp n M zp zc) (hzzc : 2 * n ≤ zzc)
    (hzzc' : zzc < 2 ^ 40) (hy : Inp R L sp ylen M yp) (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40)
    (hyi : 0 < M.readLE (yp + 8 * (ylen - 1)) 8)
    (hent : ∀ d, d < 4 → Ent sp n bp tbl M d) (hbuf : ∀ d, d < 4 → Inp R L sp n M (bp + 8 * (d * n)))
    (hzb : ∀ d, d < 4 → Apart zp (8 * zc) (bp + 8 * (d * n)) (8 * n))
    (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (r712 : M.readLE (sp + 712) 8 = ylen) (r704 : M.readLE (sp + 704) 8 = yp)
    (r736 : M.readLE (sp + 736) 8 = n) (r224 : M.readLE (sp + 224) 8 = k0) (r728 : M.readLE (sp + 728) 8 = mp)
    (r744 : M.readLE (sp + 744) 8 = mc)
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
      S'.regs 20 = BitVec.ofNat 64 ((M.readLE (yp + 8 * (ylen - 1)) 8 * 2 ^ (64 - kTop (M.readLE (yp + 8 * (ylen - 1)) 8) * 2)) % 2 ^ 64) →
      S'.regs 21 = BitVec.ofNat 64 (kTop (M.readLE (yp + 8 * (ylen - 1)) 8)) - 1#64 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      MemFrame M M' (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) → LiveFrame M M' L [(zp, zp + 8 * n)] →
      R.inv b L g (view R.rt L M') → M'.regions = M.regions →
      M'.readLE zp (8 * n) = tbl (M.readLE (yp + 8 * (ylen - 1)) 8 / 2 ^ (kTop (M.readLE (yp + 8 * (ylen - 1)) 8) * 2)) →
      M'.readLE (sp + 240) 8 = ylen - 1 →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
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
  janus_run [r168, r400, r712, r704, r736, r224, r728, r744, e17, ry] until [zclz]
  gen_reg 21 as t with hT
  have hT' : BitLenA64.smearBV (BitVec.ofNat 64 yi) = t := by rw [← hT, ← BitLenA64.smearBV]
  have hzz64 : zzp < 2 ^ 64 := by rw [← r400]; exact Util.readLE8_lt _ _
  refine zcD impl R hmv ret hret Q b L g sp n mp mc k0 yp ylen bp zp zc zzp zzc yi tbl M r18 r29 t he hn hn16
    ⟨z1, z2, z3, z4, z5, z6, z7⟩ hzzc' hzz64 hyl hyl' hyi hyi64 hent hbuf hzb r712 r704 r736 r224 r728 r744 hok hinv
    _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hT' ?_ ?_ ?_ ?_ KT
  all_goals janus_simp

end FvModexp.Arm64.W2Pro
