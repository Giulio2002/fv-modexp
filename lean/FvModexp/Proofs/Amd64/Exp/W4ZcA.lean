import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.W4Seg
import FvModexp.Proofs.Amd64.Exp.W4ZcK
import FvModexp.Proofs.Amd64.Exp.W4ZcK0

set_option autoImplicit false

/-!
# window-4 prologue (amd64): the first window, `copy(z, powers[yi >> 4k])` (nat.go:1434-1446; agent expmc s48)

Twin of `Arm64.W4Zc.zcopy`. From `zj` (fn+0xb8f, after `z.make`/`zz.make`) to the loop test: `bitLen(y[len-1])` (smear +
`BSRQ`), `k = (bitLen+3)/4 - 1`, `d = yi >> 4k < 16`, the table header loads, `min(n, len powers[d]) = n`, the
`z == powers[d]` test (refuted: `z` is apart from the table), then `W4ZcT.zcT` (memmove, `yi <<= 64 - 4k`, `k--`). The
`k = 0` case is split off (shift counts 0 / 64).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf)

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zcopy (impl : List Amd64.Segment) {R : RtInv}
    (hmv : MemmoveLive64 (LibW.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {ret : W64} {Q : State → Prop}
    (b : Nat) (L : List (Nat × Nat)) (g fs sp n mp mc k0 yp ylen zp zc zzp zzc yi : Nat) (pp pcap tbl : Nat → Nat) (M : Memory)
    (r5 : W64)
    (he : Env R L g fs sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hz : Buf R L g fs sp n M zp zc)
    (hnz : n ≤ zzc) (hzzc : zzc < 2 ^ 40) (hzzp : zzp < 2 ^ 64)
    (hy : Inp R L sp ylen M yp) (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40)
    (hyi : M.readLE (yp + 8 * (ylen - 1)) 8 = yi) (hyi0 : 0 < yi)
    (hent : ∀ d, d < 16 → Ent sp n pp pcap tbl M d) (hbuf : ∀ d, d < 16 → Inp R L sp n M (pp d))
    (hzb : ∀ d, d < 16 → Apart zp (8 * zc) (pp d) (8 * n))
    (r398 : M.readLE (sp + 0x398) 8 = ylen) (r390 : M.readLE (sp + 0x390) 8 = yp)
    (r168 : M.readLE (sp + 0x168) 8 = zp) (r88 : M.readLE (sp + 0x88) 8 = zc)
    (r3a8 : M.readLE (sp + 0x3a8) 8 = mp) (rd8 : M.readLE (sp + 0xd8) 8 = k0) (r3b0 : M.readLE (sp + 0x3b0) 8 = n)
    (r3b8 : M.readLE (sp + 0x3b8) 8 = mc)
    (hok : ∀ d, R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, d, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 zj) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc) (h1 : S.regs 1 = BitVec.ofNat 64 zzp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 zzc)
    (KT : ∀ S' : State, S'.rip = BitVec.ofNat 64 testL → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 2 = BitVec.ofNat 64 zc → S'.regs 8 = BitVec.ofNat 64 zzp →
      S'.regs 11 = BitVec.ofNat 64 n → S'.regs 12 = BitVec.ofNat 64 zzc → S'.regs 3 = BitVec.ofNat 64 mp →
      S'.regs 6 = BitVec.ofNat 64 k0 → S'.regs 10 = BitVec.ofNat 64 mc →
      S'.regs 9 = BitVec.ofNat 64 ((yi * 2 ^ (64 - kTop yi * 4)) % 2 ^ 64) →
      S'.regs 15 = BitVec.ofNat 64 (kTop yi) - 1#64 →
      S'.regs 7 = BitVec.ofNat 64 yp → S'.regs 13 = BitVec.ofNat 64 ylen → S'.regs 1 = BitVec.ofNat 64 (ylen - 1) →
      MemFrame M S'.mem (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) → LiveFrame M S'.mem L [(zp, zp + 8 * n)] →
      R.inv b L g (view R.rt L S'.mem) → S'.mem.regions = M.regions →
      S'.mem.readLE zp (8 * n) = tbl (yi / 2 ^ (kTop yi * 4)) →
      S'.mem.readLE (sp + 0x140) 8 = n → S'.mem.readLE (sp + 0xe8) 8 = ylen - 1 →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he0 := he
  have he0' := he
  have hz0 := hz
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  have hyi64 : yi < 2 ^ 64 := by rw [← hyi]; exact Util.readLE8_lt _ _
  have hnz' : (BitVec.ofNat 64 zzc < BitVec.ofNat 64 n) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]; omega
  have ry : M.readLE (yp + ylen * 8 - 8) 8 = yi := by rw [← hyi, show yp + ylen * 8 - 8 = yp + 8 * (ylen - 1) by omega]
  have hya := hy.1
  have hyp := hy.2.1
  refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 6208585) ?_
  janus64_run [r398, r390, hnz', ry] until [6208585]
  gen_reg 3 as t with hT
  have hts : t = BitLenA64.smearBV (BitVec.ofNat 64 yi) := by rw [← hT, ← smearR_eq]; rfl
  have ht0 : t.toNat ≠ 0 := by
    rw [hts]; exact (BitLenA64.smearBV_log2 _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hyi64]; omega)).1
  have ht0' : (t.toNat = 0) = False := by simp [ht0]
  refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 6208603) ?_
  janus64_run [ht0, ht0'] until [6208603]
  have hbs : BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 t.toNat) = BitVec.ofNat 64 (Exp.bitLen yi - 1) := by
    rw [hts, BitLenA64.clz_smear, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hyi64]
    have hc := Util.clz_bl 64 yi hyi64
    have hb : Aux.bitLen yi = Exp.bitLen yi := rfl
    rw [← hb]; exact congrArg (BitVec.ofNat 64) (by omega)
  obtain ⟨hk15, hd16⟩ := kTop_le yi hyi0 hyi64
  have e1 := ek1 yi hyi0 hyi64
  generalize hK : kTop yi = k at e1 hk15 hd16 KT
  have e2 := ek2 _ hk15
  have e3 := ek3 _ hk15
  have hk4 : k * 4 < 64 := by omega
  have hmsb : (BitVec.ofNat 64 (k * 4)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
  have e4 := ed yi k hyi64
  generalize hD : yi / 2 ^ (k * 4) = d at e4 hd16 KT
  refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 6208637) ?_
  janus64_run [hbs, e1, e2, e3, hmsb] until [6208637]
  have hzd' := hzb d hd16
  clear hzb
  by_cases hk0 : k = 0
  · refine zcK0 impl hmv b L g fs sp n mp mc k0 yp ylen zp zc zzp zzc yi k d pp pcap tbl M r5 he0' hn hn16 hz0 hk0
      (by subst hk0; rw [← hD]; simp) hd16 hzzc hzzp hyl hyl' hyi64 (hent d hd16) (hbuf d hd16) hzd' r398 r390 r168 r88
      r3a8 rd8 r3b0 r3b8 (hok _) hinv _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ KT
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | exact h5 | exact h14 | exact hx15 | exact hdf | exact hfs | exact hsp | exact h0 | exact h11 | exact h12 | rfl
  · refine zcK impl hmv b L g fs sp n mp mc k0 yp ylen zp zc zzp zzc yi k d pp pcap tbl M r5 he0' hn hn16 hz0 hk15 hk0
      hd16 e4 hzzc hzzp hyl hyl' hyi64 (hent d hd16) (hbuf d hd16) hzd' r398 r390 r168 r88
      r3a8 rd8 r3b0 r3b8 (hok _) hinv _ rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ KT
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | exact h5 | exact h14 | exact hx15 | exact hdf | exact hfs | exact hsp | exact h0 | exact h11 | exact h12 | rfl

end FvModexp.Amd64.W4Pro
