import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.W4Seg
import FvModexp.Proofs.Amd64.Exp.W4ZcT

set_option autoImplicit false

/-!
# window-4 prologue (amd64), first window: the table lookup `powers[d]` and the `z == powers[d]` test,
`k = 0` (fn+0xc1d → fn+0xc58, then `W4ZcT.zcT`; agent expmc s48)

Split out of `W4ZcA.zcopy` (module time). `d = yi >> 4k < 16`, the header loads, `min(n, len powers[d]) = n`, the
pointer test (refuted: `z` is apart from `powers[d]`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zcK0 (impl : List Amd64.Segment) {R : RtInv}
    (hmv : MemmoveLive64 (LibW.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {ret : W64} {Q : State → Prop}
    (b : Nat) (L : List (Nat × Nat)) (g fs sp n mp mc k0 yp ylen zp zc zzp zzc yi k d : Nat) (pp pcap tbl : Nat → Nat)
    (M : Memory) (r5 : W64)
    (he : Env R L g fs sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hz : Buf R L g fs sp n M zp zc)
    (hk : k = 0) (hd : d = yi) (hd16 : d < 16)
    (hzzc : zzc < 2 ^ 40) (hzzp : zzp < 2 ^ 64) (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40) (hyi64 : yi < 2 ^ 64)
    (hent : Ent sp n pp pcap tbl M d) (hpd : Inp R L sp n M (pp d)) (hzd' : Apart zp (8 * zc) (pp d) (8 * n))
    (r398 : M.readLE (sp + 0x398) 8 = ylen) (r390 : M.readLE (sp + 0x390) 8 = yp)
    (r168 : M.readLE (sp + 0x168) 8 = zp) (r88 : M.readLE (sp + 0x88) 8 = zc)
    (r3a8 : M.readLE (sp + 0x3a8) 8 = mp) (rd8 : M.readLE (sp + 0xd8) 8 = k0) (r3b0 : M.readLE (sp + 0x3b0) 8 = n)
    (r3b8 : M.readLE (sp + 0x3b8) 8 = mc)
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, pp d, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6208637) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 (k * 4)) (h6 : S.regs 6 = BitVec.ofNat 64 yi)
    (h8 : S.regs 8 = BitVec.ofNat 64 zzp) (h9 : S.regs 9 = BitVec.ofNat 64 yi) (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 zzc)
    (h15 : S.regs 15 = BitVec.ofNat 64 (k + 1))
    (KT : ∀ S' : State, S'.rip = BitVec.ofNat 64 testL → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 2 = BitVec.ofNat 64 zc → S'.regs 8 = BitVec.ofNat 64 zzp →
      S'.regs 11 = BitVec.ofNat 64 n → S'.regs 12 = BitVec.ofNat 64 zzc → S'.regs 3 = BitVec.ofNat 64 mp →
      S'.regs 6 = BitVec.ofNat 64 k0 → S'.regs 10 = BitVec.ofNat 64 mc →
      S'.regs 9 = BitVec.ofNat 64 ((yi * 2 ^ (64 - k * 4)) % 2 ^ 64) → S'.regs 15 = BitVec.ofNat 64 k - 1#64 →
      S'.regs 7 = BitVec.ofNat 64 yp → S'.regs 13 = BitVec.ofNat 64 ylen → S'.regs 1 = BitVec.ofNat 64 (ylen - 1) →
      MemFrame M S'.mem (R.rt ++ cw sp ++ [(zp, zp + 8 * n)]) → LiveFrame M S'.mem L [(zp, zp + 8 * n)] →
      R.inv b L g (view R.rt L S'.mem) → S'.mem.regions = M.regions → S'.mem.readLE zp (8 * n) = tbl d →
      S'.mem.readLE (sp + 0x140) 8 = n → S'.mem.readLE (sp + 0xe8) 8 = ylen - 1 →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hk hd
  have he0 := he
  have hz0 := hz
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  obtain ⟨eE1, eE2, eE3, eE4⟩ := hent
  have hdm : d % 2 ^ 64 = d := Nat.mod_eq_of_lt (by omega)
  have eh1 : M.readLE (sp + (d + d * 2) * 8 + 424) 8 = pp d := by
    rw [show sp + (d + d * 2) * 8 + 424 = sp + 0x1a8 + 24 * d by omega]; exact eE2
  have eh2 : M.readLE (sp + (d + d * 2) * 8 + 432) 8 = n := by
    rw [show sp + (d + d * 2) * 8 + 432 = sp + 0x1b0 + 24 * d by omega]; exact eE3
  have hzd := hzd'
  unfold Apart at hzd
  have hpdl : pp d < 2 ^ 64 := by have := hpd.2.1; omega
  have hne : ((BitVec.ofNat 64 zp : BitVec 64) = BitVec.ofNat 64 (pp d)) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  have hne' : ((18446744073709551616 - pp d + zp) % 18446744073709551616 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; omega
  have hne'' : ((18446744073709551616 - pp d % 18446744073709551616 + zp % 18446744073709551616) % 18446744073709551616 = 0) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; omega
  have htoi : ((BitVec.ofNat 64 n).toInt < (n : Int)) = False := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 6208696) ?_
  janus64_run [hdm, eh1, eh2, hne, hne', hne'', htoi] until [6208696]
  refine zcT impl hmv b L g fs sp n mp mc k0 yp ylen zp zc zzp zzc d 0 (pp d) (tbl d) M r5 he hn hn16 hz0
    (by omega) hzzc hzzp hyl hyl' hyi64 hpd hzd' eE1 r168 r88 r398 r390 r3a8 rd8 r3b0 r3b8 hok hinv _ rfl ?_ rfl
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ KT
  all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  all_goals first | exact h5 | exact h14 | exact hx15 | exact hdf | exact hfs | exact hsp | exact h0 | exact h1 | exact h8 | exact h9 | exact h11 | exact h12 | exact h15 | rfl

end FvModexp.Amd64.W4Pro
