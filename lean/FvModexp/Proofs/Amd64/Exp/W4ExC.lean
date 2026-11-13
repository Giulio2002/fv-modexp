import FvModexp.Proofs.Amd64.Exp.W4ExS

set_option autoImplicit false

/-!
# window-4 (amd64), the final reduction (nat.go:1476-1488) composed (agent expmc s47)

Twin of `Arm64.W4Loop.exB`. From the entry of the first `zz.cmp(m)` (`W4Loop.exA`'s continuation state) to the join
`njoin`: `cmp < 0` → `exCmp`'s `KLt` (nothing written, `zz` unchanged); `cmp ≥ 0` → `exSub` (then `zz = m`, the
difference `0`). The value at the join is `if m ≤ zz then 0 else zz` (= the model's final reduction, as `zz ≤ m`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W4Loop

theorem win_of_live {L : List (Nat × Nat)} {sp a k : Nat} (hLs : LiveSep L [(sp - 4296, sp + 0x3c0)])
    (hs : 4296 ≤ sp) (hin : InRanges a k L) : Outside a k [(sp - 4296, sp + 0x60)] := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := hLs r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

theorem jw_of_win {rt : List (Nat × Nat)} {sp p c a k : Nat}
    (ho : Outside a k (rt ++ [(sp - 4296, sp + 0x60), (sp + 0x98, sp + 0xa8), (sp + 0x188, sp + 0x190)] ++
      [(p, p + 8 * c)])) : Outside a k [(sp - 4296, sp + 0x60)] := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
  exact ho.1.2.1

/-- `JoinPost` moves back over a frame inside the callee window (the first `cmp`, the `CALL`'s return address) -/
theorem JoinPost.pre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {g sp n zzp zzc V p l c : Nat}
    {M M1 M' : Memory} (hf : MemFrame M M1 [(sp - 4296, sp + 0x60)]) (hreg : M1.regions = M.regions)
    (hLs : LiveSep L [(sp - 4296, sp + 0x3c0)]) (hs : 4296 ≤ sp)
    (h : JoinPost R b L g sp n zzp zzc V M1 p l c M') : JoinPost R b L g sp n zzp zzc V M p l c M' := by
  obtain ⟨L', b', hLE, hb, hinv, hrg, hF, hLF, rest⟩ := h
  exact ⟨L', b', hLE, hb, hinv, hrg.trans hreg, hf.trans hF (fun a k ho => ⟨jw_of_win ho, ho⟩),
    (FvModexp.Expmc.liveFrame_of_frame hf (fun a k hin _ => win_of_live hLs hs hin)).trans hLF (fun _ _ h => h),
    rest⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- the final reduction: from the entry of the first `zz.cmp(m)` to the join `njoin` -/
theorem exC {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmvok : ∀ d src k, k ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, src, k])
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y : Nat} {tbl pp pcap : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory} (hd : Extracted.program.DataLoaded M0)
    (hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp pcap M0) (hnm : NatNorm M0 mp n)
    {ret : W64} {Q : State → Prop} (S : State) (r5 : W64) (zp zc zzp zzc : Nat)
    (hpc : S.rip = BitVec.ofNat 64 cmpE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (hra : S.mem.readLE (sp - 8) 8 = fnE + 0x10d0) (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g)
    (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zzp) (h3 : S.regs 3 = BitVec.ofNat 64 n)
    (h7 : S.regs 7 = BitVec.ofNat 64 mp) (h6 : S.regs 6 = BitVec.ofNat 64 n)
    (hB : Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 S.mem zp zc zzp zzc)
    (hz8 : zzp % 8 = 0)
    (r188 : S.mem.readLE (sp + 0x188) 8 = zzp) (r98 : S.mem.readLE (sp + 0x98) 8 = n)
    (ra0 : S.mem.readLE (sp + 0xa0) 8 = zzc) (hZle : S.mem.readLE zzp (8 * n) ≤ M0.readLE mp (8 * n))
    (KJ : ∀ (S' : State) (p l c : Nat), S'.rip = BitVec.ofNat 64 njoin → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 5 = r5 → S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 7 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 l → S'.regs 8 = BitVec.ofNat 64 c →
      JoinPost R b L g sp n zzp zzc
        (if M0.readLE mp (8 * n) ≤ S.mem.readLE zzp (8 * n) then 0 else S.mem.readLE zzp (8 * n)) S.mem p l c S'.mem →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he := hst.1
  have hs1 : 4296 ≤ sp := he.2.1
  have hLs := he.2.2.2.2.2.2.2.2.2.2.1
  have hn := hst.2.1
  have hBzz := hB.2.1
  refine exCmp hap hst S r5 zp zc zzp zzc hpc hsp hra h5 h14 hfs hx15 hdf h0 h3 h7 h6 hB hM r188 r98 ra0 ?_ ?_
  · intro S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hM' hzz' hfw hrg hlt
    obtain ⟨c1, c2, c3, c4, c5, -, -, -⟩ := hBzz
    refine KJ S' zzp n zzc a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ⟨L, b, LiveExt.refl R L, by omega, hM'.2.1, hrg,
      hfw.mono (fun a k ho => jw_of_win ho),
      FvModexp.Expmc.liveFrame_of_frame hfw (fun a k hin _ => win_of_live hLs hs1 hin), ?_, by omega,
      ⟨by omega, c2⟩, fun _ => ⟨hz8, c5, by rw [hM'.1.1.accessible]; exact c3, c4⟩, Or.inl ⟨rfl, rfl⟩,
      Or.inr ⟨by omega, by rw [hM'.1.1.accessible]; exact M0.accessible_sub c3 (Or.inr rfl) (Nat.le_refl _) (by omega)⟩⟩
    unfold natVal
    rw [hzz', if_neg (by omega)]
  · intro S2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 hM2 q188 q98 qa0 hzz2 hfw hrg hge
    refine exSub hap hmk hmv hmvok hwt hro hd hst S2 r5 zp zc zzp zzc a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
      a15 a16 a17 hB hM2 hz8 hnm (by rw [hzz2]; omega) ?_
    intro S' p l c b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 hJ
    refine KJ S' p l c b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 ?_
    rw [if_pos hge]
    exact JoinPost.pre hfw hrg hLs hs1 hJ

end FvModexp.Amd64.W4Loop
