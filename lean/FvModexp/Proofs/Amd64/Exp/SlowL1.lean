import FvModexp.Proofs.Amd64.Exp.SlowSq
import FvModexp.Proofs.Amd64.Exp.SlowK2
import FvModexp.Proofs.Amd64.Exp.SlowL1R

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): lower-loop segment L1 — `KT2` (`j < 64`) → `zz = zz.sqr(stk, z)` → `KS2` (agent asm s75;
twin of arm64 `SlowL1Q`, layout of expmc's `SlowU1`)

`runL1` (`t2` → the `nat.sqr` entry, return `sq2R`), then expmc's generic `sqrS`; `KS2` gets the square in `z`, the old
`z` as `zz` (slots `0x170`/`0xe0`/`0xd8`), `r`'s and `q`'s lengths/caps from the spills (nat.go:769-770).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

theorem wsL1_own {sp K : Nat} (hK : K + 8 ≤ sp) : ∀ r ∈ wsL1 sp, OwnR sp K r := by
  intro r hr
  simp only [wsL1, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [OwnR] <;> omega

/-- the slots L1 does not write -/
theorem rdL1 {m m' : Memory} {sp : Nat} (hF : MemFrame m m' (wsL1 sp)) (h8 : 8 ≤ sp) :
    m'.readLE (sp + 0xc0) 8 = m.readLE (sp + 0xc0) 8 ∧ m'.readLE (sp + 0xb0) 8 = m.readLE (sp + 0xb0) 8 ∧
    m'.readLE (sp + 0x160) 8 = m.readLE (sp + 0x160) 8 ∧ m'.readLE (sp + 0x168) 8 = m.readLE (sp + 0x168) 8 ∧
    (∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → m'.readLE a k = m.readLE a k) := by
  refine ⟨hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_, fun a k h1 _ => hF.readLE _ _ ?_⟩ <;>
  simp only [wsL1, outside_cons, outside_nil, and_true] <;> omega

theorem sqWL {zl xl ml W : Nat} (h : zl ≤ max xl ml) (hx : xl ≤ 128) (hm : ml ≤ 128) (hW : 7104 ≤ W) :
    sqrW zl ≤ W := by
  unfold sqrW ksqrW; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the `sqr` call from L1's stores (pure; `T` = the callee-entry state) -/
theorem callL1 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W H : Nat} (hsq : SqrE0 impl R ns W) (hWK : W ≤ K) (hW : 7104 ≤ W)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : W64} {Q : State → Prop} {S0 : State} {L1 : List (Nat × Nat)} {b1 i j : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KT2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S0 L1 b1 i j v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (hjw : j < 64) (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H) (hcost : sqrCQ zl + stkR H S0.mem st ≤ b1)
    (KS : ∀ (S' : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat),
      KS2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L2 b2 i j v p' l' c' (Zv * Zv) z zl zc'
        rr rl rc q ql qc →
      b1 - (sqrCQ zl + stkR H S0.mem st) + stkR H S'.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 S' Q)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 6229984) (h4 : T.regs 4 = BitVec.ofNat 64 (sp - 8))
    (h14 : T.regs 14 = S0.regs 14) (hfs : T.fsBase = S0.fsBase) (hx15 : T.xmm 15 = S0.xmm 15) (hdf : T.df = S0.df)
    (hF : MemFrame S0.mem T.mem (wsL1 sp)) (hrg : T.mem.regions = S0.mem.regions)
    (hrd : T.mem.readLE (sp - 8) 8 = sq2R)
    (w88 : T.mem.readLE (sp + 0x88) 8 = v.toNat) (w100 : T.mem.readLE (sp + 0x100) 8 = ql)
    (wf8 : T.mem.readLE (sp + 0xf8) 8 = qc) (wf0 : T.mem.readLE (sp + 0xf0) 8 = rl)
    (we8 : T.mem.readLE (sp + 0xe8) 8 = rc) (w170 : T.mem.readLE (sp + 0x170) 8 = z)
    (we0 : T.mem.readLE (sp + 0xe0) 8 = zl) (wd8 : T.mem.readLE (sp + 0xd8) 8 = zc')
    (h0 : T.regs 0 = BitVec.ofNat 64 zz) (h3 : T.regs 3 = BitVec.ofNat 64 zzl) (h1 : T.regs 1 = BitVec.ofNat 64 zzc)
    (h7 : T.regs 7 = BitVec.ofNat 64 st) (h6 : T.regs 6 = BitVec.ofNat 64 z) (h8 : T.regs 8 = BitVec.ofNat 64 zl)
    (h9 : T.regs 9 = BitVec.ofNat 64 zc') :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hxl : xl ≤ 128 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hml : ml ≤ 128 := hP.2.2.2.2.2.1
  have hs13 : stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzlb := hk.zlb
  have hz12 : zl ≤ 2 ^ 12 := by omega
  have hs16 : stLen s.mem st + 4 * (2 * zl) + 64 ≤ 2 ^ 16 := by omega
  have hH' : stLen s.mem st + 4 * (2 * zl) + 64 ≤ H := by omega
  obtain ⟨uc0, ub0, u160, u168, ukw⟩ := rdL1 hF (by omega)
  refine sqrS hap hns hnf hsq hWK hP hk.jc hk.bb hz12 (sqWL hzlb hxl hml hW) hs16 hH' hcost (idx := 0x5fb)
    (by decide) T hpc h4 h14 hfs hx15 hdf hF hrg (wsL1_own hK3) ukw hrd h0 h3 h1 h7 h6 h8 h9 ?_
  intro s' L2 b2 p' l' c' hpc' hj' hkp e0 e3 e1 hB' hl' hbud
  have hr : ∀ a, sp + 0x68 ≤ a → a + 8 ≤ sp + 0x220 → s'.mem.readLE a 8 = T.mem.readLE a 8 :=
    fun a h1 h2 => hkp a 8 h1 h2
  refine KS s' L2 b2 p' l' c' ⟨hj', hB', hk.iy, (hr _ (by omega) (by omega)).trans (uc0.trans hk.sc0),
    (hr _ (by omega) (by omega)).trans (ub0.trans hk.sb0), hpc', by omega, hjw, e0, e3, e1,
    (hr _ (by omega) (by omega)).trans w170, (hr _ (by omega) (by omega)).trans we0,
    (hr _ (by omega) (by omega)).trans wd8, (hr _ (by omega) (by omega)).trans (u160.trans hk.s160),
    (hr _ (by omega) (by omega)).trans wf0, (hr _ (by omega) (by omega)).trans we8,
    (hr _ (by omega) (by omega)).trans (u168.trans hk.s168), (hr _ (by omega) (by omega)).trans w100,
    (hr _ (by omega) (by omega)).trans wf8, (hr _ (by omega) (by omega)).trans w88⟩ hbud

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **L1**: from `KT2` with `j < 64` to `KS2` (the square in `z`, the old `z` as `zz`) -/
theorem segL1 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W H : Nat} (hsq : SqrE0 impl R ns W) (hWK : W ≤ K) (hW : 7104 ≤ W)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 i j : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KT2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 i j v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (hjw : j < 64) (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H) (hcost : sqrCQ zl + stkR H S.mem st ≤ b1)
    (KS : ∀ (S' : State) (L2 : List (Nat × Nat)) (b2 p' l' c' : Nat),
      KS2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L2 b2 i j v p' l' c' (Zv * Zv) z zl zc'
        rr rl rc q ql qc →
      b1 - (sqrCQ zl + stkR H S.mem st) + stkR H S'.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
    rw [hk.jc.wc.fr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega)
  obtain ⟨bz, bzc⟩ := hk.bb.bz.1.lt64
  obtain ⟨-, brc⟩ := hk.bb.br.lt64
  obtain ⟨-, bqc⟩ := hk.bb.bq.lt64
  have hzl := hk.bb.bz.2.1
  have hrl := hk.bb.lr
  have hql := hk.bb.lq
  refine runL1 ret0 Q sp j z zl zc' zz zzl zzc rl rc ql qc v S.mem hacc (by omega) hK5 hjw bz (by omega) bzc
    (by omega) brc (by omega) bqc hk.sb0 hk.s150 hk.s70 hk.s78 S hk.pc hk.jc.esp rfl hk.e0 hk.e10 hk.e8 hk.e1 hk.e2
    hk.e13 hk.e15 hk.e9 ?_
  intro T t1 t4 t14 tfs tx tdf tF trg tra w88 w100 wf8 wf0 we8 w170 we0 wd8 r0 r3 r1 r7 r6 r8 r9
  exact callL1 hap hns hnf hsq hWK hW hP hk hjw hH hcost KS T t1 t4 t14 tfs tx tdf tF trg tra w88 w100 wf8 wf0
    we8 w170 we0 wd8 r0 r3 r1 (r7.trans hk.e7) r6 r8 r9

end

end FvModexp.Amd64.ExpSlow
