import FvModexp.Proofs.Amd64.Exp.SlowDv
import FvModexp.Proofs.Amd64.Exp.SlowK2
import FvModexp.Proofs.Amd64.Exp.SlowL3R

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): lower-loop segment L3 — `KD2` → `zz, r = zz.div(r, z, m)` → `KJ2` (agent asm s75;
twin of arm64 `SlowL3Q`; nat.go:778-780)

`runL3` (`len m > 0` always: `0 < M`) → expmc's `divS` (return `dv2R`) → `runL3b` (stores the old `z` to `0x160`):
`z` = the remainder (`Zv % M`), `zz` = the old `q`, `r` = the old `z`, `q` = the quotient.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

theorem wsL3_own {sp K : Nat} (hK : K + 8 ≤ sp) : ∀ r ∈ wsL3 sp, OwnR sp K r := by
  intro r hr
  simp only [wsL3, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only [OwnR] <;> omega

/-- the slots L3 does not write before `nat.div` -/
theorem rdL3 {m m' : Memory} {sp : Nat} (hF : MemFrame m m' (wsL3 sp)) (h8 : 8 ≤ sp) :
    m'.readLE (sp + 0xc0) 8 = m.readLE (sp + 0xc0) 8 ∧ m'.readLE (sp + 0xb0) 8 = m.readLE (sp + 0xb0) 8 ∧
    m'.readLE (sp + 0x168) 8 = m.readLE (sp + 0x168) 8 ∧ m'.readLE (sp + 0x100) 8 = m.readLE (sp + 0x100) 8 ∧
    m'.readLE (sp + 0xf8) 8 = m.readLE (sp + 0xf8) 8 ∧ m'.readLE (sp + 0x88) 8 = m.readLE (sp + 0x88) 8 ∧
    (∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → m'.readLE a k = m.readLE a k) := by
  refine ⟨hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_, hF.readLE _ _ ?_,
    hF.readLE _ _ ?_, fun a k h1 _ => hF.readLE _ _ ?_⟩ <;>
  simp only [wsL3, outside_cons, outside_nil, and_true] <;> omega

/-- the slots the `0x160` store keeps -/
theorem rd160 {m m' : Memory} {sp : Nat} (hF : MemFrame m m' [(sp + 0x160, sp + 0x168)]) :
    m'.readLE (sp + 0xc0) 8 = m.readLE (sp + 0xc0) 8 ∧ m'.readLE (sp + 0xb0) 8 = m.readLE (sp + 0xb0) 8 ∧
    (∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → m'.readLE a k = m.readLE a k) := by
  refine ⟨hF.readLE _ _ ?_, hF.readLE _ _ ?_, fun a k h1 _ => hF.readLE _ _ ?_⟩ <;>
  simp only [outside_cons, outside_nil, and_true] <;> omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

/-- `BB` through the function's own stores (`WC.own`'s transports) -/
theorem BB.own {M M' : Memory} {L1 : List (Nat × Nat)} {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (h : BB R L st zp zc M L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc)
    (hdl : ∀ q c, DL R L st zp zc M L1 q c → DL R L st zp zc M' L1 q c)
    (hln : ∀ q l c v, LN R L st zp zc M L1 q l c v → LN R L st zp zc M' L1 q l c v) :
    BB R L st zp zc M' L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc :=
  ⟨hln _ _ _ _ h.bz, hdl _ _ h.bzz, h.lzz, hdl _ _ h.br, h.lr, hdl _ _ h.bq, h.lq, h.p1, h.p2, h.p3, h.p4, h.p5,
    h.p6⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the tail `dv2R` → `j2` of L3 (the `0x160` store) -/
theorem tailL3 {impl : List Amd64.Segment} (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s)
    {H : Nat} {ret0 : W64} {Q : State → Prop} {S : State} {L2 : List (Nat × Nat)} {b2 i j : Nat} {v : BitVec 64}
    {z zl zc' pr lr cr Zv q ql qc pq lq cq : Nat}
    (hj : JC R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L2 b2)
    (hB : BB R L st zp zc S.mem L2 pr lr cr Zv q ql qc z zl zc' pq lq cq)
    (hpc : S.rip = BitVec.ofNat 64 dv2R) (hiy : i + 2 ≤ yl) (hlr : lr ≤ max xl ml) (hjw : j < 64)
    (hc0 : S.mem.readLE (sp + 0xc0) 8 = i) (hb0 : S.mem.readLE (sp + 0xb0) 8 = j)
    (h88 : S.mem.readLE (sp + 0x88) 8 = v.toNat) (h198 : S.mem.readLE (sp + 0x198) 8 = z)
    (h148 : S.mem.readLE (sp + 0x148) 8 = zl) (h140 : S.mem.readLE (sp + 0x140) 8 = zc')
    (h168 : S.mem.readLE (sp + 0x168) 8 = q) (h100 : S.mem.readLE (sp + 0x100) 8 = ql)
    (hf8 : S.mem.readLE (sp + 0xf8) 8 = qc)
    (e0 : S.regs 0 = BitVec.ofNat 64 pq) (e3 : S.regs 3 = BitVec.ofNat 64 lq) (e1 : S.regs 1 = BitVec.ofNat 64 cq)
    (e7 : S.regs 7 = BitVec.ofNat 64 pr) (e6 : S.regs 6 = BitVec.ofNat 64 lr) (e8 : S.regs 8 = BitVec.ofNat 64 cr)
    (KJ : ∀ (S' : State), KJ2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L2 b2 i j v pr lr cr Zv
        q ql qc z zl zc' pq lq cq → stkR H S'.mem st = stkR H S.mem st →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
    rw [hj.wc.fr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega)
  obtain ⟨bz, -⟩ := hB.br.lt64
  obtain ⟨hstw, -⟩ := hP.stkF
  unfold Apart at hstw
  refine runL3b ret0 Q sp z zl zc' q ql qc v S.mem hacc (by omega) hK5 bz h88 h198 h148 h140 h168 h100 hf8 S hpc
    hj.esp rfl ?_
  intro T t1 t4 tF trg t160 r0 r3 r1 r15 r9 r11 r12 r13 r8 r6 r7 r2 t14 tfs tx tdf
  obtain ⟨hw, hdl, hln⟩ := WC.own hP hj.wc tF trg (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp only [OwnR]; omega)
  obtain ⟨uc0, ub0, ukw⟩ := rd160 tF
  have hcap : stCap T.mem st = stCap S.mem st :=
    tF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine KJ T ⟨hj.call (t4.trans hj.esp.symm) t14 tfs tx tdf hw ukw, hB.own hdl hln, hiy, uc0.trans hc0,
    ub0.trans hb0, t1, hlr, hjw, r0.trans e7, r3.trans e6, r1.trans e8, r8, r6, r7, r15.trans e0, r9.trans e3,
    r11.trans e1, t160, r12, r13, r2⟩ (stkR_congr hcap)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **L3**: from `KD2` to `KJ2` (`z := z mod m`, buffers rotated) -/
theorem segL3 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W H : Nat} {dvC : Nat → Nat → Nat} (hdv : DivHypLGQ impl R ns W 0x70 dvC) (hWK : W ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 i j : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KD2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 i j v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H) (hcost : dvC zl ml + stkR H S.mem st ≤ b1)
    (KJ : ∀ (S' : State) (L2 : List (Nat × Nat)) (b2 pq lq cq pr lr cr : Nat),
      KJ2 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L2 b2 i j v pr lr cr
        (Zv % natVal s.mem mp ml) q ql qc z zl zc' pq lq cq →
      b1 - (dvC zl ml + stkR H S.mem st) + stkR H S'.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hxl : xl ≤ 128 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hml : ml ≤ 128 := hP.2.2.2.2.2.1
  have hml0 : 0 < ml := hP.2.2.2.2.1
  have hs13 : stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
    rw [hk.jc.wc.fr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega)
  obtain ⟨bz, bzc⟩ := hk.bb.bz.1.lt64
  obtain ⟨bzz, bzzc⟩ := hk.bb.bzz.lt64
  have hzl := hk.bb.bz.2.1
  have hzzl := hk.bb.lzz
  have hzlb := hk.zlb
  obtain ⟨-, -, -, -, -, e1d0, e1d8, e1e0, -, e200, -, -, -⟩ := hk.jc.esl
  have bmp := readLE_lt_8 S.mem (sp + 0x1d0)
  have bmc := readLE_lt_8 S.mem (sp + 0x1e0)
  refine runL3 ret0 Q sp z zl zc' zz zzl zzc rr rl rc mp ml mc st S.mem hacc (by omega) hK5 bz (by omega) bzc bzz
    (by omega) bzzc hml0 (by omega) (by omega) (by omega) e1d8 e1d0 e1e0 e200 hk.s160 hk.sf0 hk.se8 S hk.pc hk.jc.esp rfl hk.e0 hk.e3
    hk.e1 hk.e8 hk.e6 hk.e7 ?_
  intro T t1 t4 t14 tfs tx tdf tF trg tra w198 w148 w140 w0 w8 w16 w24 w32 w40 r0 r3 r1 r7 r6 r8 r9
  obtain ⟨uc0, ub0, u168, u100, uf8, u88, ukw⟩ := rdL3 tF (by omega)
  have hz9 : zl ≤ 2 ^ 9 := by omega
  have hs16 : stLen s.mem st + 16 * zl + 64 ≤ 2 ^ 16 := by omega
  have hH' : stLen s.mem st + 16 * zl + 64 ≤ H := by omega
  refine divS hap hns hnf hdv hWK hP hk.jc hk.bb hM hz9 hs16 hH' hcost (idx := 0x765) (by decide) T t1 t4 t14 tfs
    tx tdf tF trg (wsL3_own hK3) ukw tra r0 r3 r1 r7 r6 r8 r9 w0 w8 w16 w24 w32 w40 ?_
  intro s' L2 b2 pq lq cq pr lr cr hpc' hj' hkp e0 e3 e1 e7 e6 e8 hB' hlr hbud
  have hr : ∀ a, sp + 0x68 ≤ a → a + 8 ≤ sp + 0x220 → s'.mem.readLE a 8 = T.mem.readLE a 8 :=
    fun a h1 h2 => hkp a 8 h1 h2
  refine tailL3 (H := H) hP hj' hB' hpc' hk.iy (by omega) hk.jw
    ((hr _ (by omega) (by omega)).trans (uc0.trans hk.sc0)) ((hr _ (by omega) (by omega)).trans (ub0.trans hk.sb0))
    ((hr _ (by omega) (by omega)).trans (u88.trans hk.s88)) ((hr _ (by omega) (by omega)).trans w198)
    ((hr _ (by omega) (by omega)).trans w148) ((hr _ (by omega) (by omega)).trans w140)
    ((hr _ (by omega) (by omega)).trans (u168.trans hk.s168)) ((hr _ (by omega) (by omega)).trans (u100.trans hk.s100))
    ((hr _ (by omega) (by omega)).trans (uf8.trans hk.sf8)) e0 e3 e1 e7 e6 e8 fun S' hk' hst => ?_
  exact KJ S' L2 b2 pq lq cq pr lr cr hk' (by rw [hst]; exact hbud)

end

end FvModexp.Amd64.ExpSlow
