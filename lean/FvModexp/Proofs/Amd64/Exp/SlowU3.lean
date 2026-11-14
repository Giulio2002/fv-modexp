import FvModexp.Proofs.Amd64.Exp.SlowDv
import FvModexp.Proofs.Amd64.Exp.SlowU3R

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): upper-loop segment U3 — `KD1` → `zz, r = zz.div(stk, r, z, m)` → `KJ1` (agent expmc s81;
twin of arm64 `SlowU3Q`)

`runU3` (the `len m = 0` branch is dead: `0 < len m`), `divS` (return `dv1R`), `runU3b` (rotation
`zz, r, q, z = q, z, zz, r`; the old `z`'s pointer stored to `[0x160]`) → `j1`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

theorem wsU3_own {sp K : Nat} (hK : K + 8 ≤ sp) : ∀ r ∈ wsU3 sp, OwnR sp K r := by
  intro r hr
  simp only [wsU3, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp only [OwnR] <;> omega

/-- the slots U3's stores keep -/
theorem rdU3 {m m' : Memory} {sp : Nat} (hF : MemFrame m m' (wsU3 sp)) (h8 : 8 ≤ sp) :
    (∀ a k, sp + 0x30 ≤ a → a + k ≤ sp + 0x108 → m'.readLE a k = m.readLE a k) ∧
    (∀ a k, sp + 0x118 ≤ a → a + k ≤ sp + 0x178 → m'.readLE a k = m.readLE a k) ∧
    (∀ a k, sp + 0x180 ≤ a → a + k ≤ sp + 0x220 → m'.readLE a k = m.readLE a k) := by
  refine ⟨fun a k h1 h2 => hF.readLE _ _ ?_, fun a k h1 h2 => hF.readLE _ _ ?_, fun a k h1 h2 => hF.readLE _ _ ?_⟩ <;>
  simp only [wsU3, outside_cons, outside_nil, and_true] <;> omega

theorem rd160U {m m' : Memory} {sp : Nat} (hF : MemFrame m m' [(sp + 0x160, sp + 0x168)]) :
    ∀ a k, (a + k ≤ sp + 0x160 ∨ sp + 0x168 ≤ a) → m'.readLE a k = m.readLE a k := fun a k h =>
  hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)

/-- `BB` through stores that keep every destination / live local -/
theorem BB.tr {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M M' : Memory} {L1 : List (Nat × Nat)}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hdl : ∀ q c, DL R L st zp zc M L1 q c → DL R L st zp zc M' L1 q c)
    (hln : ∀ q l c v, LN R L st zp zc M L1 q l c v → LN R L st zp zc M' L1 q l c v)
    (h : BB R L st zp zc M L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc) :
    BB R L st zp zc M' L1 z zl zc' Zv zz zzl zzc rr rl rc q ql qc :=
  ⟨hln _ _ _ _ h.bz, hdl _ _ h.bzz, h.lzz, hdl _ _ h.br, h.lr, hdl _ _ h.bq, h.lq, h.p1, h.p2, h.p3, h.p4, h.p5,
    h.p6⟩

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **U3**: `KD1` → `KJ1` (the division) -/
theorem segU3 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {W H : Nat} {dvC : Nat → Nat → Nat} (hdv : DivHypLGQ impl R ns W 0x70 dvC) (hWK : W ≤ K)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hM : 0 < natVal s.mem mp ml)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 j w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc rr rl rc q ql qc : Nat}
    (hk : KD1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 j w v z zl zc' Zv zz zzl zzc
      rr rl rc q ql qc)
    (hH : stLen s.mem st + 48 * max xl ml + 64 ≤ H) (hcost : dvC zl ml + stkR H S.mem st ≤ b1)
    (KJ : ∀ (S' : State) (L2 : List (Nat × Nat)) (b2 pq lq cq pr lr cr : Nat),
      KJ1 R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L2 b2 j w v pr lr cr
        (Zv % natVal s.mem mp ml) q ql qc z zl zc' pq lq cq →
      b1 - (dvC zl ml + stkR H S.mem st) + stkR H S'.mem st ≤ b2 → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hxl : xl ≤ 128 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hml8 : ml ≤ 128 := hP.2.2.2.2.2.1
  have hml0 : 0 < ml := hP.2.2.2.2.1
  have hs13 : stLen s.mem st + 2 ^ 13 ≤ 2 ^ 16 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmP := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, bmp, bmc, -⟩ := hmP
  have hacc : ∀ M : Memory, (∀ a n w, M.accessible a n w = s.mem.accessible a n w) →
      M.accessible (sp - 8) 0x228 true = true := fun M hM => by
    rw [hM]; exact Janus.Arm64.Memory.accessible_mono _ hP.cenv0.2.2.2.1 (by omega) (by omega)
  have hzlb := hk.zlb
  obtain ⟨bz, bzc⟩ := hk.bb.bz.1.lt64
  have hzlc := hk.bb.bz.2.1
  obtain ⟨-, -, -, -, -, sl1d0, sl1d8, sl1e0, -, sl200, -, -, -⟩ := hk.jc.esl
  refine runU3 ret0 Q sp z zl zc' zz zzl zzc rr rl rc mp ml mc st S.mem (hacc _ hk.jc.wc.fr.accessible) (by omega)
    hK5 bz (by omega) bzc bmp (by omega) bmc hml0 sl1d8 sl1d0 sl1e0 sl200 hk.s160 hk.s90 hk.s98 S hk.pc hk.jc.esp rfl
    hk.e0 hk.e3 hk.e1 hk.e8 hk.e6 hk.e7 ?_
  intro T tpc t4 t14 tfs tx tdf tF trg tra w178 w110 w108 y0 y1 y2 y3 y4 y5 r0 r3 r1 r7 r6 r8 r9
  obtain ⟨uA, uB, uC⟩ := rdU3 tF (by omega)
  refine divS hap hns hnf hdv hWK hP hk.jc hk.bb hM (by omega) (by omega) (by omega) hcost (idx := 0x44a)
    (by decide) T tpc t4 t14 tfs tx tdf tF trg (wsU3_own hK3) (fun a k h1 h2 => uC a k (by omega) h2) tra
    r0 r3 r1 r7 r6 r8 r9 y0 y1 y2 y3 y4 y5 ?_
  intro s' L2 b2 pq lq cq pr lr cr hpc' hj' hkp e0 e3 e1 e7 e6 e8 hB' hlr hbud
  have rA : ∀ a, sp + 0x68 ≤ a → a + 8 ≤ sp + 0x108 → s'.mem.readLE a 8 = S.mem.readLE a 8 :=
    fun a h1 h2 => (hkp a 8 h1 (by omega)).trans (uA a 8 (by omega) h2)
  have rB : ∀ a, sp + 0x118 ≤ a → a + 8 ≤ sp + 0x178 → s'.mem.readLE a 8 = S.mem.readLE a 8 :=
    fun a h1 h2 => (hkp a 8 (by omega) (by omega)).trans (uB a 8 h1 h2)
  refine runU3b ret0 Q sp zl zc' z q ql qc v s'.mem (hacc _ hj'.wc.fr.accessible) (by omega) hK5 bz
    ((rA _ (by omega) (by omega)).trans hk.s88) ((hkp _ 8 (by omega) (by omega)).trans w110)
    ((hkp _ 8 (by omega) (by omega)).trans w108) ((hkp _ 8 (by omega) (by omega)).trans w178)
    ((rB _ (by omega) (by omega)).trans hk.s168) ((rA _ (by omega) (by omega)).trans hk.sa0)
    ((rA _ (by omega) (by omega)).trans hk.sa8) s' hpc' hj'.esp rfl ?_
  intro T2 t2pc t24 t2F t2rg w160 t20 t23 t21 t215 t211 t29 t28 t26 t27 t212 t213 t22 t214 t2fs t2x t2df
  obtain ⟨hw2, hdl2, hln2⟩ := WC.own hP hj'.wc t2F t2rg (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; simp only [OwnR]; omega)
  have k160 := rd160U t2F
  have hj2 := hj'.call (S' := T2) (t24.trans hj'.esp.symm) t214 t2fs t2x t2df hw2
    (fun a k h1 _ => k160 a k (Or.inr (by omega)))
  obtain ⟨hstw, -⟩ := hP.stkF
  unfold Apart at hstw
  have hcap : stCap T2.mem st = stCap s'.mem st := k160 _ _ (by omega)
  have r2 : ∀ a, (a + 8 ≤ sp + 0x160 ∨ sp + 0x168 ≤ a) → T2.mem.readLE a 8 = s'.mem.readLE a 8 :=
    fun a h => k160 a 8 h
  refine KJ T2 L2 b2 pq lq cq pr lr cr ⟨hj2, BB.tr hdl2 hln2 hB', hk.w63,
    (r2 _ (by omega)).trans ((rB _ (by omega) (by omega)).trans hk.s138), t2pc, by omega, hk.jw,
    t20.trans e7, t23.trans e6, t21.trans e8, t28, t26, t27, t215.trans e0, t211.trans e3, t29.trans e1, w160,
    t212, t213, t22, (r2 _ (by omega)).trans ((rA _ (by omega) (by omega)).trans hk.sb8)⟩ ?_
  rw [stkR_congr hcap]
  exact hbud

end

end FvModexp.Amd64.ExpSlow
