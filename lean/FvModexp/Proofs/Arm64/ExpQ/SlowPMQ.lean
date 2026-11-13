import FvModexp.Proofs.Arm64.ExpQ.SlowSqQ
import FvModexp.Proofs.Arm64.Exp.SlowPM

set_option autoImplicit false

/-! (Q-form copy of Exp/SlowPM.lean, TIGHT COSTS, agent expmc s43)
# `nat.expNNSlow` (arm64): **`segM`** — `KM` (`MV`) → `copy(z, x)` → `KV` (`PV`) (agent expmc)

`runMV`: `z ≠ x` (the destination is apart from `x`: `Loc.ap`), spills `144/136/344`, `memmove(z, x, 8 · len x)`
(`mvCallW`; `WC.mv`), `runMvR` (reloads) → `KV` with `z` a live value `natVal x` (`Mem.Copied`, `x`'s bytes kept by
the frame: `WC.readB`/`oe_bytes`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.ExpSlow


section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`segM`: `KM` → `KV`** (see the module doc) -/
theorem segMQ {impl : List Segment} (hmv : MemmoveLive (LibW.program.link impl) mvE 4096 R)
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) (hxl0 : 0 < xl)
    {ret0 : BitVec 64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 z zc' : Nat}
    (hk : KM R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 z zc')
    (KV' : ∀ S' : State, stCap S'.mem st = stCap S.mem st → KV R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 z zc' →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.2.1
  have hK0 := hP.1.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hwacc := hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxp : xp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hx48 : xp + 8 * xl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxa : s.mem.accessible xp (8 * xl) false = true := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxN : NatNorm s.mem xp xl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxW : Apart xp (8 * xl) (sp - K) (K + 544) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  have hstw : Apart st 24 (sp - K) (K + 544) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hjc := hk.jc
  have hw := hjc.wc
  have hdz := hk.dz
  have hlz := hk.lz
  have c0 : 0 < zc' := by omega
  obtain ⟨c40, hlv, hloc, hob, -⟩ := hdz
  obtain ⟨zal, zH, zacc, z48⟩ := hlv c0
  obtain ⟨zW, zst, -, -, zx, -, -⟩ := Loc.ap hP hloc c0
  have hzx : z ≠ xp := by unfold Apart at zx; omega
  have hacc : S.mem.accessible (sp - 8) 552 true = true := by
    rw [hw.fr.accessible]; exact Memory.accessible_mono _ hwacc (by omega) (by omega)
  refine runMV ret0 Q sp z xl zc' xp S.mem hal hsp2 hacc (by omega) (by omega) (by omega) hxp S hk.pc hjc.esp rfl
    hk.e0 hk.e1 hk.e2 hk.e4 hk.e5 (fun _ _ e => absurd e hzx) ?_
  intro S2 M2 pc2 sp2 _ f0 f1 f2 f30 f18 f28 f29 m2 hF hrg r344 r136 r144
  subst m2
  have hj2 := JC.frameW hP hjc (wsM_in sp) hF hrg (sp2.trans hjc.esp) (f28.trans hjc.e28) (f29.trans hjc.e29)
    (f18.trans hjc.e18)
  have hd2 := DL.frameW hP (wsM_in sp) hF hk.dz
  have hw2 := hj2.wc
  have zacc2 : S2.mem.accessible z (8 * xl) true = true := by
    rw [hF.accessible]; exact Memory.accessible_mono _ zacc (Nat.le_refl _) (by omega)
  have xacc2 : S2.mem.accessible xp (8 * xl) false = true := by
    rw [hw2.fr.accessible]; exact hxa
  refine mvCallW hmv ret0 Q hP hw2 (dst := z) (src := xp) (n := 8 * xl) (ra := mvR) (by decide) (by decide)
    (by omega) (by omega) zacc2 (zH.sub (Nat.le_refl _) (by omega)) (by unfold Apart at zW ⊢; omega) hx48 xacc2 hxW S2
    pc2 hj2.esp hj2.e28 rfl f0 f1 f2 f30 ?_
  intro junk f v m ex ep hF3 hLF3 hinv3 hcp hrg3
  obtain ⟨t1, t28, t29, t18, tpc, tm⟩ := @rsv S2 junk f v m ex ep
  have hdhd : Apart z (8 * xl) st 24 := by unfold Apart at zst ⊢; omega
  have hw3 : WC R L K g sp st zp zc s.mem m L1 b1 (stLen s.mem st) := by
    refine WC.mv hP hw2 hF3 hLF3 hrg3 hinv3 hdhd (fun a k ho => ?_) (fun a k hin ho => ?_)
    · have := Loc.sub (st := st) (m0 := s.mem) hloc a k (by rw [outside_append, outside_append] at ho; exact ho.1.1)
        (by rw [outside_append] at ho; exact ho.2)
      simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    · have := Loc.subL (st := st) (m0 := s.mem) hloc a k hin ho
      simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  have kW : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp + 8 ∨ sp + 32 ≤ a ∧ a + k ≤ sp + 544) →
      m.readLE a k = S2.mem.readLE a k :=
    fun a k ha => mv_rdW hP hF3 ha (by unfold Apart at zW ⊢; omega)
  have hhd3 : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = S2.mem.readLE (st + j) 8 := fun j hj =>
    mv_rdH (K := K) hF3 hLF3 (by omega) (hw2.sok.2.1.sub (by omega) (by omega))
      (by unfold Apart at hstw ⊢; omega) (by unfold Apart at hdhd ⊢; omega)
  have g0 : stW m st = stW S2.mem st := by have := hhd3 0 (by omega); simpa using this
  have g1 : stLen m st = stLen S2.mem st := hhd3 8 (by omega)
  have g2 : stCap m st = stCap S2.mem st := hhd3 16 (by omega)
  have hd3 := hd2.hdr g0 g1 g2 hF3.accessible
  have hsf3 : SF sp st xp xl xc yp yl mp ml mc r29 ret m := hj2.sf.keep fun a k ha => kW a k (by omega)
  have hacc3 : m.accessible (sp - 8) 552 true = true := by
    rw [hF3.accessible, hw2.fr.accessible]; exact Memory.accessible_mono _ hwacc (by omega) (by omega)
  refine runMvR ret0 Q sp z xl zc' st yp yl m hal hsp2 hacc3 ((kW _ _ (by omega)).trans r344)
    ((kW _ _ (by omega)).trans r136) ((kW _ _ (by omega)).trans r144) hsf3.s464 hsf3.s496 hsf3.s504 _
    (by rw [tpc, f30]) (t1.trans hj2.esp) tm ?_
  intro S3 pc3 sp3 m3 e0 e5 e2 e3 e7 e8 e18 e28 e29
  have hv : natVal S3.mem z xl = natVal s.mem xp xl := by
    show S3.mem.readLE z (8 * xl) = s.mem.readLE xp (8 * xl)
    rw [m3, FvModexp.Expmc.readLE_of_copied hcp]
    have := x_rd hP hw2 (j := 0) (k := 8 * xl) (by omega)
    simpa using this
  have hn : NatNorm S3.mem z xl := by
    rcases hxN with e | hne0
    · exact Or.inl e
    · right
      rw [m3, FvModexp.Expmc.readLE_of_copied (cp_subS hcp (j := 8 * (xl - 1)) (k := 8) (by omega)),
        x_rd hP hw2 (by omega)]
      exact hne0
  rw [← m3] at hw3 hsf3 hd3
  refine KV' S3 (by rw [m3, g2]; exact capW hP (wsM_in sp) hF) ⟨pc3, ⟨hw3, rfl, sp3.trans (t1.trans hj2.esp), e28.trans (t28.trans hj2.e28),
    e29.trans (t29.trans hj2.e29), e18.trans (t18.trans hj2.e18), hsf3⟩, ⟨hd3, hlz, hv, hn⟩, e0, e5, e2, e3,
    e7, e8⟩

end

end FvModexp.Arm64.Q.ExpSlow
