import FvModexp.Proofs.Amd64.Exp.SlowJ

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): **`segM`** — `KS` (`setJ`) → `KV` (`aSet`): `copy(z, x)` (agent expmc s79; twin of arm64
`SlowPM`)

`runJ` (`z`'s array is never `x`'s: both are non-empty and apart, so the same-pointer branch is dead), the spills
`FM sp`, `memmove(z, x, 8·len x)` (`mvCall`, `WC.mv`), `runMv`; `z`'s value = `x`'s (`readLE_of_copied`, `x_rd`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

/-- a destination through a step keeping the stack header and accessibility (same live set) -/
theorem DL.hdr {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M M' : Memory} {L1 : List (Nat × Nat)}
    {p c : Nat} (h : DL R L st zp zc M L1 p c) (e0 : stW M' st = stW M st) (e1 : stLen M' st = stLen M st)
    (e2 : stCap M' st = stCap M st) (hacc : ∀ a n w, M'.accessible a n w = M.accessible a n w) :
    DL R L st zp zc M' L1 p c := by
  obtain ⟨c40, hlv, hloc, hob, h0⟩ := h
  refine ⟨c40, fun hc => ?_, hloc, fun hc => ?_, h0⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hlv hc
    exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  · obtain ⟨o1, o2, o3⟩ := hob hc
    refine ⟨o1, ?_, ?_⟩
    · show Apart p (8 * c) (stW M' st + 8 * stLen M' st) (8 * (stCap M' st - stLen M' st))
      rw [e0, e1, e2]; exact o2
    · show InRanges (stW M' st) (8 * stCap M' st) R.rt → ApartAll (stW M' st) (8 * stCap M' st) L →
        Apart p (8 * c) (stW M' st) (8 * stCap M' st)
      rw [e0, e2]; exact o3

theorem cp_subS {m0 m : Memory} {d s n j k : Nat} (h : Mem.Copied m0 m d s n) (hj : j + k ≤ n) :
    Mem.Copied m0 m (d + j) (s + j) k := fun i hi => by
  have := h (j + i) (by omega)
  rw [← Nat.add_assoc, ← Nat.add_assoc] at this
  exact this

theorem rsv {T : State} {junk : Nat → W64} {f : Flags} {x yh : Nat → BitVec 128} {m : Memory}
    {zh : Nat → BitVec 256} {kr : Nat → W64} :
    (retState64 T junk [] f x yh m zh kr).regs 4 = T.regs 4 + 8#64 ∧
      (retState64 T junk [] f x yh m zh kr).regs 14 = T.regs 14 ∧
      (retState64 T junk [] f x yh m zh kr).fsBase = T.fsBase ∧
      (retState64 T junk [] f x yh m zh kr).xmm 15 = T.xmm 15 ∧
      (retState64 T junk [] f x yh m zh kr).df = T.df ∧
      (retState64 T junk [] f x yh m zh kr).rip = retAddrOf T ∧
      (retState64 T junk [] f x yh m zh kr).mem = m := by
  simp [retState64, callRegs64_apply]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)}
    {K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- the bytes of `x` at a context memory are the entry's -/
theorem x_rd (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) {j k : Nat}
    (hjk : j + k ≤ 8 * xl) : M.readLE (xp + j) k = s.mem.readLE (xp + j) k := by
  have hxO : OE R L sp K st s.mem xp (8 * xl) := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb := oe_bytes hP hxO (fun hc => (hP.zF hc).2.2.2.2.2.2.1)
  exact h.readB (hxO.1.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega)))
    fun i hi => by rw [Nat.add_assoc]; exact hb (j + i) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`segM`: `KS` → `KV`** (see the module doc) -/
theorem segM {impl : List Amd64.Segment} (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hmz : MemmoveZeroLive64 (LibW.program.link impl) mvE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s) (hxl0 : 0 < xl)
    {ret0 : W64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 pZ cZ : Nat}
    (hk : KS R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S L1 b1 pZ cZ)
    (KV' : ∀ S' : State, KV R L K g fs sp st bp r zp zc xp xl xc yp yl yc mp ml mc s S' L1 b1 pZ cZ →
      stCap S'.mem st = stCap S.mem st → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := hP.kf
  have hsp64 : sp < 2 ^ 64 := by omega
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxp : xp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hx48 : xp + 8 * xl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxa : s.mem.accessible xp (8 * xl) false = true := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxN : NatNorm s.mem xp xl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxW : Apart xp (8 * xl) (sp - 8 - K) (K + 0x228) := hP.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  obtain ⟨hstw, -⟩ := hP.stkF
  have hwacc := hP.cenv0.2.2.2.1
  have hjc := hk.jc
  have hw := hjc.wc
  have hdz := hk.dz
  have hlz := hk.lz
  have c0 : 0 < cZ := by omega
  obtain ⟨c40, hlv, hloc, hob, -⟩ := hdz
  obtain ⟨zal, zH, zacc, z48⟩ := hlv c0
  obtain ⟨zW, zst, -, -, zx, -, -⟩ := Loc.ap hP hloc c0
  have hzx : pZ ≠ xp := by unfold Apart at zx; omega
  have hacc : S.mem.accessible (sp - 8) 0x228 true = true := by
    rw [hw.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
  refine runJ ret0 Q sp st xp xl xc pZ cZ S.mem hacc (by omega) hK5 hxp (by omega) (by omega) (by omega) S hk.pc
    hjc.esp rfl hk.r0 hk.r1 hk.r2 hk.r8 hk.r6 (fun _ _ _ e => absurd e hzx) ?_
  intro S2 M2 pc2 sp2 _ f0 f3 f1 f14 ffs fx fdf m2 hF hrg r8 r80 r138 r158
  subst m2
  obtain ⟨hw2, hdl2, -⟩ := WC.own hP hw hF hrg (fun q hq => by
    simp only [FM, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp only [OwnR] <;> omega)
  have hd2 := hdl2 _ _ hk.dz
  have kF : ∀ a k, sp + 0x1a8 ≤ a → a + k ≤ sp + 0x220 → S2.mem.readLE a k = S.mem.readLE a k := fun a k h1 h2 =>
    hF.readLE a k (by simp only [FM, outside_cons, outside_nil, and_true]; omega)
  have zacc2 : S2.mem.accessible pZ (8 * xl) true = true := by
    rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_mono _ zacc (Nat.le_refl _) (by omega)
  have xacc2 : S2.mem.accessible xp (8 * xl) false = true := by
    rw [hw2.fr.accessible]; exact hxa
  refine mvCall hmv hmz hP hw2 (d := pZ) (src := xp) (n := 8 * xl) (by omega) (by omega) hxp
    (Or.inr ⟨hx48, xacc2, hxW, by omega, zacc2, zH.sub (Nat.le_refl _) (by omega),
      by unfold Apart at zW ⊢; omega⟩) S2 pc2 sp2 (f14.trans hjc.e14) rfl (by rw [r8]; decide)
    (fx.trans hjc.ex15) (fdf.trans hjc.edf) f0 f3 f1 ?_
  intro junk f x yh m zh kr dd hdd hF3 hLF3 hinv3 hcp hrg3
  obtain rfl : dd = pZ := by rcases hdd with ⟨h1, -⟩ | ⟨-, h2⟩ <;> omega
  obtain ⟨t4, t14, tfs, tx, tdf, tpc, tm⟩ := @rsv S2 junk f x yh m zh kr
  have hdhd : Apart dd (8 * xl) st 24 := by unfold Apart at zst ⊢; omega
  have hw3 : WC R L K g sp st zp zc s.mem m L1 b1 (stLen s.mem st) := by
    refine WC.mv hP hw2 hF3 hLF3 hrg3 hinv3 hdhd (fun a k ho => ?_) (fun a k hin ho => ?_)
    · have := Loc.sub (st := st) (m0 := s.mem) hloc a k (by rw [outside_append, outside_append] at ho; exact ho.1.1)
        (by rw [outside_append] at ho; exact ho.2)
      simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
    · have := Loc.subL (st := st) (m0 := s.mem) hloc a k hin ho
      simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  have kW : ∀ a k, (sp - 8 ≤ a ∧ a + k ≤ sp ∨ sp + 24 ≤ a ∧ a + k ≤ sp + 0x220) →
      m.readLE a k = S2.mem.readLE a k :=
    fun a k ha => mv_rdW hP hF3 ha (by unfold Apart at zW ⊢; omega)
  have hhd3 : ∀ j, j + 8 ≤ 24 → m.readLE (st + j) 8 = S2.mem.readLE (st + j) 8 := fun j hj =>
    mv_rdH (K := K) hF3 hLF3 (by omega) (hw2.sok.2.1.sub (by omega) (by omega))
      (by unfold Apart at hstw ⊢; omega) (by unfold Apart at hdhd ⊢; omega)
  have g0 : stW m st = stW S2.mem st := by have := hhd3 0 (by omega); simpa using this
  have g1 : stLen m st = stLen S2.mem st := hhd3 8 (by omega)
  have g2 : stCap m st = stCap S2.mem st := hhd3 16 (by omega)
  have hd3 := hd2.hdr g0 g1 g2 hF3.accessible
  have hacc3 : m.accessible (sp - 8) 0x228 true = true := by
    rw [hF3.accessible, hw2.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hwacc (by omega) (by omega)
  have hsl3 := hjc.esl.keep (fun a k ha => (kW a k (Or.inr (by simp only [SlotR] at ha; omega))).trans
    (kF a k (by simp only [SlotR] at ha; omega) (by simp only [SlotR] at ha; omega)))
  refine runMv ret0 Q sp st xp xl xc dd cZ m hacc3 (by omega) hK5 hsl3.2.2.2.2.2.2.2.2.2.1
    hsl3.2.2.2.2.2.2.2.2.2.2.1 hsl3.2.2.2.2.2.2.2.2.2.2.2.1 hsl3.2.2.2.2.2.2.2.2.2.2.2.2
    ((kW _ 8 (Or.inr ⟨by omega, by omega⟩)).trans r80) ((kW _ 8 (Or.inr ⟨by omega, by omega⟩)).trans r138)
    ((kW _ 8 (Or.inr ⟨by omega, by omega⟩)).trans r158) _
    (by rw [tpc, ra_eq (ra := mvR) sp2 hsp64 r8]) (by rw [t4, sp2, bv_add8 (by omega) hsp64]) tm ?_
  intro S3 pc3 sp3 m3 e0 e1 e2 e10 e6 e7 e9 e14 efs ex edf
  have hv : natVal S3.mem dd xl = natVal s.mem xp xl := by
    show S3.mem.readLE dd (8 * xl) = s.mem.readLE xp (8 * xl)
    rw [m3, FvModexp.Expmc.readLE_of_copied hcp]
    have := x_rd hP hw2 (j := 0) (k := 8 * xl) (by omega)
    simpa using this
  have hn : NatNorm S3.mem dd xl := by
    rcases hxN with e | hne0
    · exact Or.inl e
    · right
      rw [m3, FvModexp.Expmc.readLE_of_copied (cp_subS hcp (j := 8 * (xl - 1)) (k := 8) (by omega)),
        x_rd hP hw2 (by omega)]
      exact hne0
  have hj3 := hjc.call (S' := S3) (sp3.trans hjc.esp.symm) (e14.trans (t14.trans f14))
    (efs.trans (tfs.trans ffs)) (ex.trans (tx.trans fx)) (edf.trans (tdf.trans fdf)) (by rw [m3]; exact hw3)
    (fun a k h1 h2 => by rw [m3]; exact (kW a k (Or.inr ⟨by omega, h2⟩)).trans (kF a k h1 h2))
  rw [← m3] at hd3
  have ecap2 : stCap S2.mem st = stCap S.mem st := by
    unfold Apart at hstw
    exact hF.readLE _ _ (by simp only [FM, outside_cons, outside_nil, and_true]; omega)
  exact KV' S3 ⟨hj3, pc3, ⟨hd3, hlz, hv, hn⟩, e0, e1, e2, e10, e6, e7, e9⟩ (by rw [m3, g2]; exact ecap2)

end

end FvModexp.Amd64.ExpSlow
