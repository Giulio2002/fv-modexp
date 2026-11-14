import FvModexp.Proofs.Amd64.Exp.P2W4R1
import FvModexp.Proofs.Amd64.Exp.P2W4Seg
import FvModexp.Proofs.Amd64.Exp.P2W4Al

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): `return 1` with a fresh one-word array (nat.go:1187-1192, nat.go:58-76)
(agent divmc s76, port of divmc s70; amd64 twin of agent infra's `Arm64.P2W4R1b`)

* `r1b`: `z ≠ nil`, `cap z = 0`: `makeslice(Word, 1, 1)` (CALL at +0x354, return +0x359), `[0] = 1` at +0x361 → `tS`;
* `r1c`: `z == nil`: `newobject([1]Word)` (CALL at +0x379, return +0x37e), `[0] = 1` at +0x37e → `tN`;
* `r1all`: the three shapes from `r1E`.
`wc_push`: `WC`/`ESl` through a `CALL`'s return-address push at `sp - 0x8`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

open FvModexp.Amd64.ExpHyp

/-- an opaque wrapper (keeps big facts out of `janus64_run`'s context splitting) -/
structure Hd (P : Prop) : Prop where
  h : P

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 ℓ H : Nat}

/-- `WC` and `ESl` through the return-address push of a `CALL` from `RSP = sp` -/
theorem wc_push (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ) (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st))
    (v : Nat) :
    WC R H L K g sp st zp zc s.mem (M.writeLE (sp - 0x8) 8 v) L1 b1 ℓ ∧
      ESl (M.writeLE (sp - 0x8) 8 v) sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st) := by
  have hce := h.cenv hP
  have hK0 : K ≤ sp - 0x8 := hce.2.1
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hwr : MemFrame M (M.writeLE (sp - 0x8) 8 v) [(sp - 0x8, sp)] := by janus_frame
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  have hrt := hP.win_rt
  have hLs := hP.cenv0.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  refine ⟨h.frame hwr (by simp only [Janus.Arm64.Memory.regions_writeLE]) (fun a k ho => ?_) (fun a k hin _ => ?_)
      (by simp only [outside_cons, outside_nil, and_true]; omega) (fun q hq => Or.inr ?_),
    ESl.keep hsl fun a k ha => hwr.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)⟩
  · simp only [WN, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega
  · obtain ⟨q, hq, q1, q2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this ⊢; omega
  · simp only [List.mem_singleton] at hq; subst hq; dsimp only
    exact hrt.of_sub (by omega) (by omega)

/-- after a fresh allocation of `[p, p + r)` and `[p] = 1`: the context, the slots and the one-word result -/
theorem fresh1 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) {M0 m : Memory} {p rr : Nat}
    (hA : AllocR R H L K g sp st zp zc s.mem M0 L1 b1 ℓ m p rr 8) (hle : LiveExt R L L1)
    (hsl : ESl M0 sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) :
    WC R H L K g sp st zp zc s.mem (m.writeLE p 8 1) (L1 ++ [(p, p + rr)]) (b1 - rr) ℓ ∧
      ESl (m.writeLE p 8 1) sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st) ∧
      NatOF R L (L1 ++ [(p, p + rr)]) (m.writeLE p 8 1) zp zc 1 p 1 1 1 := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hout := hP.win_rt
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  have hpw := hA.rin.apart hout
  have hsz := hA.sz
  unfold Apart at hpw hstw
  have hF1 : MemFrame m (m.writeLE p 8 1) [(p, p + 8)] :=
    (MemFrame.refl _ _).writeLE_inRanges _ ⟨(p, p + 8), by simp, by simp only; omega, by simp only; omega⟩
  have hin2 : InRanges p 8 (L1 ++ [(p, p + rr)]) :=
    ⟨(p, p + rr), by simp, by simp only; omega, by simp only; omega⟩
  have hapL : ApartAll p rr L := fun q hq => hA.rap q (hle.mem_old hq)
  have hsok0 := hP.stk0
  have hhdA : Apart p rr st 24 := by
    rcases hsok0.2.1 with hL0 | hO0
    · have := hapL.apart_of_inRanges hL0; unfold Apart; omega
    · exact (hA.rin.apart hO0).symm
  unfold Apart at hhdA
  have hws : InRanges p 8 R.rt := hA.rin.sub (Nat.le_refl _) (by omega)
  refine ⟨hA.wc.frame hF1 (by simp only [Janus.Arm64.Memory.regions_writeLE]) (fun a k ho => ?_)
      (fun a k hin _ => ?_) ?_ ?_,
    ESl.keep hsl (fun a k ha => by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hA.keep a k (by omega)), ?_⟩
  · rw [outside_append, outside_append] at ho
    have := hA.rin.apart ho.1.1
    unfold Apart at this
    simp only [outside_cons, outside_nil, and_true]; omega
  · have := hapL.apart_of_inRanges hin
    simp only [outside_cons, outside_nil, and_true]; omega
  · simp only [outside_cons, outside_nil, and_true]; omega
  · intro q hq; simp only [List.mem_singleton] at hq; subst hq; simp only
    rw [show p + 8 - p = 8 by omega]; exact Or.inl hin2
  · refine ⟨?_, Or.inr ?_, Nat.le_refl _, by decide, fun _ => ⟨hA.al, Or.inl hin2, ?_, by have := hA.b48; omega⟩,
      Or.inr ⟨Nat.le_refl _, hws, fun q hq => ?_⟩⟩
    · show (m.writeLE p 8 1).readLE p (8 * 1) = 1
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
    · rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Janus.Arm64.Memory.readLE_writeLE_self]; decide
    · simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact Janus.Arm64.Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by omega)
    · have := hapL q hq; unfold Apart at this ⊢; omega

/-- `ResSep` for the fresh one-word result -/
theorem rs_fresh1 (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (hw : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    {m : Memory} {p rr : Nat} (hA : AllocR R H L K g sp st zp zc s.mem M L1 b1 ℓ m p rr 8) :
    ResSep s.mem (m.writeLE p 8 1) st p 1 := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  have hsz := hA.sz
  have hsok := hw.sok
  have hst : Apart p rr st 24 := by
    rcases hsok.2.1 with hL | hO
    · have := hA.rap.apart_of_inRanges hL; unfold Apart; omega
    · exact (hA.rin.apart hO).symm
  unfold Apart at hstw hst
  have hh : ∀ j, j + 8 ≤ 24 → (m.writeLE p 8 1).readLE (st + j) 8 = M.readLE (st + j) 8 := fun j hj => by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hA.rdH _ _ (hsok.2.1.sub (by omega) (by omega)) (by unfold Apart; omega)
  have e0 : stW (m.writeLE p 8 1) st = stW M st := by have := hh 0 (by omega); simpa using this
  have e2 : stCap (m.writeLE p 8 1) st = stCap M st := hh 16 (by omega)
  exact (rs_live hw (p := p) (c := 1) (ApartAll.sub' hA.rap (Nat.le_refl _) (by omega))).congr e0 e2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `z ≠ nil`, `cap z = 0`: `makeslice(Word, 1, 1)`, `[0] = 1` -/
theorem r1b {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hw : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) {cst : Nat}
    (hbc : allocCost 8 ≤ b1) (hb : b - cst ≤ b1 - allocCost 8) (hzp : zp ≠ 0) (hzc : zc = 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 r1E) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = s.fsBase) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hm : S.mem = M) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FQ R b L K zp zc st 1 cst s) := by
  have hzp64 : zp < 2 ^ 64 := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hwacc : M.accessible (sp - 0x8 - K) (K + 0x360) true = true := (hw.cenv hP).2.2.2.1
  have hwaccF : M.accessible (sp - 0x8 - K) (K + 0x360) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  obtain ⟨hw1, hsl1⟩ := wc_push hP hw hsl 6198826
  have hsl0 := hsl
  obtain ⟨-, -, -, -, -, -, r1f0, r200, -⟩ := hsl
  have hz0 : ¬ (zp = 0) := hzp
  have hrd : (M.writeLE (sp - 0x8) 8 6198826).readLE (sp - 0x8) 8 = 6198826 := Janus.Arm64.Memory.readLE_writeLE_self ..
  have hbs : blockSize (8 * 1) true ≤ b1 := Nat.le_trans (blockSize_le_allocCost 8 true) hbc
  subst hm hzc
  have hwH : Hd (WC R H L K g sp st zp 0 s.mem (S.mem.writeLE (sp - 0x8) 8 6198826) L1 b1 ℓ) := ⟨hw1⟩
  have hsH : Hd (ESl (S.mem.writeLE (sp - 0x8) 8 6198826) sp st bp r zp 0 xp xl xc yp yl lm
    (stLen s.mem st)) := ⟨hsl1⟩
  have hwH0 : Hd (WC R H L K g sp st zp 0 s.mem S.mem L1 b1 ℓ) := ⟨hw⟩
  clear hw1 hsl1 hsl0 hw
  refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 mkE) ?_
  janus64_run [r1f0, r200, hwaccF, hz0] until [mkE]
  refine mkCall hmk hP hwH.h (n := 1) (c := 1) (by decide) (by decide) (by decide) hbs _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun ptr junk f x yh m zh kr hA => ?_)
  all_goals first | (janus64_simp; done) | skip
  case refine_2 =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  obtain ⟨hw', hsl', hres⟩ := fresh1 hP hA hwH.h.le hsH.h
  have hrs := rs_fresh1 hP hwH.h hA
  have hacc1 : m.accessible ptr.toNat 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by have := hA.sz; omega)
  have hb48 := hA.b48
  have hsz := hA.sz
  have hrc : blockSize (8 * 1) true ≤ allocCost 8 := hA.rc
  have hpl := ptr.isLt
  clear hA hwH hsH hwH0
  refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 tS) ?_
  janus64_run [hacc1] until [tS]
  refine ReachesRet.mono (tailS hap _ sp g st (stLen s.mem st) bp r ptr.toNat 1 s.fsBase (m.writeLE ptr.toNat 8 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by decide) (by decide) hpl ?_ ?_ (by omega) (tenv_of hP hw' hsl'))
    (fun s' ht => finQ hP hw' hres hrs (by omega) ht)
  all_goals first
    | exact hfs
    | (simp only [Janus.Arm64.Memory.accessible_writeLE]; exact Janus.Arm64.Memory.accessible_weaken _ hacc1)
    | janus64_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `z == nil`: `newobject([1]Word)`, `[0] = 1` -/
theorem r1c {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (hno : NewobjectLiveContract64 (LibW.program.link impl) noE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hw : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) {cst : Nat}
    (hbc : allocCost 8 ≤ b1) (hb : b - cst ≤ b1 - allocCost 8) (hzp : zp = 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 r1E) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = s.fsBase) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hm : S.mem = M) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FQ R b L K zp zc st 1 cst s) := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hwacc : M.accessible (sp - 0x8 - K) (K + 0x360) true = true := (hw.cenv hP).2.2.2.1
  have hwaccF : M.accessible (sp - 0x8 - K) (K + 0x360) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  obtain ⟨hw1, hsl1⟩ := wc_push hP hw hsl 6198865
  have hsl0 := hsl
  obtain ⟨-, -, -, -, -, -, r1f0, -⟩ := hsl
  have hbs : blockSize 8 true ≤ b1 := Nat.le_trans (blockSize_le_allocCost 8 true) hbc
  subst hm hzp
  have hwH : Hd (WC R H L K g sp st 0 zc s.mem (S.mem.writeLE (sp - 0x8) 8 6198865) L1 b1 ℓ) := ⟨hw1⟩
  have hsH : Hd (ESl (S.mem.writeLE (sp - 0x8) 8 6198865) sp st bp r 0 zc xp xl xc yp yl lm
    (stLen s.mem st)) := ⟨hsl1⟩
  have hwH0 : Hd (WC R H L K g sp st 0 zc s.mem S.mem L1 b1 ℓ) := ⟨hw⟩
  clear hw1 hsl1 hsl0 hw
  refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 noE) ?_
  janus64_run [r1f0, hwaccF] until [noE]
  refine noCall hno hP hwH.h hbs _ ?_ ?_ ?_ ?_ ?_ ?_ (fun ptr junk f x yh m zh kr hA _ => ?_)
  all_goals first | (janus64_simp; done) | skip
  case refine_2 =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  obtain ⟨hw', hsl', hres⟩ := fresh1 hP hA hwH.h.le hsH.h
  have hrs := rs_fresh1 hP hwH.h hA
  have hacc1 : m.accessible ptr.toNat 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hA.acc (Nat.le_refl _) (by have := hA.sz; omega)
  have hb48 := hA.b48
  have hsz := hA.sz
  have hrc : blockSize 8 true ≤ allocCost 8 := hA.rc
  have hpl := ptr.isLt
  clear hA hwH hsH hwH0
  refine SegProg.lift P2W4Seg.codeIn (r := BitVec.ofNat 64 tN) ?_
  janus64_run [hacc1] until [tN]
  refine ReachesRet.mono (tailN hap _ sp g st (stLen s.mem st) bp r ptr.toNat s.fsBase (m.writeLE ptr.toNat 8 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hpl (tenv_of hP hw' hsl'))
    (fun s' ht => finQ hP hw' hres hrs (by omega) ht)
  all_goals first
    | exact hfs
    | janus64_simp

/-- **`return 1`** from `r1E` (all three shapes) -/
theorem r1all {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    (hno : NewobjectLiveContract64 (LibW.program.link impl) noE 4096 R)
    (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s) (hw : WC R H L K g sp st zp zc s.mem M L1 b1 ℓ)
    (hsl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) {cst : Nat}
    (hbc : allocCost 8 ≤ b1) (hb : b - cst ≤ b1 - allocCost 8)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 r1E) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = s.fsBase) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hm : S.mem = M) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (FQ R b L K zp zc st 1 cst s) := by
  by_cases hzp : zp = 0
  · exact r1c hap hno hP hw hsl hbc hb hzp S hpc hsp h14 hfs hx15 hdf hm
  by_cases hzc : zc = 0
  · exact r1b hap hmk hP hw hsl hbc hb hzp hzc S hpc hsp h14 hfs hx15 hdf hm
  · exact r1a hap hP hw hsl (by omega) hzp (by omega) S hpc hsp h14 hfs hx15 hdf hm

end

end FvModexp.Amd64.P2W4
