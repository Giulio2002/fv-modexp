import FvModexp.Proofs.Amd64.Exp.SubMod2NGL
import FvModexp.Proofs.Amd64.Nat.TruncDefs
import FvModexp.Proofs.Common.Util

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64), general form: callee calls on `LibW` (`trunc` on `Trunc.Hyp2`, empty-tolerant `sub` on
`SubHypR0`, `add` on `AddHypR`, `cmp`), callee preconditions, and the postcondition (agent infra s48; twin of
Arm64/Exp/SubMod2NGC.lean + the `LibW` call helpers of Arm64/Exp/SubMod2NBase.lean)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

/-! ## Calls on `LibW` -/

/-- asm's verified `nat.cmp` in `LibW` (as expmc's `W4ExB.cmpSum`, copied to keep this module off the window chain) -/
theorem cmpSumW (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    Summary (LibW.program.link impl) 6184128 CmpSum.Pre CmpSum.Post := by
  have hc : CodeIn64 FvModexp.Lib.CmpAmd64.program (LibW.program.link impl) := by
    rw [LibW.eq_only]
    exact Callees.codeIn_single hap (seg := Extracted.seg15) rfl
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide)
  exact Summary.of_codeIn64 hc CmpSum.cmp_summary

set_option maxRecDepth 20000 in
/-- a call of `nat.trunc` (premise `Trunc.Hyp2`) at its entry `6188320`, continuation form, Nat-level arguments -/
theorem truncCallW {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat}
    (htr : Trunc.Hyp2 impl R ns stk above) {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl xc n : Nat}
    {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 6188320) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 x) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 n) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : x < 2 ^ 64) (bxl : xl < 2 ^ 64) (bn : n < 2 ^ 64)
    (hpre : TruncPre R b L stk above zp zl zc x xl n S) (hnorm : NatNorm S.mem x xl ∨ (n + 63) / 64 ≤ xl)
    (hcp : zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n))
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 14 = S.regs 14 →
      s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions → TruncPost R b L stk above zp zc x xl n S s' →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := hypSumW hap hns (by simp [numIntRegs]) (htr b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 n))
  rw [show segAddr Extracted.program Trunc.fn = 6188320 by decide] at hS
  have hzl : zl < 2 ^ 64 := by have := hpre.2.2.1; omega
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, _, e3, e4⟩, hq⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]
  · rw [tN bz, tN hzl, tN bzc, tN bx, tN bxl, tN bn]; exact ⟨hpre, hnorm, hcp⟩
  · rw [tN bz, tN bzc, tN bx, tN bxl, tN bn] at hq
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e3 e4 hrg hq

set_option maxRecDepth 20000 in
/-- a call of `nat.sub` (premise `SubHypR0`) at its entry `6183136` with `RSP = sp'`, continuation form over the
destructured (Nat-level) postcondition -/
theorem subCall0 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hsub : SubHypR0 impl R) {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : Nat} {sp' g : Nat}
    {M : Memory} {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatSub.names).link impl) ra)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (by' : yp < 2 ^ 64)
    (byl : yl < 2 ^ 64) (bsp : sp' + 8 < 2 ^ 64) (bx39 : xl < 2 ^ 39)
    (hpc : S.rip = BitVec.ofNat 64 6183136) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 xp) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yp) (h10 : S.regs 10 = BitVec.ofNat 64 yl) (h11 : S.regs 11 = BitVec.ofNat 64 yc)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hS : S.mem = M) (hsp : (S.regs 4).toNat = sp') (h14 : (S.regs 14).toNat = g)
    (hpre : NatSub.Pre0 R b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc) S)
    (K : ∀ (s' : State) (p' n' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.rip = BitVec.ofNat 64 ra →
      s'.regs 4 = BitVec.ofNat 64 (sp' + 8) → s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 →
      s'.fsBase = S.fsBase → s'.df = S.df →
      s'.mem.regions = M.regions → s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 n' →
      s'.regs 1 = BitVec.ofNat 64 c' → natVal s'.mem p' n' = natVal M xp xl - natVal M yp yl →
      NatNorm s'.mem p' n' → n' ≤ c' → n' ≤ xl → LiveExt R L L' → b - makeCost xl ≤ b' →
      R.inv b' L' g (view R.rt L' s'.mem) → NatLive s'.mem R L' p' c' →
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) →
      MemFrame M s'.mem (R.rt ++ [(sp' - 4288, sp' + 80)] ++ [(zp, zp + 8 * zc)]) →
      LiveFrame M s'.mem L [(zp, zp + 8 * zc)] → (xl ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 → p' < 2 ^ 64 →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS' := hypSumW hap subW_names (by simp [numIntRegs])
    (hsub b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc))
  rw [show segAddr Extracted.program NatSub.fn = 6183136 by decide] at hS'
  refine ReachesRet.call_regions hS' hpc ⟨by rw [hrd]; exact hra, hx15, ?_, hdf, hpre⟩
    fun s' hr ⟨⟨e1, _, e3, e4⟩, hq, hr1, hr2⟩ hrg => ?_
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9, h10, h11]
  · obtain ⟨hfs, hdf', p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, hF, hLF⟩ := hq
    rw [tN bz, tN bzc, tN bx, tN bxl, tN by', tN byl, hS] at *
    simp only [win, hsp, h14] at hF hinv
    rw [hS] at hrg
    refine K s' p' n' c' L' b' (by rw [hr, retAddrOf_eq, hrd]) ?_ e3 e4 hfs hdf' hrg
      (by rw [← q0, Expmc.bv_ofNat_toNat]) (by rw [← q1, Expmc.bv_ofNat_toNat]) (by rw [← q2, Expmc.bv_ofNat_toNat])
      hv hn hlc hln hLE hb hinv hlive hor (by simpa only [show 4288 + 80 = 4368 from rfl] using hF) hLF
      (fun h => ?_) (by rw [← q2]; exact hr2 bx39) (by rw [← q0]; exact BitVec.isLt _)
    · rw [e1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp]
    · obtain ⟨a1, a2⟩ := hr1 h
      exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

set_option maxRecDepth 20000 in
/-- a call of `nat.add` (premise `AddHypR`) at its entry `6182240` with `RSP = sp'` (on `LibW`) -/
theorem addCallW {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hadd : AddHypR impl R) {b : Nat} {L : List (Nat × Nat)} {zp zl zc xp xl xc yp yl yc : Nat} {sp' g : Nat}
    {M : Memory} {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments NatAdd.names).link impl) ra)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64) (by' : yp < 2 ^ 64)
    (byl : yl < 2 ^ 64) (bsp : sp' + 8 < 2 ^ 64) (bx39 : xl < 2 ^ 39) (by39 : yl < 2 ^ 39)
    (hpc : S.rip = BitVec.ofNat 64 6182240) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 xp) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yp) (h10 : S.regs 10 = BitVec.ofNat 64 yl) (h11 : S.regs 11 = BitVec.ofNat 64 yc)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hS : S.mem = M) (hsp : (S.regs 4).toNat = sp') (h14 : (S.regs 14).toNat = g)
    (hpre : NatAdd.Pre R b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc) S)
    (K : ∀ (s' : State) (p' n' c' : Nat) (L' : List (Nat × Nat)) (b' : Nat), s'.rip = BitVec.ofNat 64 ra →
      s'.regs 4 = BitVec.ofNat 64 (sp' + 8) → s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 →
      s'.fsBase = S.fsBase → s'.df = S.df →
      s'.mem.regions = M.regions → s'.regs 0 = BitVec.ofNat 64 p' → s'.regs 3 = BitVec.ofNat 64 n' →
      s'.regs 1 = BitVec.ofNat 64 c' → natVal s'.mem p' n' = natVal M xp xl + natVal M yp yl →
      NatNorm s'.mem p' n' → n' ≤ c' → n' ≤ max xl yl + 1 → LiveExt R L L' →
      b - makeCost (if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ b' →
      R.inv b' L' g (view R.rt L' s'.mem) → NatLive s'.mem R L' p' c' →
      ((p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) →
      MemFrame M s'.mem (R.rt ++ [(sp' - 4440, sp' + 80)] ++ [(zp, zp + 8 * zc)]) →
      LiveFrame M s'.mem L [(zp, zp + 8 * zc)] →
      ((if min xl yl = 0 then max xl yl else max xl yl + 1) ≤ zc → p' = zp ∧ c' = zc) → c' < 2 ^ 40 → p' < 2 ^ 64 →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS' := hypSumW hap addW_names (by simp [numIntRegs])
    (hadd b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp) (BitVec.ofNat 64 yl)
    (BitVec.ofNat 64 yc))
  rw [show segAddr Extracted.program NatAdd.fn = 6182240 by decide] at hS'
  refine ReachesRet.call_regions hS' hpc ⟨by rw [hrd]; exact hra, hx15, ?_, hdf, hpre⟩
    fun s' hr ⟨⟨e1, _, e3, e4⟩, hq, hr1, hr2⟩ hrg => ?_
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9, h10, h11]
  · obtain ⟨hfs, hdf', p', n', c', q0, q1, q2, hv, hn, hlc, hln, L', b', hLE, hb, hinv, hlive, hor, hF, hLF⟩ := hq
    rw [tN bz, tN bzc, tN bx, tN bxl, tN by', tN byl, hS] at *
    simp only [win, hsp, h14] at hF hinv
    simp only [NatAdd.mx, NatAdd.need, tN bxl, tN byl] at hln hb hr1 hr2
    rw [hS] at hrg
    refine K s' p' n' c' L' b' (by rw [hr, retAddrOf_eq, hrd]) ?_ e3 e4 hfs hdf' hrg
      (by rw [← q0, Expmc.bv_ofNat_toNat]) (by rw [← q1, Expmc.bv_ofNat_toNat]) (by rw [← q2, Expmc.bv_ofNat_toNat])
      hv hn hlc hln hLE hb hinv hlive hor hF hLF (fun h => ?_) (by rw [← q2]; exact hr2 (by omega))
      (by rw [← q0]; exact BitVec.isLt _)
    · rw [e1]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, hsp]
    · obtain ⟨a1, a2⟩ := hr1 h
      exact ⟨by rw [← q0, a1], by rw [← q2, a2]⟩

/-! ## Callee preconditions -/

theorem PreG.costB {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) : cost n ≤ b :=
  hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1

/-- the amd64 entry facts of `PreG` -/
theorem PreG.ent {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) : Ent s zp zc n :=
  hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- `z`'s window / guard / TLS facts -/
theorem PreG.zwin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) :
    (zp + 8 * zc ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ zp) ∧
      Apart zp (8 * zc) ((s.regs 14).toNat + 16) 8 ∧ Apart zp (8 * zc) (s.fsBase.toNat - 8) 8 := by
  have hzw := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [win, K, A, outside_cons, outside_nil, and_true] at hzw
  exact ⟨hzw, hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

set_option maxRecDepth 20000 in
/-- the precondition of a `trunc` call at `RSP_c = e - 136`: destination `z'` given by its facts, budget base
`bb ≥ cost n`, at most `k ≤ 4` budgeted calls before -/
theorem truncPreG_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} (hbb : cost n ≤ bb) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 k : Nat} (hrt : Rt R bb L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State}
    (hS : S.mem = M) (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 136) (h14 : S.regs 14 = s.regs 14)
    (hfs : S.fsBase = s.fsBase) {stk above : Nat} (hkT : stk ≤ 4440) (haT : above ≤ 80)
    {zp' zl' zc' : Nat} (hzl' : zl' ≤ zc') (hzc' : zc' < 2 ^ 40) (hzlv : NatLive M R L1 zp' zc')
    (hzw' : 0 < zc' → (zp' + 8 * zc' ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ zp') ∧
      Apart zp' (8 * zc') ((s.regs 14).toNat + 16) 8 ∧ Apart zp' (8 * zc') (s.fsBase.toNat - 8) 8)
    {x xl : Nat} (hx40 : xl < 2 ^ 40) (hxa : M.accessible x (8 * xl) false = true) (hx48 : x + 8 * xl ≤ 2 ^ 48)
    (hxh : Held R L1 x (8 * xl)) (hxw : x + 8 * xl ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ x)
    (hxl : xl ≤ 2 ^ 16)
    (halias : zp' = x ∨ (0 < zc' → 0 < xl → Apart zp' (8 * zc') x (8 * xl))) :
    TruncPre R b1 L1 stk above zp' zl' zc' x xl n S := by
  have hsp4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hce := CallW.callEnv_of (cenvG_of hpre hrt (dlG_of hpre hrt)) hsp (by rw [h14]) (by rw [hfs]) hS hkT haT
    (by omega)
  have hn15 := hpre.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, hbud, hinv, -⟩ := hrt
  refine ⟨hce, hpre.2.1, hzl', ⟨hzc', by rw [hS]; exact hzlv, fun hc => ?_⟩, ⟨hx40, by rw [hS]; exact hxa, hx48, hxh, ?_⟩,
    hxl, by omega, halias, ?_, by rw [hS, h14]; exact hinv⟩
  · obtain ⟨h1, h2, h3⟩ := hzw' hc
    simp only [win, hsp, h14, hfs, outside_cons, outside_nil, and_true]
    exact ⟨by omega, h2, h3⟩
  · simp only [win, hsp, outside_cons, outside_nil, and_true]; omega
  · have h1 := truncNeed_le_w xl n
    simp only [cost] at hbb
    rw [Nat.mul_comm] at hbud
    have h2 : wCost n * k ≤ wCost n * 4 := Nat.mul_le_mul_left _ hk
    omega

/-- `truncPreG_of` with `z` itself as the destination -/
theorem truncPreG_self {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} (hbb : cost n ≤ bb) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 k : Nat} (hrt : Rt R bb L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State}
    (hS : S.mem = M) (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 136) (h14 : S.regs 14 = s.regs 14)
    (hfs : S.fsBase = s.fsBase) {stk above : Nat} (hkT : stk ≤ 4440) (haT : above ≤ 80) {zl' : Nat} (hzl' : zl' ≤ zc)
    {x xl : Nat} (hx40 : xl < 2 ^ 40) (hxa : M.accessible x (8 * xl) false = true) (hx48 : x + 8 * xl ≤ 2 ^ 48)
    (hxh : Held R L1 x (8 * xl)) (hxw : x + 8 * xl ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ x)
    (hxl : xl ≤ 2 ^ 16)
    (halias : zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) :
    TruncPre R b1 L1 stk above zp zl' zc x xl n S :=
  truncPreG_of hpre hbb hrt hk hS hsp h14 hfs hkT haT hzl' hpre.2.2.2.2.2.2.2.2.2.2.1 hrt.2.2.2.2.2.2
    (fun _ => hpre.zwin) hx40 hxa hx48 hxh hxw hxl halias

/-- `truncPreG_of` with a `nil` destination -/
theorem truncPreG_nil {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} (hbb : cost n ≤ bb) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 k : Nat} (hrt : Rt R bb L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State}
    (hS : S.mem = M) (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 136) (h14 : S.regs 14 = s.regs 14)
    (hfs : S.fsBase = s.fsBase) {stk above : Nat} (hkT : stk ≤ 4440) (haT : above ≤ 80)
    {x xl : Nat} (hx40 : xl < 2 ^ 40) (hxa : M.accessible x (8 * xl) false = true) (hx48 : x + 8 * xl ≤ 2 ^ 48)
    (hxh : Held R L1 x (8 * xl)) (hxw : x + 8 * xl ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ x)
    (hxl : xl ≤ 2 ^ 16) :
    TruncPre R b1 L1 stk above 0 0 0 x xl n S :=
  truncPreG_of hpre hbb hrt hk hS hsp h14 hfs hkT haT (Nat.le_refl _) (by decide) (by simp)
    (fun h => absurd h (by decide)) hx40 hxa hx48 hxh hxw hxl (Or.inr fun h => absurd h (by decide))

set_option maxRecDepth 20000 in
/-- the precondition of `z.sub(x, y)` at `RSP_c = e - 136` (empty-tolerant operands; `z` = the entry `z`, at most two
budgeted calls before) -/
theorem subPre0_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (hrt : Rt R b L s zp zc n k M L1 b1) (hk : k ≤ 2) {S : State} (hS : S.mem = M)
    (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 136) (h14 : S.regs 14 = s.regs 14) (hfs : S.fsBase = s.fsBase)
    {xp xl xc yp' yl' yc' : Nat} (hyx : yl' ≤ xl) (hYX : natVal M yp' yl' ≤ natVal M xp xl) (hxc : xl ≤ xc)
    (hyc : yl' ≤ yc') (hxc40 : xc < 2 ^ 40) (hyc40 : yc' < 2 ^ 40) (hxW : xl ≤ W n) (hxp : xp < 2 ^ 64)
    (hyp : yp' < 2 ^ 64)
    (hzx : 0 < zc → 0 < xl → zp = xp ∨ Apart zp (8 * zc) xp (8 * xl))
    (hzy : 0 < zc → 0 < yl' → zp = yp' ∨ Apart zp (8 * zc) yp' (8 * yl'))
    (hx : 0 < xl → M.accessible xp (8 * xl) false = true ∧ xp + 8 * xl ≤ 2 ^ 48 ∧ Held R L1 xp (8 * xl) ∧
      (xp + 8 * xl ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ xp)) (hxn : NatNorm M xp xl)
    (hy : 0 < yl' → M.accessible yp' (8 * yl') false = true ∧ yp' + 8 * yl' ≤ 2 ^ 48 ∧ Held R L1 yp' (8 * yl') ∧
      (yp' + 8 * yl' ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ yp')) (hyn : NatNorm M yp' yl') :
    NatSub.Pre0 R b1 L1 (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp') (BitVec.ofNat 64 yl') (BitVec.ofNat 64 yc') S := by
  have hsp4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hce := CallW.callEnv_of (cenvG_of hpre hrt (dlG_of hpre hrt)) hsp (by rw [h14]) (by rw [hfs]) hS
    (show 4288 ≤ 4440 by omega) (show 80 ≤ 80 by omega) (by omega)
  have hz64 := hpre.2.2.2.2.2.2.2.2.2.1.1
  have hzc := hpre.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hzw, hzg, hzf⟩ := hpre.zwin
  have hcost := hpre.costB
  have hserv := hpre.2.1
  have hwt := hpre.2.2.1
  obtain ⟨-, -, -, -, hbud, hinv, hlive⟩ := hrt
  have hmk : makeCost xl ≤ wCost n := makeCost_le_w (by omega)
  simp only [cost] at hcost
  have hkw : k * wCost n ≤ 2 * wCost n := Nat.mul_le_mul_right _ hk
  simp only [W] at hxW
  unfold NatSub.Pre0
  rw [tN hz64, tN (show zc < 2 ^ 64 by omega), tN hxp, tN (show xl < 2 ^ 64 by omega),
    tN (show xc < 2 ^ 64 by omega), tN hyp, tN (show yl' < 2 ^ 64 by omega), tN (show yc' < 2 ^ 64 by omega), hS]
  simp only [win, hsp, h14, hfs, K, A, outside_cons, outside_nil, and_true]
  refine ⟨hce, hwt, hyx, hYX, hxc, hyc, hxc40, hyc40, by omega, by omega, hzc, hlive, fun _ => by omega,
    fun hz => ⟨by unfold Apart at hzg ⊢; omega, hzf, fun h => ?_, fun h => ?_⟩, fun h => ?_, hxn, hyn, fun h => ?_, hinv,
    fun _ => ⟨hserv.1 _ _ _ (by unfold makeCap; split <;> omega), by omega⟩,
    fun d src k hk => hserv.2.1 d src k (by omega)⟩
  · rcases hzx hz h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h
  · rcases hzy hz h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h
  · obtain ⟨a1, a2, a3, a4⟩ := hx h
    exact ⟨a1, a2, a3, by omega⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hy h
    exact ⟨a1, a2, a3, by omega⟩

set_option maxRecDepth 20000 in
/-- the precondition of `z.add(x, y)` at `RSP_c = e - 136`: destination `z'` given by its facts, budget base
`bb ≥ cost n`, at most `k ≤ 4` budgeted calls before -/
theorem addPreG_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : PreG R b L op zp zl zc yp yl yc n s) {bb : Nat} (hbb : cost n ≤ bb) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 k : Nat} (hrt : Rt R bb L s zp zc n k M L1 b1) (hk : k ≤ 4) {S : State}
    (hS : S.mem = M) (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 136) (h14 : S.regs 14 = s.regs 14)
    (hfs : S.fsBase = s.fsBase)
    {zp' zc' : Nat} (hc0 : 0 < zc') (hzc' : zc' < 2 ^ 40) (hzlv : NatLive M R L1 zp' zc') (hz64 : zp' < 2 ^ 64)
    (hzw' : 0 < zc' → (zp' + 8 * zc' ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ zp') ∧
      Apart zp' (8 * zc') ((s.regs 14).toNat + 16) 8 ∧ Apart zp' (8 * zc') (s.fsBase.toNat - 8) 8)
    {xp xl xc yp' yl' yc' : Nat} (hxc : xl ≤ xc) (hyc : yl' ≤ yc') (hxc40 : xc < 2 ^ 40) (hyc40 : yc' < 2 ^ 40)
    (hxW : xl ≤ W n) (hyW : yl' ≤ W n)
    (hzx : zp' = xp ∨ Apart zp' (8 * zc') xp (8 * xl)) (hzy : zp' = yp' ∨ Apart zp' (8 * zc') yp' (8 * yl'))
    (hxa : M.accessible xp (8 * xl) false = true) (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxh : Held R L1 xp (8 * xl))
    (hxn : NatNorm M xp xl) (hxw : xp + 8 * xl ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ xp)
    (hya : M.accessible yp' (8 * yl') false = true) (hy48 : yp' + 8 * yl' ≤ 2 ^ 48) (hyh : Held R L1 yp' (8 * yl'))
    (hyn : NatNorm M yp' yl') (hyw : yp' + 8 * yl' ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat - 56 ≤ yp') :
    NatAdd.Pre R b1 L1 (BitVec.ofNat 64 zp') (BitVec.ofNat 64 zc') (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl)
      (BitVec.ofNat 64 xc) (BitVec.ofNat 64 yp') (BitVec.ofNat 64 yl') (BitVec.ofNat 64 yc') S := by
  have hsp4 : 4576 ≤ (s.regs 4).toNat := hpre.1.2.1.1
  have hce := CallW.callEnv_of (cenvG_of hpre hrt (dlG_of hpre hrt)) hsp (by rw [h14]) (by rw [hfs]) hS
    (show 4440 ≤ 4440 by omega) (show 80 ≤ 80 by omega) (by omega)
  have hn2 := hpre.2.2.2.2.2.2.2.1
  have hserv := hpre.2.1
  have hwt := hpre.2.2.1
  obtain ⟨-, -, -, -, hbud, hinv, -⟩ := hrt
  have hmk : makeCost (if min xl yl' = 0 then max xl yl' else max xl yl' + 1) ≤ wCost n :=
    makeCost_le_w (by split <;> omega)
  simp only [W] at hxW hyW
  simp only [cost] at hbb
  have hkw : k * wCost n ≤ 4 * wCost n := Nat.mul_le_mul_right _ hk
  have hxp : xp < 2 ^ 64 := by omega
  have hyp : yp' < 2 ^ 64 := by omega
  obtain ⟨hw1, hw2, hw3⟩ := hzw' hc0
  unfold NatAdd.Pre NatAdd.PreS
  simp only [NatAdd.need, NatAdd.mx]
  rw [tN hz64, tN (show zc' < 2 ^ 64 by omega), tN hxp, tN (show xl < 2 ^ 64 by omega),
    tN (show xc < 2 ^ 64 by omega), tN hyp, tN (show yl' < 2 ^ 64 by omega), tN (show yc' < 2 ^ 64 by omega), hS]
  simp only [win, hsp, h14, hfs, K, A, outside_cons, outside_nil, and_true]
  refine ⟨hce, hwt, hxc, hyc, hxc40, hyc40, by omega, by omega, hzc', hzlv, by omega,
    fun _ => ⟨by unfold Apart at hw2 ⊢; omega, hw3, ?_, ?_⟩, hxa, hx48, hxh, hxn, hyn, by omega, hya,
    hy48, hyh, by omega, hinv,
    fun _ => ⟨hserv.1 _ _ _ (by unfold makeCap; split <;> split <;> omega), by omega⟩,
    fun d src k hk => hserv.2.1 d src k (by omega)⟩
  · rcases hzx with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h
  · rcases hzy with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr h

/-! ## The postcondition -/

/-- the general postcondition from the runtime facts after the last call (relative to `b - g · gA n`) and the result -/
theorem post_ofG {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc yp yl n k g : Nat} {s s' : State}
    {L2 : List (Nat × Nat)} {b2 : Nat} (hrt : Rt R (b - g * gA n) L s zp zc n k s'.mem L2 b2) (hk : k ≤ 5)
    (hg : g ≤ W n) (hg0 : W n ≤ zc → g = 0) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    {p' l' c' : Nat} (e0 : (s'.regs 0).toNat = p') (e1 : (s'.regs 3).toNat = l') (e2 : (s'.regs 1).toNat = c')
    (hv : natVal s'.mem p' l' = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n) (hnorm : NatNorm s'.mem p' l')
    (hlc : l' ≤ c') (hc40 : c' < 2 ^ 40) (hlive : NatLive s'.mem R L2 p' c')
    (hor : (p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))
    (hre : W n + 1 ≤ zc → p' = zp ∧ c' = zc) :
    PostG R b L zp zl zc yp yl n s s' := by
  obtain ⟨-, hF, hLF, hLE, hb, hinv, -⟩ := hrt
  have h1 : k * wCost n ≤ 5 * wCost n := Nat.mul_le_mul_right _ hk
  have h2 : g * gA n ≤ W n * gA n := Nat.mul_le_mul_right _ hg
  refine ⟨hfs, hdf, p', l', c', e0, e1, e2, hv, hnorm, hlc, hc40, L2, b2, hLE, by simp only [costG, cost]; omega,
    fun hW => ?_, hinv, hlive, hor, hF, hLF, hre⟩
  rw [hg0 hW, Nat.zero_mul, Nat.sub_zero] at hb
  simp only [cost]; omega

/-- `post_ofG` without growth (runtime facts relative to `b`) -/
theorem post_ofG0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc yp yl n k : Nat} {s s' : State}
    {L2 : List (Nat × Nat)} {b2 : Nat} (hrt : Rt R b L s zp zc n k s'.mem L2 b2) (hk : k ≤ 5)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    {p' l' c' : Nat} (e0 : (s'.regs 0).toNat = p') (e1 : (s'.regs 3).toNat = l') (e2 : (s'.regs 1).toNat = c')
    (hv : natVal s'.mem p' l' = Exp.subMod2N (natVal s.mem zp zl) (natVal s.mem yp yl) n) (hnorm : NatNorm s'.mem p' l')
    (hlc : l' ≤ c') (hc40 : c' < 2 ^ 40) (hlive : NatLive s'.mem R L2 p' c')
    (hor : (p' = zp ∧ c' = zc) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L))
    (hre : W n + 1 ≤ zc → p' = zp ∧ c' = zc) :
    PostG R b L zp zl zc yp yl n s s' := by
  obtain ⟨-, hF, hLF, hLE, hb, hinv, -⟩ := hrt
  have h1 : k * wCost n ≤ 5 * wCost n := Nat.mul_le_mul_right _ hk
  exact ⟨hfs, hdf, p', l', c', e0, e1, e2, hv, hnorm, hlc, hc40, L2, b2, hLE, by simp only [costG, cost]; omega,
    fun _ => by simp only [cost]; omega, hinv, hlive, hor, hF, hLF, hre⟩

/-- `bitLen` of a word (as the arm64 `SubMod2N.bitLen_le64`) -/
theorem bitLen_le64 (v : Nat) (h : v < 2 ^ 64) : Aux.bitLen v ≤ 64 := by
  by_cases hv : v = 0
  · subst hv; decide
  · have h1 := (Util.bitLen_bounds v hv).1
    have h2 : 2 ^ (Aux.bitLen v - 1) < 2 ^ 64 := by omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).1 h2
    omega


end FvModexp.Amd64.SubMod2N
