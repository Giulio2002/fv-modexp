import FvModexp.Proofs.Arm64.Exp.SlowG
import FvModexp.Proofs.Arm64.Exp.CallWW
import FvModexp.Proofs.Arm64.Exp.LibCalls

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): call helpers for the empty-tolerant premise forms on `LibW` (agent expmc)

As infra's `LibCalls.sqrCallX` / `mulCallX` (LibCallsX): `sqrCallG` (`SqrHypG`), `mulCallG` (`ExpEven.MulHypG`),
`divCallG` (`DivHypLG`): at the callee entry with the arguments in registers and the return address `ra`, the
continuation gets the callee's post at the return state.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpEven (CapIn0 MulPreG MulXG MulHypG)
open FvModexp.Arm64.ExpHyp (fnDiv)
open FvModexp.Arm64.LibCalls (tN)

set_option maxRecDepth 20000 in
theorem sqrCallG {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat} {cost : Nat → Nat → Nat}
    (hsq : SqrHypG impl R ns stk above cost) {b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program fnSqr)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 x) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : x < 2 ^ 64)
    (bxl : xl < 2 ^ 64) (bxc : xc < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : SqrPreG R b (cost (stLen S.mem st) xl) L stk above zp zl zc st x xl S ∧ CapIn0 R L x xl xc ∧
      SqrXG R L S stk above st zp zc x xl xc)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions →
      SqrPostL R b (cost (stLen S.mem st) xl) L stk above zp zc st x xl S s' →
      (xl = 0 → s'.regs 0 = BitVec.ofNat 64 zp ∧ s'.regs 2 = BitVec.ofNat 64 zc) →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := CallWW.hypSum hap hns (hsq b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, trivial⟩
  · rw [tN bz, tN bzl, tN bzc, tN bst, tN bx, tN bxl, tN bxc]; exact hpre
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq.1 hq.2

set_option maxRecDepth 20000 in
theorem mulCallG {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat} {cost : Nat → Nat → Nat → Nat}
    (hmu : MulHypG impl R ns stk above cost) {b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc y yl yc : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program fnMul)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 x) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 y) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : x < 2 ^ 64)
    (bxl : xl < 2 ^ 64) (bxc : xc < 2 ^ 64) (by' : y < 2 ^ 64) (byl : yl < 2 ^ 64) (byc : yc < 2 ^ 64)
    (bra : ra < 2 ^ 64)
    (hpre : MulPreG R b (cost (stLen S.mem st) xl yl) L stk above zp zl zc st x xl y yl S ∧ CapIn0 R L x xl xc ∧
      CapIn0 R L y yl yc ∧ MulXG R L S stk above st zp zc x xl xc y yl yc)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions →
      MulPostL R b (cost (stLen S.mem st) xl yl) L stk above zp zc st x xl y yl S s' →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := CallWW.hypSum hap hns (hmu b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 y)
    (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, trivial⟩
  · rw [tN bz, tN bzl, tN bzc, tN bst, tN bx, tN bxl, tN bxc, tN by', tN byl, tN byc]; exact hpre
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN by', tN byl] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq.1

set_option maxRecDepth 20000 in
theorem divCallG {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat}
    {cost : Nat → Nat → Nat → Nat} (hdv : DivHypLG impl R ns stk above cost) {b : Nat} {L : List (Nat × Nat)}
    {zp zl zc st z2 z2l z2c u ul uc v vl vc : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program fnDiv)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 z2) (h5 : S.regs 5 = BitVec.ofNat 64 z2l)
    (h6 : S.regs 6 = BitVec.ofNat 64 z2c) (h7 : S.regs 7 = BitVec.ofNat 64 u) (h8 : S.regs 8 = BitVec.ofNat 64 ul)
    (h9 : S.regs 9 = BitVec.ofNat 64 uc) (h10 : S.regs 10 = BitVec.ofNat 64 v) (h11 : S.regs 11 = BitVec.ofNat 64 vl)
    (h12 : S.regs 12 = BitVec.ofNat 64 vc)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bz2 : z2 < 2 ^ 64)
    (bz2l : z2l < 2 ^ 64) (bz2c : z2c < 2 ^ 64) (bu : u < 2 ^ 64) (bul : ul < 2 ^ 64) (buc : uc < 2 ^ 64)
    (bv : v < 2 ^ 64) (bvl : vl < 2 ^ 64) (bvc : vc < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : DivPreG R b cost L stk above zp zl zc st z2 z2l z2c u ul v vl S)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions →
      DivPostLG R b cost L stk above zp zc st z2 z2c u ul v vl S s' →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := CallWW.hypSum hap hns (hdv b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 z2) (BitVec.ofNat 64 z2l) (BitVec.ofNat 64 z2c) (BitVec.ofNat 64 u)
    (BitVec.ofNat 64 ul) (BitVec.ofNat 64 uc) (BitVec.ofNat 64 v) (BitVec.ofNat 64 vl) (BitVec.ofNat 64 vc))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, trivial⟩
  · rw [tN bz, tN bzl, tN bzc, tN bst, tN bz2, tN bz2l, tN bz2c, tN bu, tN bul, tN bv, tN bvl]; exact hpre
  · rw [tN bz, tN bzc, tN bst, tN bz2, tN bz2c, tN bu, tN bul, tN bv, tN bvl] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq

end FvModexp.Arm64.ExpSlow
