import FvModexp.Proofs.Arm64.Exp.LibCalls
import FvModexp.Proofs.Arm64.Nat.SqrMulX

/-!
# Call helpers for divmc's `nat.sqr` / `nat.mul` export shapes `SqrHypX` / `MulHypX` (arm64; agent infra)

As `LibCalls.sqrCallR` / `mulCallR`, with the extra pre conjunct `SqrX` / `MulX` and the `StackBackL` posts;
`stkNatCallL`: `(*stack).nat` with divmc's `HypL` / `PostL`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.LibCalls

open FvModexp.Arm64.EvenHyp

set_option maxRecDepth 20000 in
theorem sqrCallX {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat} {cost : Nat → Nat → Nat}
    (hsq : SqrHypX impl R ns stk above cost) {b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program fnSqr)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 x) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : x < 2 ^ 64)
    (bxl : xl < 2 ^ 64) (bxc : xc < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : SqrPre R b (cost (stLen S.mem st) xl) L stk above zp zl zc st x xl S) (hcap : CapIn R L x xl xc)
    (hX : SqrX R L S stk above st zp zc x xl xc)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions →
      SqrPostL R b (cost (stLen S.mem st) xl) L stk above zp zc st x xl S s' → Reuse (2 * xl) zp zc [(x, xc)] s' →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := CallWW.hypSum hap hns (hsq b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, trivial⟩
  · rw [tN bz, tN bzl, tN bzc, tN bst, tN bx, tN bxl, tN bxc]; exact ⟨hpre, hcap, hX⟩
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN bxc] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq.1 hq.2

set_option maxRecDepth 20000 in
theorem mulCallX {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat} {cost : Nat → Nat → Nat → Nat}
    (hmu : MulHypX impl R ns stk above cost) {b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc y yl yc : Nat}
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
    (hpre : MulPre R b (cost (stLen S.mem st) xl yl) L stk above zp zl zc st x xl y yl S)
    (hcx : CapIn R L x xl xc) (hcy : CapIn R L y yl yc)
    (hX : MulX R L S stk above st zp zc x xl xc y yl yc)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions →
      MulPostL R b (cost (stLen S.mem st) xl yl) L stk above zp zc st x xl y yl S s' →
      Reuse (xl + yl) zp zc [(x, xc), (y, yc)] s' → ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := CallWW.hypSum hap hns (hmu b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 y)
    (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, trivial⟩
  · rw [tN bz, tN bzl, tN bzc, tN bst, tN bx, tN bxl, tN bxc, tN by', tN byl, tN byc]; exact ⟨hpre, hcx, hcy, hX⟩
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN bxc, tN by', tN byl, tN byc] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq.1 hq.2

set_option maxRecDepth 20000 in
/-- `LibCalls.stkNatCall` with the `StackBackL`-ready post (`StackNat.HypL` / `PostL`) -/
theorem stkNatCallL {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat}
    (hsn : StackNat.HypL impl R ns stk above) {b : Nat} {L : List (Nat × Nat)} {st n : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (bst : st < 2 ^ 64) (bn : n < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : StackNat.Pre R b L stk above st n S)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions → StackNat.PostL R b L stk above st n S s' →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := CallWW.hypSum hap hns (hsn b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 n))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, LibCalls.tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, trivial⟩
  · rw [LibCalls.tN bst, LibCalls.tN bn]; exact hpre
  · rw [LibCalls.tN bst, LibCalls.tN bn] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq

end FvModexp.Arm64.LibCalls
