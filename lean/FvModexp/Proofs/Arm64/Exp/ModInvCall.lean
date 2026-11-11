import FvModexp.Proofs.Arm64.Exp.ModInvSeg3
import FvModexp.Proofs.Arm64.Nat.TruncDefs
import FvModexp.Proofs.Arm64.Nat.LshDefs

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): generic call helpers for `nat.sqr` / `nat.mul` / `nat.lsh` (agent infra)

Continuation form (as `SubMod2N.truncCall`): at the callee entry with the arguments in registers and the callee's
precondition, the continuation receives the return state and the callee's postcondition (Nat-level arguments).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (LshPost fnLsh)
open FvModexp.Arm64.SubMod2N (tN)

set_option maxRecDepth 20000 in
theorem sqrCall {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) {stk above : Nat} {cost : Nat → Nat}
    (hsq : SqrHyp impl R ns stk above cost) {b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program fnSqr)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 x) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : x < 2 ^ 64)
    (bxl : xl < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : SqrPre R b (cost xl) L stk above zp zl zc st x xl S)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions → SqrPost R b (cost xl) L stk above zp zc st x xl S s' →
      ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS := CallW.hypSum hap hns (hsq b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, trivial⟩
  · rw [tN bz, tN bzl, tN bzc, tN bst, tN bx, tN bxl]; exact hpre
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq

set_option maxRecDepth 20000 in
theorem mulCall {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) {stk above : Nat} {cost : Nat → Nat → Nat}
    (hmu : MulHyp impl R ns stk above cost) {b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc y yl yc : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program fnMul)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 x) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h7 : S.regs 7 = BitVec.ofNat 64 y) (h8 : S.regs 8 = BitVec.ofNat 64 yl)
    (h9 : S.regs 9 = BitVec.ofNat 64 yc)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : x < 2 ^ 64)
    (bxl : xl < 2 ^ 64) (by' : y < 2 ^ 64) (byl : yl < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : MulPre R b (cost xl yl) L stk above zp zl zc st x xl y yl S)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions →
      MulPost R b (cost xl yl) L stk above zp zc st x xl y yl S s' →
      ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS := CallW.hypSum hap hns (hmu b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 st) (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 y)
    (BitVec.ofNat 64 yl) (BitVec.ofNat 64 yc))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, trivial⟩
  · rw [tN bz, tN bzl, tN bzc, tN bst, tN bx, tN bxl, tN by', tN byl]; exact hpre
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN by', tN byl] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq

set_option maxRecDepth 20000 in
/-- `nat.lsh` (asm's `Lsh.Hyp2`: `LshPreA` + `0 < sh ∧ 0 < xl`) -/
theorem lshCall {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) {stk above : Nat}
    (hls : Lsh.Hyp2 impl R ns stk above) {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl xc sh : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program fnLsh)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 x) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 sh)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : x < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bsh : sh < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : LshPreA R b L stk above zp zl zc x xl sh S) (hsh : 0 < sh) (hxl : 0 < xl)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions → LshPost R b L stk above zp zc x xl sh S s' →
      ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS := CallW.hypSum hap hns (hls b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 sh))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, trivial⟩
  · rw [tN bz, tN bzl, tN bzc, tN bx, tN bxl, tN bsh]; exact ⟨hpre, hsh, hxl⟩
  · rw [tN bz, tN bzc, tN bx, tN bxl, tN bsh] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq

set_option maxRecDepth 20000 in
/-- `nat.trunc` (asm's `Trunc.Hyp2`: `TruncPre` + `NatNorm x ∨ ⌈n/64⌉ ≤ xl` + the empty-copy disjunct) -/
theorem truncCall2 {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) {stk above : Nat}
    (htr : Trunc.Hyp2 impl R ns stk above) {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl xc n : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program fnTrunc)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zl) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h3 : S.regs 3 = BitVec.ofNat 64 x) (h4 : S.regs 4 = BitVec.ofNat 64 xl) (h5 : S.regs 5 = BitVec.ofNat 64 xc)
    (h6 : S.regs 6 = BitVec.ofNat 64 n)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : x < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bn : n < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : TruncPre R b L stk above zp zl zc x xl n S) (hnorm : NatNorm S.mem x xl ∨ (n + 63) / 64 ≤ xl)
    (hcp : zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n))
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions → TruncPost R b L stk above zp zc x xl n S s' →
      ReachesRet (LibExp.program.link impl) ret s' Q) :
    ReachesRet (LibExp.program.link impl) ret S Q := by
  have hS := CallW.hypSum hap hns (htr b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc)
    (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 n))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, h2, h3, h4, h5, h6, trivial⟩
  · rw [tN bz, tN bzl, tN bzc, tN bx, tN bxl, tN bn]; exact ⟨hpre, hnorm, hcp⟩
  · rw [tN bz, tN bzc, tN bx, tN bxl, tN bn] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq

set_option maxRecDepth 20000 in
/-- a return address inside `modularInverseModPowerOfTwo`'s own segment (`seg41`, base `1797104`) is a return address
of every callee program that does not contain it -/
theorem ra_mi {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 300) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (1797104 + 4 * i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg41) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x1b6bf0 + 4 * i < 2 ^ 48; omega) (by decide)
  simpa only [Extracted.seg41] using this

end FvModexp.Arm64.ModInv
