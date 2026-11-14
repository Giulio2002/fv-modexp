import FvModexp.Proofs.Amd64.Exp.ModInvRnd
import FvModexp.Proofs.Amd64.Exp.SubMod2NGEns
import FvModexp.Proofs.Amd64.NatQ.MulHypQE
import FvModexp.Proofs.Amd64.Nat.LshDefs

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): call helpers for the round's callees (agent infra s56; twin of
`Arm64/Exp/ModInvCall`)

Continuation form: at the callee entry (`RSP_c`, return address at `[RSP_c]`, arguments in registers) with the
callee's precondition, the continuation receives the return state and the callee's postcondition.
* `callE`: any `Ensures` on `(onlySegments ns).link impl` (`ns ⊆ LibW.names`), via `SubMod2N.hypSumW`;
* `SqrE`: the callee premise for `nat.sqr` (= divmc's `Q.NatSqr.ens` shape, as `P2Pre.SqrE`); `nat.mul` is asm's
  `Q.DivRec.MulHypQE` (`y` on the stack at `RSP_c + 8 / 16 / 24`), `nat.trunc` / `nat.lsh` asm's `Trunc.Hyp2` /
  `Lsh.Hyp2`, `nat.subMod2N` infra's `SubMod2N.fullG` (a `Summary` on `LibW` itself, `subCall`);
* `ra_mi`: a return address inside the function's own segment (`seg41`, base `0x5ea8c0`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.EvenHyp

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- **`nat.sqr` as a callee, Q-form** (program `ns`, callee window `W`): divmc's `Q.NatSqr.ens` shape -/
def SqrE (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (W : Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program Q.NatSqr.fn)
      [zp, zl, zc, st, xp, xl, xc]
      (Q.NatSqr.SPre R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat)
      (Q.NatSqr.SPost R b H L W zp.toNat zc.toNat st.toNat xp.toNat xl.toNat xc.toNat)

set_option maxRecDepth 20000 in
/-- a call of an `Ensures` callee of `LibW` from its entry (continuation form) -/
theorem callE {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {f : String} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hlen : args.length ≤ numIntRegs)
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post)
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr Extracted.program f)) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (hx15 : S.xmm 15 = 0) (hdf : S.df = false) (hargs : ArgsFrom64 S 0 args) (hpre : pre S)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions → post S s' →
      ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have hS := SubMod2N.hypSumW hap hns hlen h
  refine ReachesRet.call_regions hS hpc ⟨by rw [hrd]; exact hra, hx15, hargs, hdf, hpre⟩
    fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e2 e3 e4 hrg hq

set_option maxRecDepth 20000 in
/-- `nat.sqr` (`SqrE`): `z = (RAX, RBX, RCX)`, `stk = RDI`, `x = (RSI, R8, R9)` -/
theorem sqrCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {W : Nat}
    (hsq : SqrE impl R ns W) (H b : Nat) {L : List (Nat × Nat)} {zp zl zc st xp xl xc : Nat}
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr Extracted.program Q.NatSqr.fn))
    (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bxc : xc < 2 ^ 64) (hpre : Q.NatSqr.SPre R b H L W zp zc st xp xl xc S)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      Q.NatSqr.SPost R b H L W zp zc st xp xl xc S s' → ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have h := hsq H b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 st)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc)
  rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN bxc] at h
  exact callE hap hns (by simp [numIntRegs]) h hra hpc hrd hx15 hdf
    (by simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]) hpre K

set_option maxRecDepth 20000 in
/-- `nat.mul` (`Q.DivRec.MulHypQE`): `z = (RAX, RBX, RCX)`, `stk = RDI`, `x = (RSI, R8, R9)`, `y` at
`RSP_c + 8 / 16 / 24` -/
theorem mulCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {W : Nat}
    (hmu : Q.DivRec.MulHypQE impl R ns W) (H b : Nat) {L : List (Nat × Nat)} {zp zl zc st xp xl xc yp yl yc : Nat}
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr Extracted.program Q.NatMul.fn))
    (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bxc : xc < 2 ^ 64)
    (hy0 : S.mem.readLE ((S.regs 4).toNat + 8) 8 = yp) (hy1 : S.mem.readLE ((S.regs 4).toNat + 16) 8 = yl)
    (hy2 : S.mem.readLE ((S.regs 4).toNat + 24) 8 = yc)
    (hpre : Q.NatMul.MPre R b H L W zp zc st xp xl xc yp yl yc S)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      Q.NatMul.MPost R b H L W zp zc st xp xl xc yp yl yc S s' → ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have h := hmu H b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 st)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) yp yl yc
  rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN bxc] at h
  exact callE hap hns (by simp [numIntRegs]) h hra hpc hrd hx15 hdf
    (by simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]) ⟨hy0, hy1, hy2, hpre⟩ K

set_option maxRecDepth 20000 in
/-- `nat.trunc` (`Trunc.Hyp2`): `z = (RAX, RBX, RCX)`, `x = (RDI, RSI, R8)`, `n = R9` -/
theorem truncCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat}
    (htr : Trunc.Hyp2 impl R ns stk above) (b : Nat) {L : List (Nat × Nat)} {zp zl zc x xl xc n : Nat}
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr Extracted.program fnTrunc))
    (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 x) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 n)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : x < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bn : n < 2 ^ 64)
    (hpre : TruncPre R b L stk above zp zl zc x xl n S) (hnorm : NatNorm S.mem x xl ∨ (n + 63) / 64 ≤ xl)
    (hcp : zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n))
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      TruncPost R b L stk above zp zc x xl n S s' → ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have h := htr b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 x)
    (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 n)
  rw [tN bz, tN bzl, tN bzc, tN bx, tN bxl, tN bn] at h
  exact callE hap hns (by simp [numIntRegs]) h hra (by rw [hpc]; rfl) hrd hx15 hdf
    (by simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]) ⟨hpre, hnorm, hcp⟩ K

set_option maxRecDepth 20000 in
/-- `nat.lsh` (`Lsh.Hyp2`): `z = (RAX, RBX, RCX)`, `x = (RDI, RSI, R8)`, `s = R9` -/
theorem lshCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat}
    (hls : Lsh.Hyp2 impl R ns stk above) (b : Nat) {L : List (Nat × Nat)} {zp zl zc x xl xc sh : Nat}
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr Extracted.program Lsh.fn))
    (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 x) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 sh)
    (bz : zp < 2 ^ 64) (bzl : zl < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : x < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bsh : sh < 2 ^ 64)
    (hpre : Lsh.LshPreA R b L stk above zp zl zc x xl sh S) (hsh : 0 < sh) (hxl : 0 < xl)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      Lsh.LshPost R b L stk above zp zc x xl sh S s' → ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have h := hls b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl) (BitVec.ofNat 64 zc) (BitVec.ofNat 64 x)
    (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 sh)
  rw [tN bz, tN bzl, tN bzc, tN bx, tN bxl, tN bsh] at h
  exact callE hap hns (by simp [numIntRegs]) h hra hpc hrd hx15 hdf
    (by simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]) ⟨hpre, hsh, hxl⟩ K

set_option maxRecDepth 20000 in
/-- `nat.subMod2N` (`SubMod2N.fullG`, general form, a `Summary` on `LibW`): `z = (RAX, RBX, RCX)` passed twice
(`z.subMod2N(z, y, n)`: `x = (RDI, RSI, R8)`), `y = (R9, R10, R11)`, `n` at `RSP_c + 8` (`PreG`'s `Ent`) -/
theorem subCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true)
    (hnf : ns.contains SubMod2N.fn = false) {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80)
    (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract64 (LibW.program.link impl) (cA "runtime.growslice") 4096 R)
    (b : Nat) {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat}
    {S : State} {ret : W64} {Qp : State → Prop}
    (hpc : S.rip = BitVec.ofNat 64 6215840)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 zp) (h6 : S.regs 6 = BitVec.ofNat 64 zl) (h8 : S.regs 8 = BitVec.ofNat 64 zc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yp) (h10 : S.regs 10 = BitVec.ofNat 64 yl)
    (h11 : S.regs 11 = BitVec.ofNat 64 yc)
    (hpre : SubMod2N.PreG R b L op zp zl zc yp yl yc n S)
    (K : ∀ s', s'.rip = retAddrOf S → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      SubMod2N.PostG R b L zp zl zc yp yl n S s' → ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have hS := SubMod2N.fullG impl hap R hns hnf hkT haT htr hsub hadd hgr b L op zp zl zc yp yl yc n
  exact ReachesRet.call_regions hS hpc ⟨h0, h3, h1, h7, h6, h8, h9, h10, h11, hpre⟩
    fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => K s' hr e1 e2 e3 e4 hrg hq

set_option maxRecDepth 20000 in
/-- a return address inside `modularInverseModPowerOfTwo`'s own segment (`seg41`, base `0x5ea8c0`) is a return
address of every callee program that does not contain it -/
theorem ra_mi {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0x610) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (0x5ea8c0 + i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg41) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5ea8c0 + i < 2 ^ 47; omega)
  simpa only [Extracted.seg41] using this

end FvModexp.Amd64.ModInv
