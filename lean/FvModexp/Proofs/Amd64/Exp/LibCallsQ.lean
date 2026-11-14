import FvModexp.Proofs.Amd64.Exp.P2PreDefs
import FvModexp.Proofs.Amd64.Exp.CallW

set_option autoImplicit false

/-!
# Shared amd64 callee-call helpers of the power-of-two chain (agent divmc s67; amd64 twins of `Arm64/Exp/CallWW`,
`Arm64/Exp/LibCalls{,Q}.{stkNatCallQ,sqrCallQ,mulCallQ,truncCall}` and `Arm64/Exp/P2Q.stkNatCallQ`)

Light module (imports only `P2PreDefs` + `CallW`) for `P2W2`, `P2W4`, `P2D` (amd64). Continuation form: at the callee
entry (`RIP` = the callee, `[RSP]` = the return address `ra`, the arguments in the Go ABIInternal registers, `X15 = 0`,
`DF` clear) and the callee's precondition, the continuation gets the return state (`RIP = ra`, `RSP + 8`, `RBP`/`R14`/
`X15` kept, regions kept) and the callee's postcondition. Copies of `P2Pre.{hypSumW, stkNatCallQ, sqrCallQ, mulCallQ,
truncCallP}` (Amd64/Exp/P2Call, P2PreSq, P2PreMu, P2PreTrC) without their `P2Pre` segment imports.
* `hypSumW`: an `Ensures` on `(onlySegments ns).link impl` (`ns ⊆ LibW.names`) as a `Summary` of `LibW.program.link impl`.
* `raSeg`: a return address inside a segment whose function `ns` leaves out.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.LibCalls

/-- a wrapper hiding a big hypothesis from `janus64_run`'s context splitting -/
structure Hide (P : Prop) : Prop where
  h : P

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- the entry of `(*stack).nat` -/
abbrev snE : Nat := 6186112

theorem snE_addr : segAddr Extracted.program StackNat.fn = snE := by decide
theorem sqr_addr : segAddr Extracted.program Q.NatSqr.fn = 6229984 := by decide
theorem mul_addr : segAddr Extracted.program Q.NatMul.fn = 6228032 := by decide
theorem trunc_addr : segAddr Extracted.program Trunc.fn = 6188320 := by decide

/-- a return address inside a segment `cs` of the extraction whose function `ns` leaves out is a return address of
the callee program -/
theorem raSeg {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    {cs : Amd64.Segment} (hcs : cs ∈ Extracted.program.segments) (hn : ns.contains cs.name = false) (i : Nat)
    (hi : i < cs.bytes.length) (hu : cs.base + i < 2 ^ 47) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (cs.base + i) :=
  CallW.retAddr_restrict hap hcs hn i hi hu

/-- an `Ensures` on `(onlySegments ns).link impl` (`ns ⊆ LibW.names`) as a `Summary` of `LibW.program.link impl`
(adapted from infra's `Amd64/Exp/SubMod2NGJ.hypSumW`) -/
theorem hypSumW {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {f : String} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hlen : args.length ≤ numIntRegs)
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibW.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.mem.readLE (s.regs 4).toNat 8) ∧
        s.xmm 15 = 0 ∧ ArgsFrom64 s 0 args ∧ s.df = false ∧ pre s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ post s s') := by
  have hS := Ensures.toSummaryIn h (A64.noExit_restrict64 hap ns) hlen (A64.codeIn_restrict_mono64 hap hns)
  rw [← LibW.eq_only] at hS
  exact hS

set_option maxRecDepth 20000 in
/-- a call of the Q-form `(*stack).nat` (`StackNatX.HypQ`, reserve level `H`) from its entry -/
theorem stkNatCallQ {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat}
    (hsn : StackNatX.HypQ impl R ns stk above) (H : Nat) {b : Nat} {L : List (Nat × Nat)} {st n : Nat}
    {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 snE) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 n) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) (bst : st < 2 ^ 64) (bn : n < 2 ^ 64)
    (hpre : StackNatX.PreQ R b L H stk above st n S)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      StackNatX.PostQ R b L H stk above st n S s' → ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := hypSumW hap hns (by simp [numIntRegs]) (hsn H b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 n))
  rw [snE_addr] at hS
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3]
  · rw [tN bst, tN bn]; exact hpre
  · rw [tN bst, tN bn] at hq
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e2 e3 e4 hrg hq

set_option maxRecDepth 20000 in
/-- a call of the Q-form `nat.sqr` (`SqrE`, window `W`, reserve level `H`) from its entry -/
theorem sqrCallQ {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {W : Nat}
    (hsq : P2Pre.SqrE impl R ns W) (H : Nat) {b : Nat} {L : List (Nat × Nat)} {zp zl zc st xp xl xc : Nat}
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 6229984) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bxc : xc < 2 ^ 64)
    (hpre : Q.NatSqr.SPre R b H L W zp zc st xp xl xc S)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      Q.NatSqr.SPost R b H L W zp zc st xp xl xc S s' → ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have hS := hypSumW hap hns (by simp [numIntRegs]) (hsq H b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 st) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc))
  rw [sqr_addr] at hS
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN bxc]; exact hpre
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN bxc] at hq
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e2 e3 e4 hrg hq

set_option maxRecDepth 20000 in
/-- a call of the Q-form `nat.mul` (`MulHypQE`, window `W`, reserve level `H`) from its entry -/
theorem mulCallQ {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {W : Nat}
    (hml : Q.DivRec.MulHypQE impl R ns W) (H : Nat) {b : Nat} {L : List (Nat × Nat)}
    {zp zl zc st xp xl xc yp yl yc : Nat}
    {S : State} {ret : W64} {Qp : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 6228032) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 st) (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl)
    (h9 : S.regs 9 = BitVec.ofNat 64 xc) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bst : st < 2 ^ 64) (bx : xp < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bxc : xc < 2 ^ 64)
    (hy0 : S.mem.readLE ((S.regs 4).toNat + 8) 8 = yp) (hy1 : S.mem.readLE ((S.regs 4).toNat + 16) 8 = yl)
    (hy2 : S.mem.readLE ((S.regs 4).toNat + 24) 8 = yc)
    (hpre : Q.NatMul.MPre R b H L W zp zc st xp xl xc yp yl yc S)
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      Q.NatMul.MPost R b H L W zp zc st xp xl xc yp yl yc S s' → ReachesRet (LibW.program.link impl) ret s' Qp) :
    ReachesRet (LibW.program.link impl) ret S Qp := by
  have hS := hypSumW hap hns (by simp [numIntRegs]) (hml H b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 st) (BitVec.ofNat 64 xp) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) yp yl yc)
  rw [mul_addr] at hS
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN bxc]; exact ⟨hy0, hy1, hy2, hpre⟩
  · rw [tN bz, tN bzc, tN bst, tN bx, tN bxl, tN bxc] at hq
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e2 e3 e4 hrg hq

set_option maxRecDepth 20000 in
/-- a call of `nat.trunc` (`Trunc.Hyp2`) at its entry, continuation over the callee's postcondition -/
theorem truncCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat}
    (htr : Trunc.Hyp2 impl R ns stk above) {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl xc n : Nat}
    {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 6188320) (hrd : S.mem.readLE (S.regs 4).toNat 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 x) (h6 : S.regs 6 = BitVec.ofNat 64 xl) (h8 : S.regs 8 = BitVec.ofNat 64 xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 n) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (bz : zp < 2 ^ 64) (bzc : zc < 2 ^ 64) (bx : x < 2 ^ 64) (bxl : xl < 2 ^ 64)
    (bn : n < 2 ^ 64)
    (hpre : EvenHyp.TruncPre R b L stk above zp zl zc x xl n S) (hnorm : NatNorm S.mem x xl ∨ (n + 63) / 64 ≤ xl)
    (hcp : zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n))
    (K : ∀ s', s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = S.regs 4 + 8 → s'.regs 5 = S.regs 5 →
      s'.regs 14 = S.regs 14 → s'.xmm 15 = S.xmm 15 → s'.mem.regions = S.mem.regions →
      EvenHyp.TruncPost R b L stk above zp zc x xl n S s' → ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := hypSumW hap hns (by simp [numIntRegs]) (htr b L (BitVec.ofNat 64 zp) (BitVec.ofNat 64 zl)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 x) (BitVec.ofNat 64 xl) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 n))
  rw [trunc_addr] at hS
  have hzl : zl < 2 ^ 64 := by have := hpre.2.2.1; omega
  refine ReachesRet.call_regions hS hpc ⟨?_, hx15, ?_, hdf, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [hrd]; exact hra
  · simp [ArgsFrom64, argReg, intArgRegs, h0, h3, h1, h7, h6, h8, h9]
  · rw [tN bz, tN hzl, tN bzc, tN bx, tN bxl, tN bn]; exact ⟨hpre, hnorm, hcp⟩
  · rw [tN bz, tN bzc, tN bx, tN bxl, tN bn] at hq
    exact K s' (by rw [hr, retAddrOf_eq, hrd]) e1 e2 e3 e4 hrg hq

end FvModexp.Amd64.LibCalls
