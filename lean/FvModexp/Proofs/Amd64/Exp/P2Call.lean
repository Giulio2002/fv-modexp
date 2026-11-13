import FvModexp.Proofs.Amd64.Exp.P2PreJ

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): callee-call bridges (agent divmc s62; twin of `Arm64/Exp/P2PreCall` +
`Arm64/Exp/P2Q.stkNatCallQ`)

* `hypSumW` (adapted from infra's `Amd64/Exp/SubMod2NGJ.hypSumW`): an `Ensures` on `(onlySegments ns).link impl`
  (`ns ⊆ LibW.names`) as a `Summary` of `LibW.program.link impl`.
* `ra_bp`: a return address inside the function's own segment (`seg60`, base `0x5e8900`, `0x68a` bytes).
* `stkNatCallQ`: a call of divmc's Q-form `(*stack).nat` (`StackNatX.HypQ`) from its entry.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

/-- a wrapper hiding a big hypothesis from `janus64_run`'s context splitting -/
structure Hide (P : Prop) : Prop where
  h : P

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

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
/-- a return address inside the function's own segment (`seg60`, base `0x5e8900`) is a return address of every callee
program that does not contain the function -/
theorem ra_bp {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hn : ns.contains fn = false) (i : Nat) (hi : i < 0x68a) :
    RetAddr ((Extracted.program.onlySegments ns).link impl) (0x5e8900 + i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg60) (ns := ns)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) hn i
    (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5e8900 + i < 2 ^ 47; omega)
  simpa only [Extracted.seg60] using this

/-- `runtime.gcWriteBarrier2`'s contract address -/
abbrev wbE : Nat := 4761248

theorem wbE_eq : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = wbE := by decide

theorem snE_addr : segAddr Extracted.program StackNat.fn = snE := by decide

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

end FvModexp.Amd64.P2Pre
