import FvModexp.Proofs.Amd64.Exp.OddPro
import FvModexp.Proofs.Amd64.Exp.OddPost

set_option autoImplicit false

/-!
# `nat.expNNOdd` (amd64): `ens` (CONVENTIONS §3; agent expmc s64; twin of `Arm64.OddFun`)

`z.expNNOdd(stk, x, y, m)` returns `x^y mod m` (see `PreD`/`PostD`): the prologue (`pro`), the call of window-4
(`ExpW4.ens`, `len y > 1`, frame `sp - 0x78`, `K - 0x78`) or window-2 (`ExpW2.ens`, frame `sp + 0xa0`, `K + 0xa0`), the
epilogue (`epi`). Premises: the live runtime contracts and `nat.div`'s shape `ExpHyp.DivHypL` (as the windows). The
return address is only the ABI's (`RetAddr`); `PreD` does not mention it.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.ExpOdd

/-- an `Ensures` on `(Extracted.program.onlySegments ns).link impl` (`ns ⊆ LibOdd.names`) as a `Summary` of
`LibOdd.program.link impl` (the `LibOdd` twin of `CallW.hypSum`) -/
theorem hypSumO {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibOdd.names.contains x = true) {f : String} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hlen : args.length ≤ numIntRegs)
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibOdd.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.mem.readLE (s.regs 4).toNat 8) ∧
        s.xmm 15 = 0 ∧ ArgsFrom64 s 0 args ∧ s.df = false ∧ pre s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ post s s') := by
  have hS := Ensures.toSummaryIn h (A64.noExit_restrict64 hap ns) hlen (A64.codeIn_restrict_mono64 hap hns)
  rw [← LibOdd.eq_only] at hS
  exact hS

set_option maxHeartbeats 64000000 in
theorem w_sub : ∀ x, LibW.names.contains x = true → LibOdd.names.contains x = true := MontW.sub_of_all (by decide)

theorem fn_seg : Extracted.seg21.name = fn := by decide

set_option maxRecDepth 20000 in
theorem ra_of {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) (i : Nat) (hi : i < 0x11b) :
    RetAddr ((Extracted.program.onlySegments LibW.names).link impl) (6205248 + i) := by
  have := CallW.retAddr_restrict hap (cs := Extracted.seg21) (ns := LibW.names)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true])
    (by rw [fn_seg]; decide) i (Nat.lt_of_lt_of_le hi (by decide)) (by show 0x5eaf40 + i < 2 ^ 47; omega)
  simpa only [Extracted.seg21] using this

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_self (v : BitVec 64) : BitVec.ofNat 64 v.toNat = v := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem rsp_ge {v : BitVec 64} (h : v = BitVec.ofNat 64 (v.toNat - 0x388 + 0x388)) :
    v.toNat - 0x388 + 0x388 = v.toNat := by
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat] at h1
  have := v.isLt
  omega

theorem add8 {v w : BitVec 64} {t : Nat} (hv : v.toNat = t) (hw : w = BitVec.ofNat 64 (t + 8)) (ht : t + 8 < 2 ^ 64) :
    w = v + 8 := by
  subst hw
  apply BitVec.eq_of_toNat_eq
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h8, hv]
  try omega

end FvModexp.Amd64.ExpOdd
