import FvModexp.Proofs.Amd64.Exp.SubMod2NS1
import FvModexp.Proofs.Amd64.Exp.SubMod2NS2
import FvModexp.Proofs.Amd64.Exp.SubMod2NS3
import FvModexp.Proofs.Amd64.Exp.SubMod2NS4A
import FvModexp.Proofs.Amd64.Exp.SubMod2NS4B
import FvModexp.Proofs.Amd64.Exp.SubMod2NS4C

/-!
# **`nat.subMod2N`** (go-bigmodexpfix nat.go:1726), amd64 — the summary (agent infra)

`z.subMod2N(z, y, n)` (`x = z`, `y`'s array apart from `z`'s, `cap z ≥ ⌈n/64⌉`) returns a normalised nat holding
`Exp.subMod2N Z Y n` (= `(Z - Y) mod 2^n`, `ExpEven.subMod2N_correct`), in `z`'s array or a fresh one. The nine
register arguments `z, x = z, y` are `RAX..R11`; `n` is the tenth argument, on the stack at `[RSP + 8]` (`Ent`).
Callee premises: `TruncHyp` (asm's `nat.trunc`), `SubHypR` / `AddHypR` (divmc's `nat.sub` / `nat.add` with the reuse
conjunct, `cap < 2^40` and `DF` kept, NOTES-divmc [infra s5/s6]); `nat.cmp` is asm's verified `cmp_summary`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.EvenHyp

/-- the whole function from its entry, as a `Summary` on the exp layer's program -/
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : TruncHyp impl R ns stkT aboveT)
    (hsub : SubHypR impl R) (hadd : AddHypR impl R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Summary (LibExp.program.link impl) 6215840
      (fun s => s.regs 0 = BitVec.ofNat 64 zp ∧ s.regs 3 = BitVec.ofNat 64 zl ∧ s.regs 1 = BitVec.ofNat 64 zc ∧
        s.regs 7 = BitVec.ofNat 64 zp ∧ s.regs 6 = BitVec.ofNat 64 zl ∧ s.regs 8 = BitVec.ofNat 64 zc ∧
        s.regs 9 = BitVec.ofNat 64 yp ∧ s.regs 10 = BitVec.ofNat 64 yl ∧ s.regs 11 = BitVec.ofNat 64 yc ∧
        Pre R b L op zp zl zc yp yl yc n s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ Post R b L zp zl zc yp yl n s s') := by
  intro s hpc ⟨h0, h3, h1, h7, h6, h8, h9, h10, h11, hpre⟩
  have k5 := s4c impl hap R hns hnf hkT haT htr hadd b L op zp zl zc yp yl yc n s
  have k4 := s4b impl R b L op zp zl zc yp yl yc n s k5
  have k3 := s4a impl R b L op zp zl zc yp yl yc n s k4
  have k2 := s3 impl hap R hsub b L op zp zl zc yp yl yc n s k3
  have k1 := s2 impl hap R hns hnf hkT haT htr b L op zp zl zc yp yl yc n s k2
  exact s1 impl hap R hns hnf hkT haT htr b L op zp zl zc yp yl yc n s hpc h0 h3 h1 h7 h6 h8 h9 h10 h11 hpre k1

def names : List String := LibExp.names

/-- divmc's verified `nat.sub` (`NatSub.ensR`) is the `SubHypR` premise -/
theorem subHypR_of (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) : SubHypR impl R :=
  fun b L zp zl zc xp xl xc yp yl yc => NatSub.ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc

/-- divmc's verified `nat.add` (`NatAdd.ensR`) is the `AddHypR` premise -/
theorem addHypR_of (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) : AddHypR impl R :=
  fun b L zp zl zc xp xl xc yp yl yc => NatAdd.ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc

/-- **`nat.subMod2N`** (amd64), `z.subMod2N(z, y, n)`: a normalised nat holding `Exp.subMod2N Z Y n`, in `z`'s array
or a fresh one; writes only `z`'s array, the window and runtime memory; no panic, no fault. (`n` is passed on the
stack: `Pre`'s `Ent` conjunct.) -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : TruncHyp impl R ns stkT aboveT)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 zp, BitVec.ofNat 64 zl,
        BitVec.ofNat 64 zc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc]
      (Pre R b L op zp zl zc yp yl yc n) (Post R b L zp zl zc yp yl n) := by
  rw [show names = LibExp.names from rfl, ← LibExp.eq_only, show segAddr Extracted.program fn = 6215840 by decide]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hns hnf hkT haT htr (subHypR_of impl hap R hmk hmv) (addHypR_of impl hap R hmk hmv) b L op zp zl zc yp yl yc n) hret
    (by rw [h_rip]) (by rw [retAddrOf, h_ret])
    ⟨h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6, h_a7, h_a8, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps `LibExp.names` -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {ns : List String} (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : TruncHyp impl R ns stkT aboveT)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) :=
  CallW.hypSum hap (fun _ h => h) (by simp [numIntRegs])
    (ens impl hap R hns hnf hkT haT htr hmk hmv b L op zp zl zc yp yl yc n)

end FvModexp.Amd64.SubMod2N
