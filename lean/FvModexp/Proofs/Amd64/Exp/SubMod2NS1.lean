import FvModexp.Proofs.Amd64.Exp.SubMod2NS1Z
import FvModexp.Proofs.Amd64.Exp.SubMod2NS1N
import FvModexp.Proofs.Amd64.Exp.SubMod2NS1T

/-!
# `nat.subMod2N` (amd64): entry → `J1` (agent infra): case split `len x = 0` / `x.bitLen() ≤ n` / truncate
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
theorem s1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : TruncHyp impl R ns stkT aboveT)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 6215840)
    (h0 : s.regs 0 = BitVec.ofNat 64 zp) (h3 : s.regs 3 = BitVec.ofNat 64 zl) (h1 : s.regs 1 = BitVec.ofNat 64 zc)
    (h7 : s.regs 7 = BitVec.ofNat 64 zp) (h6 : s.regs 6 = BitVec.ofNat 64 zl) (h8 : s.regs 8 = BitVec.ofNat 64 zc)
    (h9 : s.regs 9 = BitVec.ofNat 64 yp) (h10 : s.regs 10 = BitVec.ofNat 64 yl) (h11 : s.regs 11 = BitVec.ofNat 64 yc)
    (hpre : Pre R b L op zp zl zc yp yl yc n s) (k1 : J1 impl R b L op zp zl zc yp yl yc n s) :
    Goal impl R b L zp zl zc yp yl n s s := by
  by_cases hz0 : zl = 0
  · exact s1z impl R b L op zp zl zc yp yl yc n s hpc h0 h3 h1 h7 h6 h8 h9 h10 h11 hpre hz0 k1
  by_cases hc : 64 * (zl - 1) + Aux.bitLen (s.mem.readLE (zp + 8 * (zl - 1)) 8) ≤ n
  · exact s1n impl R b L op zp zl zc yp yl yc n s hpc h0 h3 h1 h7 h6 h8 h9 h10 h11 hpre hz0 hc k1
  · exact s1tr impl hap R hns hnf hkT haT htr b L op zp zl zc yp yl yc n s hpc h0 h3 h1 h7 h6 h8 h9 h10 h11 hpre hz0 hc k1

end FvModexp.Amd64.SubMod2N
