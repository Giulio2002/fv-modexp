import FvModexp.Proofs.Amd64.Exp.SubMod2NS2Z
import FvModexp.Proofs.Amd64.Exp.SubMod2NS2N
import FvModexp.Proofs.Amd64.Exp.SubMod2NS2T

/-!
# `nat.subMod2N` (amd64): `J1` → `J2` (agent infra): case split `len y = 0` / `y.bitLen() ≤ n` / truncate
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

set_option maxRecDepth 20000 in
theorem s2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibExp.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80) (htr : TruncHyp impl R ns stkT aboveT)
    (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat) (s : State)
    (k2 : J2 impl R b L op zp zl zc yp yl yc n s) : J1 impl R b L op zp zl zc yp yl yc n s := by
  by_cases hy0 : yl = 0
  · exact s2z impl R b L op zp zl zc yp yl yc n s hy0 k2
  by_cases hc : 64 * (yl - 1) + Aux.bitLen (s.mem.readLE (yp + 8 * (yl - 1)) 8) ≤ n
  · exact s2n impl R b L op zp zl zc yp yl yc n s hy0 hc k2
  · exact s2tr impl hap R hns hnf hkT haT htr b L op zp zl zc yp yl yc n s hy0 hc k2

end FvModexp.Amd64.SubMod2N
