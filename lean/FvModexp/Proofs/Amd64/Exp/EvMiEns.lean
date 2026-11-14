import FvModexp.Proofs.Amd64.Exp.ModInv
import FvModexp.Proofs.Amd64.Exp.EvJ11

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the `MiEns` premise from infra's `ModInv.ens` (asm s64)

`miEns_of`: infra's amd64 `FvModexp.Amd64.ModInv.ens` (Amd64/Exp/ModInv.lean) instantiates `ExpEven.MiEns` (EvJ11)
outright — same program (`ModInv.names = LibW.names`), entry, arguments, `PreQ` / `PostQ`; its callee premises become
`miEns_of`'s. EvenSum's composition discharges `MiEns` with it.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

open FvModexp.Amd64.ModInv in
theorem miEns_of {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    {nsS nsT nsM nsL : List String} (hnsS : ∀ x, nsS.contains x = true → LibW.names.contains x = true)
    (hnsT : ∀ x, nsT.contains x = true → LibW.names.contains x = true)
    (hnsM : ∀ x, nsM.contains x = true → LibW.names.contains x = true)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true)
    (hnfS : nsS.contains ModInv.fn = false) (hnfT : nsT.contains ModInv.fn = false)
    (hnfM : nsM.contains ModInv.fn = false)
    (hnfL : nsL.contains ModInv.fn = false) (hnfTS : nsT.contains SubMod2N.fn = false)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    {kc : Nat} (hkc : SubMod2N.K ≤ kc)
    {kS : Nat} (hsq : SqrE impl R nsS kS) (hkS : kS ≤ kc) (hkS1 : sqrW 513 ≤ kS)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R nsT stkT aboveT) (hkT : stkT ≤ 4440) (haT : aboveT ≤ 80)
    {kM : Nat} (hmu : Q.DivRec.MulHypQE impl R nsM kM) (hkM : kM ≤ kc) (hkM1 : mulWX64 ≤ kM)
    {stkL aboveL : Nat} (hls : Lsh.Hyp2 impl R nsL stkL aboveL) (hkL : stkL ≤ kc) (haL : aboveL ≤ 88)
    (hsub : SubMod2N.SubHypR0 impl R) (hadd : SubMod2N.AddHypR impl R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat}
    (hsm : ∀ a a', a ≤ a' → sqrCQ a ≤ sqrC a') (hsm' : ∀ a a', a ≤ a' → sqrC a ≤ sqrC a')
    (hmm : ∀ a a' c, a ≤ a' → mulCQ a c ≤ mulC a' c) : MiEns impl R kc sqrC mulC :=
  fun H B L zp zl zc st xp xl xc n =>
    ModInv.ens hap hnsS hnsT hnsM hnsL hnfS hnfT hnfM hnfL hnfTS hmk hkc hsq hkS hkS1 htr hkT haT hmu hkM hkM1 hls hkL
      haL hsub hadd hgr hsm hsm' hmm H B L zp zl zc st xp xl xc n

end FvModexp.Amd64.ExpEven
