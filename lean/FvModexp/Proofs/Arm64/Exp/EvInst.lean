import FvModexp.Proofs.Arm64.Exp.EvSum
import FvModexp.Proofs.Arm64.Exp.EvMulG
import FvModexp.Proofs.Arm64.Exp.EnsWiden
import FvModexp.Proofs.Arm64.Exp.ModInv
import FvModexp.Proofs.Arm64.Exp.SubMod2NGEns
import FvModexp.Proofs.Arm64.Nat.StackNat
import FvModexp.Proofs.Arm64.Nat.Lsh
import FvModexp.Proofs.Arm64.Nat.Rsh
import FvModexp.Proofs.Arm64.Nat.Trunc
import FvModexp.Proofs.Arm64.Nat.TruncE0
import FvModexp.Proofs.Arm64.Nat.NatAdd
import FvModexp.Proofs.Arm64.Nat.NatAdd0
import FvModexp.Proofs.Arm64.Nat.NatSub0
import FvModexp.Proofs.Arm64.Nat.SqrHypX
import FvModexp.Proofs.Arm64.Nat.MulHypX
import FvModexp.Proofs.Arm64.NatQ.SqrHypQ
import FvModexp.Proofs.Arm64.NatQ.MulHypQ

set_option autoImplicit false

/-!
# **`nat.expNNEven`** arm64 — `ExpEven.fullI`: the export with every callee summary plugged in (agent infra)

`fullI` = `ExpEven.full` with the PROVED callee summaries: `(*stack).nat` (divmc `StackNat.ensL`), `nat.lsh`/`nat.rsh`
(`Lsh.ens`, `Rsh.ens`), `nat.mul` (`NatMulG.hypG`, cost `mulC`, window `mulWX`), `nat.trunc` (asm `Trunc.ens0`; `Trunc.ens`
inside `subMod2N`/`modInv`), `nat.add` (divmc `NatAdd.ensR0`; `ensR` inside `subMod2N`), `nat.sub` (`NatSub.ensR0`),
`nat.subMod2N` (`SubMod2N.ensG`), `nat.modularInverseModPowerOfTwo` (`ModInv.ens`, the bridged Q-form, with divmc's Q-form
`nat.sqr` / `nat.mul` (`Q.NatSqr.hypQ` / `Q.NatMul.hypQ`, costs `sqrCQ` / `mulCQ`), frame `kc = sqrWX`). Each summary is moved to the composition's one function list with `EnsWiden.ens_widen`.

Remaining premises: the Janus runtime contracts (on `Extracted.program.ofImpl impl`; `MemmoveZeroLive` is the local copy
of Janus PR #2 → re-pin to v0.3.1), expmc's `ExpNNHypNE1` (`ExpNNHypNE.toNE1`) and the monotonicity of expmc's expNN
costs, and the frame depth `stk`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp
open FvModexp.Arm64.EnsWiden (ens_widen)
open Janus.Contracts.EqHashModel (CodeIn)

namespace FvModexp.Arm64.ExpEven

/-- the functions of `modInv`'s callees (`sqr`, `trunc`, `mul`, `lsh`) -/
def nsMi : List String := Q.NatSqr.names ++ Trunc.names ++ Q.NatMul.names ++ Lsh.names

/-- the functions of `expNNEven`'s directly summarised callees -/
def nsE : List String := StackNat.names ++ Lsh.names ++ Rsh.names ++ NatMul.names ++ Trunc.names

set_option maxHeartbeats 64000000 in
theorem nsMi_sub : ∀ x, nsMi.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide)
set_option maxHeartbeats 64000000 in
theorem nsMi_fn : nsMi.contains ModInv.fn = false := by decide
set_option maxHeartbeats 64000000 in
theorem nsMi_fnS : nsMi.contains SubMod2N.fn = false := by decide
set_option maxHeartbeats 64000000 in
theorem nsE_sub : ∀ x, nsE.contains x = true → LibNE.names.contains x = true := MontW.sub_of_all (by decide)
set_option maxHeartbeats 64000000 in
theorem nsE_fn : nsE.contains fn = false := by decide
set_option maxHeartbeats 64000000 in
theorem trW_sub : ∀ x, Trunc.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide)
set_option maxHeartbeats 64000000 in
theorem trW_fnS : Trunc.names.contains SubMod2N.fn = false := by decide

set_option maxHeartbeats 64000000 in
theorem sub_mi : (∀ x, Q.NatSqr.names.contains x = true → nsMi.contains x = true) ∧
    (∀ x, Trunc.names.contains x = true → nsMi.contains x = true) ∧
    (∀ x, Q.NatMul.names.contains x = true → nsMi.contains x = true) ∧
    (∀ x, Lsh.names.contains x = true → nsMi.contains x = true) :=
  ⟨MontW.sub_of_all (by decide), MontW.sub_of_all (by decide), MontW.sub_of_all (by decide),
    MontW.sub_of_all (by decide)⟩

set_option maxHeartbeats 64000000 in
theorem sub_e : (∀ x, StackNat.names.contains x = true → nsE.contains x = true) ∧
    (∀ x, Lsh.names.contains x = true → nsE.contains x = true) ∧
    (∀ x, Rsh.names.contains x = true → nsE.contains x = true) ∧
    (∀ x, NatMul.names.contains x = true → nsE.contains x = true) ∧
    (∀ x, Trunc.names.contains x = true → nsE.contains x = true) :=
  ⟨MontW.sub_of_all (by decide), MontW.sub_of_all (by decide), MontW.sub_of_all (by decide),
    MontW.sub_of_all (by decide), MontW.sub_of_all (by decide)⟩

theorem mulWX_le : mulWX ≤ NatSqr.sqrWX := by simp only [mulWX, NatSqr.sqrWX, sqrW, ksqrW]; omega

theorem sqrWX_eq : NatSqr.sqrWX = 70592 := by simp only [NatSqr.sqrWX, sqrW, ksqrW]

/-- `ModInv.ens` (bridged Q-form) with every callee proved: `MiEns` at `kc = sqrWX`, costs `sqrCQ` / `mulCQ` -/
theorem miEns {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    MiEns impl R NatSqr.sqrWX sqrCQ mulCQ := by
  obtain ⟨s1, s2, s3, s4⟩ := sub_mi
  have hsq : EvenHyp.SqrHypQ impl R nsMi NatSqr.sqrWX 64 sqrCQ := fun H b L z zl zc st x xl xc =>
    ens_widen hap s1 (Q.NatSqr.hypQ impl hap R hmk hgr hmc hmv hwb H b L z zl zc st x xl xc)
  have htr : Trunc.Hyp2 impl R nsMi 4208 64 := fun b L z zl zc x xl xc n =>
    ens_widen hap s2 (Trunc.ens impl hap R hmk hmv b L z zl zc x xl xc n)
  have hmu : EvenHyp.MulHypQ impl R nsMi mulWX 88 mulCQ := fun H b L z zl zc st x xl xc y yl yc =>
    ens_widen hap s3 (Q.NatMul.hypQ impl hap R hmk hgr hmc hmv hwb H b L z zl zc st x xl xc y yl yc)
  have hls : Lsh.Hyp2 impl R nsMi 4256 64 := fun b L z zl zc x xl xc sh =>
    ens_widen hap s4 (Lsh.ens impl hap R hmk hmv hmc b L z zl zc x xl xc sh)
  have hsub : SubMod2N.SubHypR0 impl R := fun b L zp zl zc xp xl xc yp yl yc =>
    NatSub.ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc
  have hadd : SubMod2N.AddHypR impl R := fun b L zp zl zc xp xl xc yp yl yc =>
    NatAdd.ensR impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc
  have hW := sqrWX_eq
  intro ℓ b L zp zl zc st xp xl xc n
  exact ModInv.ens hap nsMi_sub nsMi_fn nsMi_fnS hmk (by omega) hsq (Nat.le_refl _) (by omega) htr (by omega)
    (by omega) hmu mulWX_le (by omega) hls (by omega) (by omega) (by omega) hsub hadd hgr
    (fun a a' h => sqrCQ_mono h) (fun a a' c c' h1 h2 => mulCQ_mono h1 h2)
    ℓ b L zp zl zc st xp xl xc n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`nat.expNNEven`** (arm64) with every callee summary except `nat.expNN` (expmc's `ExpNNHypNE1`) plugged in -/
theorem fullI {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv}
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {KN : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    (hE : EvenHyp.ExpNNHypNE1 impl R KN costF needR costR needS needP costS costP)
    (hKN : 4304 ≤ KN)  (hKN2 : KN + 288 ≤ 2 ^ 20)
    (hRm : ∀ x a a', a ≤ a' → needR x a ≤ needR x a')
    (hSm : ∀ x y a a', a ≤ a' → needS x y a ≤ needS x y a')
    (hPm : ∀ x y a a', a ≤ a' → needP x y a ≤ needP x y a')
    {bU cU : Nat → Nat → Nat → Nat → Nat → Nat}
    (hNB : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      NBudE costF costR costS costP x y a l k ≤ bU x y a' l' k')
    (hNC : ∀ x y a a' l l' k k', a ≤ a' → l ≤ l' → k ≤ k' →
      ExpN.NCost costF costR costS costP x y a l k ≤ cU x y a' l' k')
    {stk : Nat} (hk1 : 71168 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 336) (hk3 : KN + 1648 ≤ stk) :
    EvenSum impl R stk 112 (needE needR needS needP) (costE costF costR costS costP bU cU sqrCQ mulCQ mulC) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := sub_e
  have hc : CodeIn (Extracted.program.ofImpl impl) (LibNE.program.link impl) := by
    rw [LibNE.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibNE.names
  have hmvE : MemmoveLive (LibNE.program.link impl) mvE 4096 R := by
    have := MemmoveLive.of_codeIn hc hmv
    rwa [show cA "runtime.memmove" = mvE by decide] at this
  have hmzE : MemmoveZeroLive (LibNE.program.link impl) mvE 4096 R := by
    have := MemmoveZeroLive.of_codeIn hc hmz
    rwa [show cA "runtime.memmove" = mvE by decide] at this
  have hmkE : MakesliceLiveContract (LibNE.program.link impl) mkE 4096 R := by
    have := MakesliceLiveContract.of_codeIn hc hmk
    rwa [show cA "runtime.makeslice" = mkE by decide] at this
  have hsn : StackNat.HypL impl R nsE 4208 24 := fun b L st n =>
    ens_widen hap e1 (StackNat.ensL impl hap R hgr hmc hwb b L st n)
  have hlh : Lsh.Hyp2 impl R nsE 4256 64 := fun b L z zl zc x xl xc sh =>
    ens_widen hap e2 (Lsh.ens impl hap R hmk hmv hmc b L z zl zc x xl xc sh)
  have hrh : Rsh.Hyp impl R nsE 4240 64 := fun b L z zl zc x xl xc sh =>
    ens_widen hap e3 (Rsh.ens impl hap R hmk hmv b L z zl zc x xl xc sh)
  have hmu : MulHypG impl R nsE mulWX 88 mulC := fun b L z zl zc st x xl xc y yl yc =>
    ens_widen hap e4 (NatMulG.hypG impl hap R hmk hgr hmc hmv hwb b L z zl zc st x xl xc y yl yc)
  have htr : TrHyp0 impl R nsE 4208 64 := fun b L z zl zc x xl xc n =>
    ens_widen hap e5 (Trunc.ens0 impl hap R hmk hmv b L z zl zc x xl xc n)
  have hadd : AddHypR0 impl R := fun b L zp zl zc xp xl xc yp yl yc =>
    NatAdd.ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc
  have hsub : SubMod2N.SubHypR0 impl R := fun b L zp zl zc xp xl xc yp yl yc =>
    NatSub.ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc
  have hSE : SubMod2N.EnsG impl R :=
    SubMod2N.ensG impl hap R trW_sub trW_fnS (by omega) (by omega) (Trunc.ens impl hap R hmk hmv) hsub hmk hmv hgr
  have hMi := miEns hap hmk hgr hmc hmv hwb
  have hW := sqrWX_eq
  have hmW : mulWX = 30208 := rfl
  exact full hap nsE_sub nsE_fn hsn (by omega) hlh (by omega) hrh (by omega) hE hKN hKN2 hmvE hmzE hmkE hSE hMi
    (by omega) hmu (by omega) htr hadd hRm hSm hPm hNB hNC
    (fun a a' h => sqrCQ_mono h) (fun a a' c c' h1 h2 => mulCQ_mono h1 h2)
    (fun ℓ ℓ' a a' c c' h1 h2 h3 => mulC_mono h1 h2 h3) (by omega) hk2
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end FvModexp.Arm64.ExpEven
