import FvModexp.Proofs.Amd64.Exp.CalleeInstQ
import FvModexp.Proofs.Amd64.Exp.P2W2E
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.StubsGrow

set_option autoImplicit false

/-!
# Row: `nat.expNNPowerOfTwoWindowSize2` (amd64) on the Run extraction (agent divmc s75; twin of Arm64/Exp/P2W2Row)

`correctness` = `P2W2.ens` (the `PreC` / `CPostR` form of `fullC`) with the PROVED closed Q-form callees of
`CalleeInstQ` (`(*stack).nat`, `nat.sqr`, `nat.mul`, `nat.trunc` on `nsQ`), callee window `kc = mulWX64 = 30792`,
moved to `Extracted.program.link impl` (`Ensures.full64`); window `[RSP - stk, RSP + 0x60)` with
`41984 ≤ stk ≤ 2^20 + 0x1d8`. Runtime premises: the live `growslice`, `memclrNoHeapPointers`, `memmove`, `makeslice`,
`newobject`, `gcWriteBarrier2` contracts. `y` is the stack argument (`RSP + 8 …`), `logM` is `R10`.
`Witness.nonvacuous`: `z = nil`, the stack `{w, 0, 4}`, `x = [3]`, `y = [5]`, `logM = 8` (`3^5 mod 2^8`), `natOne`
(header outside the extracted data, its word in the `OB` object), a 64 KiB stack region, window `stk = 41984`, the
shared witness runtime, one call-site state per contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W2Row

open FvModexp.Amd64.CalleeInstQ

/-- **window-2 power-of-two** (amd64): `z.expNNPowerOfTwoWindowSize2(stk, x, y, logM)` returns `x^y mod 2^logM` for
odd `x`, `y > 0`, `2 ≤ logM ≤ 2^13` (`P2W2.PreC` / `NHyp.CPostR`), for every runtime meeting the live allocation /
copy / clear / write-barrier contracts. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice")
      4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject")
      4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (stk : Nat) (hk0 : 41984 ≤ stk) (hk2 : stk ≤ 2 ^ 20 + 0x1d8)
    (zp zl zc st xp xl xc yp yl yc lm : Nat) (hzp : zp < 2 ^ 64) (hxc : xc < 2 ^ 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program P2W2.fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 lm]
      (fun s => NHyp.StkArg s 0 yp yl yc ∧
        P2W2.PreC R b L stk (P2W2.costB (stLen s.mem st) yl lm) zp zl zc st xp xl yp yl lm s ∧ P2W2.EX xp xl s)
      (fun s s' => NHyp.CPostR R b L stk 0x60 zp zc st (natVal s.mem xp xl ^ natVal s.mem yp yl % 2 ^ lm)
        (P2W2.costB (stLen s.mem st) yl lm) s s') :=
  Ensures.full64 hap (by simp [numIntRegs])
    (P2W2.ens hap sub nf2 nfP hgr hmc hmv hmk hno hwb (kc := mulWX64) (by decide)
      (sn hap hgr hmc hwb) (by decide) (by decide) (sq hap hgr hmc hmv hmk hwb _) (by decide) (Nat.le_refl _)
      (mu hap hgr hmc hmv hmk hwb _) (Nat.le_refl _) (Nat.le_refl _) (tr hap hmv hmk) (by decide) (by decide)
      b L stk (by omega) (by simp only [P2Pre.K, mulWX64]; omega) hk2 zp zl zc st xp xl xc yp yl yc lm hzp hxc)

end FvModexp.Amd64.P2W2Row
