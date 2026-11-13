import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2Posts
import FvModexp.Proofs.Arm64.Exp.W2Ctx
import FvModexp.Proofs.Arm64.Exp.W2RR
import FvModexp.Proofs.Arm64.Exp.W2Snc

/-!
# window-2 (arm64): `ZZ` and the statement `RRSpec` of `W2RRC.rrRetC` (`divRet → RET`)

`ZZ` is hoisted (s67) out of `W2RRC` (unchanged). `RRSpec` is `rrRetC`'s statement verbatim; `W2DivS.divStep` and its
callers up to `W2En.enStep` take it as a hypothesis and `W2FunE` discharges it with `W2Comp.rrSpec`, so the prologue
segment does not import the `RR → RET` segment (row import-chain cut).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf FinEnv)

/-- the facts about `zz` (the `lsh` result) at `divRet` (s27: apart from the WHOLE stack array, for `ResSep`) -/
@[reducible] def ZZ (R : RtInv) (L : List (Nat × Nat)) (g sp n mp xp yp ylen zp zc st l0 zzp zzc : Nat) (M : Memory) :
    Prop :=
  Buf R L g sp n M zzp zzc ∧ zzp % 8 = 0 ∧ Apart zzp (8 * zzc) mp (8 * n) ∧ Apart zzp (8 * zzc) yp (8 * ylen) ∧
  Apart zzp (8 * zzc) xp (8 * n) ∧ Apart zzp (8 * zzc) (sp - 4304) 16 ∧ Apart zzp (8 * zzc) st 24 ∧
  Apart zzp (8 * zzc) (stW M st) (8 * stCap M st) ∧ (2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc))

set_option linter.unusedVariables false in
/-- the statement of `rrRetC` (s67 import-chain cut: taken as a hypothesis by its callers, composed at the top) -/
def RRSpec : Prop :=
  ∀ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.HypL impl R StackNat.names 4208 24)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 t rp rl rc zzp zzc : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (ex : List (Nat × Nat))
    (hC : Ctx R L g sp K n mp mc Mv xp xc Xv yp ylen Y yi zp zc st n0 l0 ret r29 ex M)
    (hZ : ZZ R L g sp n mp xp yp ylen zp zc st l0 zzp zzc M)
    (ht : t < 2 ^ 64) (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n)
    (hslen : stLen M st + 5 * n + 3 ≤ 2 ^ 16)
    (hbud : blockSize (8 * n) true + stackNatCost (stLen M st) (5 * n) + blockSize (8 * (2 * n + 4)) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (hrl0 : 0 < rl) (hrln : rl ≤ n) (hrc : rc < 2 ^ 40) (hrp : rp < 2 ^ 64)
    (hra : M.accessible rp (8 * rl) false = true) (hr48 : rp + 8 * rl ≤ 2 ^ 48)
    (hrh : InRanges rp (8 * rl) L ∨ Outside rp (8 * rl) R.rt) (hrw : Apart rp (8 * rl) (sp - 4288) (4288 + 752))
    (hrS : Apart rp (8 * rl) st 24) (hrF : Apart rp (8 * rl) (stFree M st).1 (stFree M st).2)
    (hzr : Apart zzp (8 * zzc) rp (8 * rl)) (hzz0 : M.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 divRet) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 rp) (h4 : S.regs 4 = BitVec.ofNat 64 rl) (h5 : S.regs 5 = BitVec.ofNat 64 rc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M),
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ (M1 : Memory) (rrp rrc onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
        RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc ∧ OneChain R b L L2 b2 sp n st M1 M2 ∧
        RetPost R b2 L2 g sp n mp mc t (stW M2 st + 8 * stLen M st) yp ylen Y yi zp zc zzp zzc st n0 onep r18 r29
          Mv Xv (M.readLE rp (8 * rl)) M2 s'))

end FvModexp.Arm64.W2Pro
