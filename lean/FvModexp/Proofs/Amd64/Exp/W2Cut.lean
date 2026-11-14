import FvModexp.Proofs.Amd64.Exp.W2Ctx

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `ZZ` and the statement `RRSpec` of `W2RRC.rrRetC` (`divRet → RET`)

`ZZ`/`aw_w4` are hoisted verbatim (divmc s79) out of `W2RRC`. `RRSpec` is `rrRetC`'s statement verbatim; `W2DivS.divStep`
and its callers up to `W2En.enStep` take it as a hypothesis and `W2FunE` discharges it with `W2RRC.rrRetC`, so the
prologue segment (`entry → divRet`) does not import the `divRet → RET` segment (row import-chain cut, twin of the
arm64 `W2Cut` of expmc s67).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf FinEnv)

/-- the `zz` buffer -/
@[reducible] def ZZ (R : RtInv) (L : List (Nat × Nat)) (g fs sp n mp xp yp ylen zp zc st zzp zzc : Nat) (M : Memory) :
    Prop :=
  Buf R L g fs sp n M zzp zzc ∧ zzp % 8 = 0 ∧ Apart zzp (8 * zzc) mp (8 * n) ∧ Apart zzp (8 * zzc) yp (8 * ylen) ∧
  Apart zzp (8 * zzc) xp (8 * n) ∧ Apart zzp (8 * zzc) (sp + 0x2a8) 0x20 ∧ Apart zzp (8 * zzc) st 24 ∧
  Apart zzp (8 * zzc) (stW M st) (8 * stCap M st) ∧ (2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc))

/-- the context's window `[sp - 8 - K, sp + 0x2a8)` contains the loop's frame `[sp - 4296, sp + 0x2a8)` -/
theorem aw_w4 {sp K a k : Nat} (hK : 41512 ≤ K) (h : AW sp K a k) : Apart a k (sp - 4296) (4296 + 0x2a8) := by
  simp only [AW, Apart] at h ⊢; omega

set_option linter.unusedVariables false in
/-- the statement of `rrRetC` (divmc s79 import-chain cut: taken as a hypothesis by its callers, composed at the top) -/
def RRSpec : Prop :=
  ∀ {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    (hSN : StackNat.HypL impl R StackNat.names 4192 24) (hserv : RunIface.Serves R)
    {b : Nat} {L : List (Nat × Nat)}
    {g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r t rp rl rc zzp zzc : Nat} {ex : List (Nat × Nat)}
    {M : Memory} {r5 : W64}
    (hC : Ctx R L g fs sp K n mp mc Mv xp Xv yp ylen Y yi zp zc st n0 l0 fbp r ex M)
    (hZ : ZZ R L g fs sp n mp xp yp ylen zp zc st zzp zzc M)
    (ht : t < 2 ^ 64) (hfbp : fbp < 2 ^ 64) (sd8 : M.readLE (sp + 0xd8) 8 = t) (s78 : M.readLE (sp + 0x78) 8 = 2 * n)
    (s1a0 : M.readLE (sp + 0xa0) 8 = zzc) (s188 : M.readLE (sp + 0x190) 8 = zzp)
    (hkk : ((2 ^ 64 - t) % 2 ^ 64 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n)
    (hslen : stLen M st + 5 * n + 3 ≤ 2 ^ 16)
    (hbud : blockSize (8 * n) true + stackNatCost (stLen M st) (5 * n) + 2 * blockSize (8 * (2 * n + 4)) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (hrl0 : 0 < rl) (hrln : rl ≤ n) (hrc : rc < 2 ^ 40)
    (hra : M.accessible rp (8 * rl) false = true) (hr48 : rp + 8 * rl ≤ 2 ^ 48)
    (hrh : InRanges rp (8 * rl) L ∨ Outside rp (8 * rl) R.rt) (hrw : Apart rp (8 * rl) (sp - 4296) (4296 + 0x2a8))
    (hrS : Apart rp (8 * rl) st 24) (hrF : Apart rp (8 * rl) (stFree M st).1 (stFree M st).2)
    (hzr : Apart zzp (8 * zzc) rp (8 * rl)) (hzz0 : M.readLE (zzp + 8 * rl) (8 * (n - rl)) = 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 divRet) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h7 : S.regs 7 = BitVec.ofNat 64 rp) (h6 : S.regs 6 = BitVec.ofNat 64 rl) (h8 : S.regs 8 = BitVec.ofNat 64 rc)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false),
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (fun s' => ∃ (M1 : Memory) (rrp rrc onep : Nat) (M2 : Memory) (L2 : List (Nat × Nat)) (b2 : Nat),
        RRPost R b L g sp n rp rl rc zzp zzc M M1 rrp rrc ∧ OneChain R b L L2 b2 sp n st M1 M2 ∧
        RetQ R b2 L2 g fs sp n mp yp ylen Y yi zp zc zzp zzc t (stW M2 st + 8 * stLen M st) (5 * n) st n0 onep fbp
          Mv Xv (M.readLE rp (8 * rl)) M2 s')

end FvModexp.Amd64.W2Pro
