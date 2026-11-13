import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W2Anc
import FvModexp.Proofs.Arm64.Exp.W2CtxB
import FvModexp.Proofs.Arm64.Exp.W2RR
import FvModexp.Proofs.Arm64.Exp.W2Posts
import FvModexp.Proofs.Arm64.Exp.W2Cut
import FvModexp.Proofs.Arm64.Exp.W2FunDefs
import FvModexp.Proofs.Arm64.Exp.ExpHypL
import FvModexp.Proofs.Arm64.Nat.LshDefs

/-!
# window-2 prologue (arm64): the posts of the `x` normalisation and the statement `XnSpec` of `W2XnS.xnStep`

`xnE`, `DivRetPost`, `XnPost`, `DivCosts` are hoisted (s67) out of `W2XnR`, `W2DivS`, `W2XnJ`, `W2XnS` (unchanged text,
same namespace). `XnSpec` is `xnStep`'s statement verbatim; `W2EnX.atXnE` and `W2En.enStep` take it as a hypothesis
and `W2FunE` discharges it with `xnStep`, so the entry segment does not import the `x` normalisation chain.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf FinEnv)

abbrev xnE : Nat := 1802324

/-- the post of the window-2 function from `divRet` on, with the memory at `divRet` and the remainder abstracted -/
@[reducible] def DivRetPost (R : RtInv) (L0 : List (Nat × Nat)) (K bA : Nat) (M0 : Memory)
    (g sp n mp mc Mv Xv t yp ylen Y yi zp zc st n0 zzp zzc lenM : Nat)
    (r18 r29 : BitVec 64) (s' : State) : Prop :=
  ∃ (M' : Memory) (L' : List (Nat × Nat)) (b' rp rl rc : Nat) (M1 : Memory) (rrp rrc onep : Nat) (M2 : Memory)
    (L2 : List (Nat × Nat)) (b2 : Nat),
    Anc R L0 sp K st M0 L' M' ∧ bA ≤ b' ∧ stLen M' st = lenM ∧
    (Apart zzp (8 * zzc) (stW M' st) (8 * stCap M' st) ∧ Held R L' zzp (8 * zzc)) ∧
    M'.readLE rp (8 * rl) = 2 ^ (128 * n) % Mv ∧ RRPost R b' L' g sp n rp rl rc zzp zzc M' M1 rrp rrc ∧
    OneChain R b' L' L2 b2 sp n st M1 M2 ∧
    RetPost R b2 L2 g sp n mp mc t (stW M2 st + 8 * lenM) yp ylen Y yi zp zc zzp zzc st n0 onep r18 r29 Mv Xv
      (2 ^ (128 * n) % Mv) M2 s'

/-- the post of window-2 from the `x` normalisation on (`l1` = the stack level at `xJ`) -/
@[reducible] def XnPost (R : RtInv) (L0 : List (Nat × Nat)) (K bA : Nat) (M0 : Memory)
    (g sp n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 lu : Nat) (r18 r29 : BitVec 64) (s' : State) : Prop :=
  ∃ l1 zzp zzc : Nat, l0 ≤ l1 ∧ l1 ≤ lu ∧ l1 + 2 * StackNat.rnd (2 * n) + 32 * n + 80 ≤ 2 ^ 16 ∧ (2 * n + 1 ≤ zzc ∧ InRanges zzp (8 * zzc) R.rt ∧ ApartAll zzp (8 * zzc) L0) ∧
    DivRetPost R L0 K bA M0 g sp n mp mc Mv Xv (Exp.newton 64 (Mv % Exp.B)) yp ylen Y yi zp zc st n0
    zzp zzc (l1 + 2 * StackNat.rnd (2 * n)) r18 r29 s'

/-- the division-cost bounds of the x-normalisation + RR section at entry level `l0` (`k = len x - n + 1`): `x mod m`
(path A) and the `RR` division on paths A/B, A/C, B, C -/
@[reducible] def DivCosts (costF : Nat → Nat → Nat → Nat) (costD n xl l0 : Nat) : Prop :=
  costF (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n) xl n ≤ costD ∧
  costF (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD ∧
  costF (l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD ∧
  costF (l0 + StackNat.rnd n + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD ∧
  costF (l0 + 2 * StackNat.rnd (2 * n)) (2 * n + 1) n ≤ costD

set_option linter.unusedVariables false in
/-- the statement of `xnStep` (s67 import-chain cut: taken as a hypothesis by its callers, composed at the top) -/
def XnSpec : Prop :=
  ∀ (hRR : FvModexp.Arm64.W2Pro.RRSpec) (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hSN : StackNat.HypL impl R StackNat.names 4208 24)
    (nsD : List String) (stkD costD : Nat) (costF : Nat → Nat → Nat → Nat) (hDiv : ExpHyp.DivHypL impl R nsD stkD 112 costF)
    (hnsD : ∀ x, nsD.contains x = true → LibW.names.contains x = true)
    (hnsW : nsD.contains Extracted.seg35.name = false)
    (nsL : List String) (stkL : Nat) (hLsh : Lsh.Hyp2 impl R nsL stkL 64)
    (hnsL : ∀ x, nsL.contains x = true → LibW.names.contains x = true)
    (hnsWL : nsL.contains Extracted.seg35.name = false)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp K n mp mc Mv Xv yp ylen Y yi zp zc st n0 l0 xp xl xc : Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) {lu : Nat} (hlu : l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + StackNat.rnd n ≤ lu) (hKD : stkD ≤ K) (hKL : stkL ≤ K)
    (hB : CtxB R L g sp K n mp mc Mv yp ylen Y yi zp zc st n0 l0 ret r29 [] M) (hl0e : stLen M st = l0)
    (hxO : Obj R L sp K st l0 [] M xp (8 * xl)) (hxa : M.accessible xp (8 * xl) false = true)
    (hx48 : xp + 8 * xl ≤ 2 ^ 48) (hxN : NatNorm M xp xl) (hxl0 : 0 < xl) (hxl' : xl ≤ 128) (hxc : xc < 2 ^ 64)
    (hxv : M.readLE xp (8 * xl) = Xv)
    (hmB : Mv < Exp.B ^ n) (hMo : Mv % 2 = 1) (hM1 : 1 < Mv)
    (hslen : l0 + StackNat.rnd (xl - n + 1) + StackNat.rnd n + 16 * xl + StackNat.rnd n + 2 * StackNat.rnd (2 * n) +
      32 * n + 80 ≤ 2 ^ 16)
    (hcs : DivCosts costF costD n xl l0)
    (hbC : xjBud n costD l0 ≤ b) (hbB : stackNatCost l0 n + xjBud n costD (l0 + StackNat.rnd n) ≤ b)
    (hbA : xnBudA n costD l0 (xl - n + 1) ≤ b) (hbAC : xnBudAC n costD l0 (xl - n + 1) ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (r680 : M.readLE (sp + 680) 8 = xp) (r688 : M.readLE (sp + 688) 8 = xl) (r696 : M.readLE (sp + 696) 8 = xc)
    (L0 : List (Nat × Nat)) (bA : Nat) (M0 : Memory) (hAn : Anc R L0 sp K st M0 L M)
    (hbAC' : bA + xjBudA n costD l0 ≤ b) (hbAB' : bA + (stackNatCost l0 n + xjBudA n costD (l0 + StackNat.rnd n)) ≤ b)
    (hbAAB : bA + xnBudAB n costD l0 (xl - n + 1) ≤ b) (hbAAA : bA + xnBudAA n costD l0 (xl - n + 1) ≤ b)
    (hl0A : stLen M0 st ≤ l0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 xnE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h8 : S.regs 8 = BitVec.ofNat 64 ylen) (h10 : S.regs 10 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M),
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ Xv', Xv' % Mv = Xv % Mv ∧ Xv' < Exp.B ^ n ∧
        XnPost R L0 K bA M0 g sp n mp mc Mv Xv' yp ylen Y yi zp zc st n0 l0 lu r18 r29 s'))

end FvModexp.Arm64.W2Pro
