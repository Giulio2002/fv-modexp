import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.W4FinDefs
import FvModexp.Proofs.Arm64.Exp.W4PowDefs
import FvModexp.Proofs.Arm64.Exp.W4One

/-!
# window-4 (arm64): posts of the `RR`/`one`/`powers` sections and the statement `J4Spec` of `W4Mid2.j4Ret`

Hoisted (s67) out of `W4Mid2`, `W4OneRet` and `W4PowAll` (unchanged text, same namespace). `J4Spec` is `j4Ret`'s
statement verbatim; `W4P01Ret.p01Ret` and its callers take it as a hypothesis and `W4Comp` discharges it with `j4Ret`,
so the `RR → RET` segment and the `j4 → RET` segment compile in parallel (row import-chain cut).
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf Bufs Mem FinEnv TailPost step)

/-- the ranges `p01 → j4` may write besides `R.rt` -/
@[reducible] def tw (sp bp n : Nat) : List (Nat × Nat) := qw sp ++ pw sp ++ [(bp, bp + 8 * (17 * n))]

theorem apart_held {R : RtInv} {L : List (Nat × Nat)} {p k a n : Nat} (hin : InRanges p k R.rt)
    (hap : ApartAll p k L) (hh : InRanges a n L ∨ Outside a n R.rt) : Apart p k a n := by
  rcases hh with h | h
  · exact hap.apart_of_inRanges h
  · have := out_inR h hin; unfold Apart; omega

theorem buf_ext {R : RtInv} {L L' : List (Nat × Nat)} {g sp n p c : Nat} {M M' : Memory} {ws : List (Nat × Nat)}
    (hx : LiveExt R L L') (h : Buf R L g sp n M p c) (hf : MemFrame M M' ws) : Buf R L' g sp n M' p c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  exact ⟨a1, a2, by rw [hf.accessible]; exact a3, a4, hx.held a5, a6, a7⟩

theorem apart_held' {R : RtInv} {L : List (Nat × Nat)} {p k a n : Nat} (hin : InRanges p k R.rt)
    (hap : ApartAll p k L) (hh : InRanges a n L ∨ Outside a n R.rt) : Apart a n p k := by
  have := apart_held hin hap hh; unfold Apart at this ⊢; omega

/-- `p01Ret`'s conclusion with the operand values given explicitly -/
@[reducible] def RetPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc t bp yp ylen Y yi zp zc zzp zzc st n0 onep : Nat)
    (r18 r29 : BitVec 64) (Mv xv rv : Nat) (M : Memory) (s' : State) : Prop :=
  ∃ (Mj M' : Memory) (zp' zc' : Nat) (L' : List (Nat × Nat)) (b' : Nat),
    MemFrame M Mj (R.rt ++ tw sp bp n) ∧ LiveFrame M Mj L [(bp, bp + 8 * (17 * n))] ∧
    R.inv b L g (view R.rt L Mj) ∧ Mj.regions = M.regions ∧
    ZPost R L L' b b' g sp n Mj M' zp zc zp' zc' ∧
    ZjPost R b' L' g sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) yp ylen bp zp' zc' zzp zzc
      (Exp.montPow n Mv ((2 ^ 64 - t) % 2 ^ 64) xv rv)
      (zjVal n Mv ((2 ^ 64 - t) % 2 ^ 64) (Exp.montPow n Mv ((2 ^ 64 - t) % 2 ^ 64) xv rv) Y ylen yi)
      st n0 onep r18 r29 M' s'

/-- the stack/runtime chain `oneJ → p01` -/
@[reducible] def OneChain (R : RtInv) (b : Nat) (L L2 : List (Nat × Nat)) (b2 sp n st : Nat) (M0 M2 : Memory) : Prop :=
  MemFrame M0 M2 (R.rt ++ ow sp ++ [(sp - 4208, sp - 8), (sp + 8, sp + 24)] ++ stkWs M0 st) ∧
  LiveFrame M0 M2 L (stkWs M0 st) ∧ LiveExt R L L2 ∧
  b - ((if 4 < n then blockSize (8 * n) true else 0) + stackNatCost (stLen M0 st) (17 * n)) ≤ b2 ∧
  StkOK M2 R L2 st ∧ stLen M2 st = stLen M0 st + StackNat.rnd (17 * n) ∧
  (stLen M0 st + StackNat.rnd (17 * n) ≤ stCap M0 st → stW M2 st = stW M0 st ∧ stCap M2 st = stCap M0 st) ∧
  (stCap M0 st < stLen M0 st + StackNat.rnd (17 * n) → InRanges (stW M2 st) (8 * stCap M2 st) R.rt ∧
    ApartAll (stW M2 st) (8 * stCap M2 st) L) ∧ M2.regions = M0.regions ∧
  (stCap M0 st < stLen M0 st + StackNat.rnd (17 * n) → (stW M2 st, stW M2 st + 8 * stCap M2 st) ∈ L2)

set_option linter.unusedVariables false in
/-- the statement of `j4Ret` (s67 import-chain cut: taken as a hypothesis by its callers, composed at the top) -/
def J4Spec : Prop :=
  ∀ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hserv : RunIface.Serves R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y yi bp zp zc zzp zzc : Nat) (tbl : Nat → Nat)
    (M : Memory) (r18 r29 f29 : BitVec 64) (onep st n0 : Nat)
    (he : Env R L g sp M) (hce : CallW.CEnv R L g sp 4304 1040 M)
    (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hk0 : k0 < 2 ^ 64)
    (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40)
    (hm : Inp R L sp n M mp) (hy : Inp R L sp ylen M yp) (hY : M.readLE yp (8 * ylen) = Y)
    (hyi : M.readLE (yp + 8 * (ylen - 1)) 8 = yi) (hyi0 : 0 < yi)
    (hzc : zc < 2 ^ 40) (hz : 2 * n ≤ zc → Buf R L g sp n M zp zc ∧ zp % 8 = 0)
    (hold : 2 * n ≤ zc → Apart zp (8 * zc) zzp (8 * zzc) ∧ Apart zp (8 * zc) mp (8 * n) ∧
      Apart zp (8 * zc) yp (8 * ylen) ∧ (∀ d, d < 16 → Apart zp (8 * zc) (bp + 8 * (d * n)) (8 * n)) ∧
      Apart zp (8 * zc) (sp - 4304) 16 ∧ Apart zp (8 * zc) onep (8 * n) ∧ Apart zp (8 * zc) st 24)
    (hzz : Buf R L g sp n M zzp zzc) (hzz8 : zzp % 8 = 0)
    (hzzm : Apart zzp (8 * zzc) mp (8 * n)) (hzzy : Apart zzp (8 * zzc) yp (8 * ylen))
    (hzzp : ∀ d, d < 16 → Apart zzp (8 * zzc) (bp + 8 * (d * n)) (8 * n)) (hzz4 : Apart zzp (8 * zzc) (sp - 4304) 16)
    (hzzo : Apart zzp (8 * zzc) onep (8 * n)) (hzzs : Apart zzp (8 * zzc) st 24)
    (hent : ∀ d, d < 16 → Ent sp n bp tbl M d) (hbuf : ∀ d, d < 16 → Inp R L sp n M (bp + 8 * (d * n)))
    (hd : Extracted.program.DataLoaded M) (hro : RoOut R) (hty : Outside wT 16 R.rt)
    (r952 : M.readLE (sp + 952) 8 = zc) (r936 : M.readLE (sp + 936) 8 = zp) (r128 : M.readLE (sp + 128) 8 = 2 * n)
    (r168 : M.readLE (sp + 168) 8 = zzc) (r400 : M.readLE (sp + 400) 8 = zzp)
    (r1000 : M.readLE (sp + 1000) 8 = ylen) (r992 : M.readLE (sp + 992) 8 = yp)
    (r1024 : M.readLE (sp + 1024) 8 = n) (r224 : M.readLE (sp + 224) 8 = k0) (r1016 : M.readLE (sp + 1016) 8 = mp)
    (r1032 : M.readLE (sp + 1032) 8 = mc)
    (hokm : zc < 2 * n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4] ∧
      blockSize (8 * (2 * n + 4)) true ≤ b)
    (hokS : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])
    (hokM : ∀ p d, R.ok (Extracted.program.contractAddr "runtime.memmove") [p, d, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (hmw4 : Apart mp (8 * n) (sp - 4304) 16) (hnm : NatNorm M mp n)
    (hone : OneIn R L sp n M onep) (hone1 : M.readLE onep (8 * n) = 1) (r816 : M.readLE (sp + 816) 8 = onep)
    (hkk : (k0 * M.readLE mp (8 * n) + 1) % Exp.B = 0) (hmB : M.readLE mp (8 * n) < Exp.B ^ n)
    (hfe : FinEnv sp g st n0 r29 ret M) (hsth : InRanges st 24 L ∨ Outside st 24 R.rt)
    (hstw4 : Apart st 24 (sp - 4304) (4304 + 1040))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 j4) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = f29) (hmem : S.mem = M),
    Reaches ((LibW.program.link impl).withExit ret) S
      (IsReturn (fun s' => ∃ (M' : Memory) (zp' zc' : Nat) (L' : List (Nat × Nat)) (b' : Nat),
        ZPost R L L' b b' g sp n M M' zp zc zp' zc' ∧
        ZjPost R b' L' g sp n mp mc k0 yp ylen bp zp' zc' zzp zzc tbl
          (zjVal n (M.readLE mp (8 * n)) k0 tbl Y ylen yi) st n0 onep r18 r29 M' s'))

set_option linter.unusedVariables false in
/-- the statement of `p01pow` (s67 import-chain cut: `W4PowAll.p01pow`, taken as a hypothesis by its callers, composed at the top) -/
def P01Spec : Prop :=
  ∀ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc t bp onep rrp rrc xp xc : Nat) (M : Memory) (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (ht : t < 2 ^ 64)
    (hm : Inp R L sp n M mp)
    (hba : M.accessible bp (8 * (17 * n)) true = true) (hbb : bp + 8 * (17 * n) ≤ 2 ^ 48)
    (hbh : InRanges bp (8 * (17 * n)) L ∨ Outside bp (8 * (17 * n)) R.rt)
    (hbw : Apart bp (8 * (17 * n)) (sp - 4288) (4288 + 1040)) (hbg : Apart (g + 16) 8 bp (8 * (17 * n)))
    (hbm : Apart bp (8 * (17 * n)) mp (8 * n))
    (hone : OneIn R L sp n M onep) (hbo : Apart bp (8 * (17 * n)) onep (8 * n)) (hone1 : M.readLE onep (8 * n) = 1)
    (hrr : Inp R L sp n M rrp) (hbR : Apart bp (8 * (17 * n)) rrp (8 * n))
    (hx : Inp R L sp n M xp) (hbx : Apart bp (8 * (17 * n)) xp (8 * n))
    (r1016 : M.readLE (sp + 1016) 8 = mp) (r1024 : M.readLE (sp + 1024) 8 = n) (r1032 : M.readLE (sp + 1032) 8 = mc)
    (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n) (r816 : M.readLE (sp + 816) 8 = onep)
    (r832 : M.readLE (sp + 832) 8 = rrp) (r256 : M.readLE (sp + 256) 8 = n) (r264 : M.readLE (sp + 264) 8 = rrc)
    (r904 : M.readLE (sp + 904) 8 = xp) (r328 : M.readLE (sp + 328) 8 = n) (r320 : M.readLE (sp + 320) 8 = xc)
    (hok : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 p01) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h1 : S.regs 1 = BitVec.ofNat 64 (17 * n))
    (h2 : S.regs 2 = BitVec.ofNat 64 (17 * n))
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KX : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 j4 → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      MemFrame M M' (R.rt ++ tw sp bp n) → LiveFrame M M' L [(bp, bp + 8 * (17 * n))] →
      R.inv b L g (view R.rt L M') → M'.regions = M.regions →
      M'.readLE (sp + 224) 8 = (2 ^ 64 - t) % 2 ^ 64 →
      (∀ d, d < 16 → Ent sp n bp (Exp.montPow n (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64) (M.readLE xp (8 * n))
        (M.readLE rrp (8 * n))) M' d) →
      Reaches ((LibW.program.link impl).withExit ret) S' Q),
    Reaches ((LibW.program.link impl).withExit ret) S Q

end FvModexp.Arm64.W4Pro
