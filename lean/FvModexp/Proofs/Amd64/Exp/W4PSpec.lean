import FvModexp.Proofs.Amd64.Exp.W4Posts2

set_option autoImplicit false

/-!
# window-2 (amd64): the statements `P01Spec` (`W4PowAll.p01pow`) and `J4Spec` (`W4Mid2.j4Ret`) (divmc s79 cut)

Verbatim statements, taken as hypotheses by `W4P01Ret.p01Ret` and its callers up to `W4RRC.rrRetC`; `W4Comp` discharges
them, so the `divRet → RET` section imports neither the table segment nor the `j4 → RET` segment.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf OneIn FinEnv)

set_option linter.unusedVariables false in
/-- the statement of `p01pow` (divmc s79 import-chain cut: taken as a hypothesis by its callers, composed at the top) -/
def P01Spec : Prop :=
  ∀ {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc t bp bc onep rrp rrc xp : Nat} {M : Memory}
    (hs : PStatic R L g fs sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) bp bc M) (ht : t < 2 ^ 64)
    {ret : W64} {Q : State → Prop} {r5 : W64}
    (hone : OneIn R L sp n M onep) (hbo : Apart bp (8 * bc) onep (8 * n)) (hone1 : M.readLE onep (8 * n) = 1)
    (hrr : Inp R L sp n M rrp) (hbr : Apart bp (8 * bc) rrp (8 * n))
    (hx : Inp R L sp n M xp) (hbx : Apart bp (8 * bc) xp (8 * n))
    (s78 : M.readLE (sp + 0x78) 8 = 2 * n) (s3b0 : M.readLE (sp + 0x3b0) 8 = n) (s3a8 : M.readLE (sp + 0x3a8) 8 = mp)
    (s3b8 : M.readLE (sp + 0x3b8) 8 = mc) (sd8 : M.readLE (sp + 0xd8) 8 = t) (s328 : M.readLE (sp + 0x328) 8 = onep)
    (s338 : M.readLE (sp + 0x338) 8 = rrp) (sf8 : M.readLE (sp + 0xf8) 8 = n) (s100 : M.readLE (sp + 0x100) 8 = rrc)
    (s370 : M.readLE (sp + 0x370) 8 = xp) (s138 : M.readLE (sp + 0x138) 8 = n)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 p01) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h1 : S.regs 1 = BitVec.ofNat 64 bc)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (KX : ∀ S' : State, S'.rip = BitVec.ofNat 64 j4 → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      FP R L sp bp bc M S'.mem → R.inv b L g (view R.rt L S'.mem) → S'.mem.regions = M.regions →
      PSl sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) bp bc S'.mem →
      (∀ d, d < 16 → Ent sp n (tp bp n) (tc n) (Exp.montPow n (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64)
        (M.readLE xp (8 * n)) (M.readLE rrp (8 * n))) S'.mem d) →
      ReachesRet (LibW.program.link impl) ret S' Q),
    ReachesRet (LibW.program.link impl) ret S Q

set_option linter.unusedVariables false in
/-- the statement of `j4Ret` (divmc s79 import-chain cut: taken as a hypothesis by its callers, composed at the top) -/
def J4Spec : Prop :=
  ∀ {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice")
      4096 R)
    (hmvok : ∀ d src k, k ≤ 2 ^ 20 → R.ok (Extracted.program.contractAddr "runtime.memmove") [d, src, k])
    (hwt : Outside NatSub.wordT 16 R.rt) (hro : RoOut R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y yi Mv zp zc zzp zzc : Nat} {pp tbl : Nat → Nat}
    {M : Memory} {r5 : W64} {onep st n0 bp r : Nat}
    (he : Env R L g fs sp M) (hP : Pre4 R L sp n mp mc k0 yp ylen Y yi Mv pp tbl onep st n0 bp r M)
    (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hk0 : k0 < 2 ^ 64)
    (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 40) (hyi0 : 0 < yi)
    (hzc : zc < 2 ^ 40) (hz : 2 * n ≤ zc → Buf R L g fs sp n M zp zc ∧ zp % 8 = 0)
    (hzzc : zzc < 2 ^ 40) (hzz : 2 * n ≤ zzc → Buf R L g fs sp n M zzp zzc ∧ zzp % 8 = 0)
    (hoz : 2 * n ≤ zc → OldA n mp yp ylen onep st pp zp zc)
    (hozz : 2 * n ≤ zzc → OldA n mp yp ylen onep st pp zzp zzc)
    (hzzz : 2 * n ≤ zc → 2 * n ≤ zzc → Apart zp (8 * zc) zzp (8 * zzc))
    (r3d0 : M.readLE (sp + 0x3d0) 8 = zc) (r3c0 : M.readLE (sp + 0x3c0) 8 = zp) (r78 : M.readLE (sp + 0x78) 8 = 2 * n)
    (ra0 : M.readLE (sp + 0xa0) 8 = zzc) (r188 : M.readLE (sp + 0x188) 8 = zzp)
    (hacc2 : M.accessible (sp + 0x3c0) 0x20 false = true)
    (hokm : R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4])
    (hb1 : zc < 2 * n → blockSize (8 * (2 * n + 4)) true ≤ b)
    (hb2 : zzc < 2 * n → 2 * blockSize (8 * (2 * n + 4)) true ≤ b)
    (hokS : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, n * 8])
    (hinv : R.inv b L g (view R.rt L M))
    (hkk : (k0 * Mv + 1) % Exp.B = 0) (hmB : Mv < Exp.B ^ n) (hbp : bp < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6208293) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false),
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
      (fun s' => ∃ (M1 M2 : Memory) (zp1 zc1 zzp2 zzc2 : Nat) (L1 L2 : List (Nat × Nat)) (b1 b2 : Nat),
        ZPost R L L1 b b1 g fs sp n M M1 (zw1 sp) zp zc zp1 zc1 ∧
        ZPost R L1 L2 b1 b2 g fs sp n M1 M2 (zw2 sp) zzp zzc zzp2 zzc2 ∧
        ZjPost R b2 L2 g fs sp n mp yp ylen zp1 zc1 zzp2 zzc2 k0 pp (zjVal n Mv k0 tbl Y ylen yi) st n0 onep bp M2 s')

end FvModexp.Amd64.W4Pro
