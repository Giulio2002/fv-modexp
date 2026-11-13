import FvModexp.Proofs.Amd64.Exp.W2P0
import FvModexp.Proofs.Amd64.Exp.W2P1
import FvModexp.Proofs.Amd64.Exp.W2PowLoop

set_option autoImplicit false

/-!
# window-2 prologue (amd64): the whole power table, `p01 → j4` (nat.go:1549-1554; agent expmc s49)

`p0` (`powers[0]`) → `p1` (`powers[1]`) → `powLoop` (`powers[2..4)`): at `j4` every entry `d < 4` holds
`Exp.montPow n m k0 x RR d` (values read at the anchor `M` = the memory at `p01`), headers `(bp + 8·d·n, n, 2n)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf InpC Inp.c OneIn)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem p01pow {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc t bp bc onep rrp rrc xp : Nat} {M : Memory}
    (hs : PStatic R L g fs sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) bp bc M) (ht : t < 2 ^ 64)
    {ret : W64} {Q : State → Prop} {r5 : W64}
    (hone : OneIn R L sp n M onep) (hbo : Apart bp (8 * bc) onep (8 * n)) (hone1 : M.readLE onep (8 * n) = 1)
    (hrr : Inp R L sp n M rrp) (hbr : Apart bp (8 * bc) rrp (8 * n))
    (hx : Inp R L sp n M xp) (hbx : Apart bp (8 * bc) xp (8 * n))
    (s78 : M.readLE (sp + 0x78) 8 = 2 * n) (s3b0 : M.readLE (sp + 0x298) 8 = n) (s3a8 : M.readLE (sp + 0x290) 8 = mp)
    (s3b8 : M.readLE (sp + 0x2a0) 8 = mc) (sd8 : M.readLE (sp + 0xd8) 8 = t) (s328 : M.readLE (sp + 0x210) 8 = onep)
    (s338 : M.readLE (sp + 0x220) 8 = rrp) (sf8 : M.readLE (sp + 0xf8) 8 = n) (s100 : M.readLE (sp + 0x100) 8 = rrc)
    (s370 : M.readLE (sp + 0x258) 8 = xp) (s138 : M.readLE (sp + 0x140) 8 = n)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 p01) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h1 : S.regs 1 = BitVec.ofNat 64 bc)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (KX : ∀ S' : State, S'.rip = BitVec.ofNat 64 j4 → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      FP R L sp bp bc M S'.mem → R.inv b L g (view R.rt L S'.mem) → S'.mem.regions = M.regions →
      PSl sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) bp bc S'.mem →
      (∀ d, d < 4 → Ent sp n (tp bp n) (tc n) (Exp.montPow n (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64)
        (M.readLE xp (8 * n)) (M.readLE rrp (8 * n))) S'.mem d) →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  refine p0 hap hclr hmv hs ht hone hbo hrr hbr s78 s3b0 s3a8 s3b8 sd8 s328 s338 sf8 s100 hinv S hpc hsp hmem h0 h1
    h5 h14 hfs hx15 hdf ?_
  intro S1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hF1 hinv1 hrg1 hsl1 s130 hsl hv0
  refine p1 hap hclr hmv hs hx hbx hrr hbr S1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hF1 hinv1 hrg1 hsl1 s130
    (by rw [hsl 0x258 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; try exact s370)
    (by rw [hsl 0x140 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; try exact s138)
    rfl
    (by rw [hsl 0x220 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; try exact s338)
    (by rw [hsl 0xf8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact sf8)
    (by rw [hsl 0x100 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; try exact s100) hv0 ?_
  intro S2 c1 c2 c3 c4 c5 c6 c7 c8 hF2 hinv2 hrg2 hsl2 hE0 hE1
  refine powLoop hap hclr hmv hs (tbl := Exp.montPow n (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64)
    (M.readLE xp (8 * n)) (M.readLE rrp (8 * n))) ?_ KX (4 - 2) 2 S2 rfl (Nat.le_refl _) (by omega) c1 c2 c3 c4 c5
    c6 c7 c8 hF2 hinv2 hrg2 hsl2 ?_
  · intro i hi2 hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    rfl
  · intro d hd
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · refine ⟨?_, hE0.2⟩
      rw [hE0.1, hone1]; rfl
    · exact hE1

end FvModexp.Amd64.W2Pro
