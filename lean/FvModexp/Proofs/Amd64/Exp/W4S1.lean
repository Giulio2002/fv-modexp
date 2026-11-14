import FvModexp.Proofs.Amd64.Exp.W4BD
import FvModexp.Proofs.Amd64.Exp.W4Seg

set_option autoImplicit false

/-!
# window-4 main loop (amd64), segment 1: loop test → return of `zz = zz.montgomery(z, z, …)` (nat.go:1446, 1453)

From the test `TESTQ R15, R15; JGE` (+0x1031) with `k = c ≥ 0`: the stores `z.cap → 0x110`, `z.ptr → 0x358`,
`k → 0xe0`, `yi → 0xb0`, the stack arguments, the call (`callF` on the swapped buffers), up to the return +0xdac.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Loop

theorem bv_sub8 {sp : Nat} (h1 : 8 ≤ sp) (h2 : sp < 2 ^ 64) :
    BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- read-after-write closer for concrete frame offsets -/
macro "rdw" : tactic => `(tactic| (
  simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
    show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]))

theorem montE : segAddr LibW.program MontHyp.fn = 6184288 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem seg1 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y : Nat} {tbl pp pcap : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory}
    (hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp pcap M0) {ret : W64} {Q : State → Prop}
    (S : State) (c yi zp zc zzp zzc : Nat) (hc : c < 16) (hyi : yi < 2 ^ 64)
    (hpc : S.rip = BitVec.ofNat 64 test) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc) (h8 : S.regs 8 = BitVec.ofNat 64 zzp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 zzc)
    (h3 : S.regs 3 = BitVec.ofNat 64 mp) (h6 : S.regs 6 = BitVec.ofNat 64 k0) (h10 : S.regs 10 = BitVec.ofNat 64 mc)
    (h9 : S.regs 9 = BitVec.ofNat 64 yi) (h15 : S.regs 15 = BitVec.ofNat 64 c)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hB : Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 S.mem zp zc zzp zzc)
    (r140 : S.mem.readLE (sp + 0x140) 8 = n)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 (fnE + 0xdac) → s'.regs 4 = BitVec.ofNat 64 sp →
      s'.regs 5 = S.regs 5 → s'.regs 14 = BitVec.ofNat 64 g → s'.fsBase = S.fsBase → s'.xmm 15 = 0 → s'.df = false →
      s'.regs 0 = BitVec.ofNat 64 zzp → s'.regs 3 = BitVec.ofNat 64 n → s'.regs 1 = BitVec.ofNat 64 zzc →
      Mem R b L g sp M0 s'.mem zp zc zzp zzc →
      s'.mem.readLE (sp + 0x110) 8 = zc → s'.mem.readLE (sp + 0x358) 8 = zp → s'.mem.readLE (sp + 0xe0) 8 = c →
      s'.mem.readLE (sp + 0xb0) 8 = yi → s'.mem.readLE (sp + 0x140) 8 = n →
      s'.mem.readLE (sp + 0xe8) 8 = S.mem.readLE (sp + 0xe8) 8 →
      s'.mem.readLE zp (8 * n) = S.mem.readLE zp (8 * n) →
      s'.mem.readLE zzp (8 * n) = sq n (M0.readLE mp (8 * n)) k0 (S.mem.readLE zp (8 * n)) →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he := hst.1
  have hn := hst.2.1; have hmc := hst.2.2.2.1; have hmc' := hst.2.2.2.2.1; have hk0 := hst.2.2.2.2.2.1
  have hsp1 : 4296 ≤ sp := he.2.1; have hsp2 : sp + 0x3c0 ≤ 2 ^ 48 := he.2.2.1
  have hzc := hB.1.2.1; have hzp := hB.1.2.2.2.1; have hzzc := hB.2.1.2.1; have hzzp := hB.2.1.2.2.2.1
  have hmp : mp < 2 ^ 48 := by have := hst.2.2.2.2.2.2.2.2.1.2.1; omega
  have hn16 := hst.2.2.1
  have hacc : S.mem.accessible (sp - 4296) (4296 + 0x3c0) true = true := by
    rw [hM.1.1.accessible]; exact he.2.2.2.1
  have r3b0 : S.mem.readLE (sp + 0x3b0) 8 = n := (Static.rd hst hM.1 hB.1 hB.2.1).2.1
  have h63 : (BitVec.ofNat 64 c).msb = false := by simp [BitVec.msb_eq_decide]; omega
  refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 6184288) ?_
  janus64_run [h63, r140, r3b0, BitVec.msb_eq_decide] until [6184288]
  have hra : RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) 6209036 :=
    ra_of hap mont_not 0xdac (by decide)
  have hzI := hB.1.inp
  have hzzz := hB.2.2.1
  refine callF hap hclr hmv (b := b) hst hB.swap hzI hzI.c (by have := hzzz; unfold Apart at this ⊢; omega)
    (by have := hzzz; unfold Apart at this ⊢; omega) hra (by rw [montE])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact bv_sub8 (by omega) (by omega))
    (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_self])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14) hfs hx15 (by first | rfl | exact hdf) ?mem ?a0 ?a1 ?a2 ?a3 ?a4 ?K
  case mem =>
    repeat (first | exact hM.swap | refine Mem.wr ?_ he _ (by omega))
  case K =>
    intro s' hrip e4 e5 e14 efs e15 edf r0 r3 r1 hM' hsl hzz hz
    refine K s' hrip e4 e5 e14 efs e15 edf r0 r3 r1 hM'.swap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    any_goals (rw [hsl _ (by omega) (by omega)]; rdw; try exact r140)
    · rw [hzz]; have := hB.1.2.2.2.2.2.1; unfold Apart at this; rdw
    · rw [hz]; have := hB.1.2.2.2.2.2.1; unfold Apart at this; rdw
  all_goals rdw

end FvModexp.Amd64.W4Loop
