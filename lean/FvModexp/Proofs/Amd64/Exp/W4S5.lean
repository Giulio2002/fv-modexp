import FvModexp.Proofs.Amd64.Exp.W4S1
import FvModexp.Proofs.Amd64.Exp.W4Seg

set_option autoImplicit false

/-!
# window-4 main loop (amd64), segment 5: return +0xf29 → loop test (nat.go:1458-1461, 1446)

From the return of the 4th squaring (`z` header in `AX, BX, CX`): store it to `0x370/0x140/0x138`, `d = yi >> 60`,
the table entry `powers[d]` from `sp + 0x1a8 + 24 d`, `zz = zz.montgomery(z, powers[d], …)` (`callF`, swapped), then
`yi <<= 4`, `k--`, the swap `z, zz = zz, z` in registers and the reloads, up to the test `TESTQ R15, R15`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Loop

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem seg5 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y : Nat} {tbl pp pcap : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory}
    (hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp pcap M0) {ret : W64} {Q : State → Prop}
    (S : State) (i c yi zp zc zzp zzc : Nat) (hc : c < 16) (hyi : yi < 2 ^ 64)
    (hpc : S.rip = BitVec.ofNat 64 (fnE + 0xf29)) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hB : Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 S.mem zp zc zzp zzc)
    (rP : S.mem.readLE (sp + 0x188) 8 = zzp) (r98 : S.mem.readLE (sp + 0x98) 8 = n)
    (rC : S.mem.readLE (sp + 0xa0) 8 = zzc) (rb0 : S.mem.readLE (sp + 0xb0) 8 = yi)
    (re0 : S.mem.readLE (sp + 0xe0) 8 = c) (re8 : S.mem.readLE (sp + 0xe8) 8 = i)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 test → s'.regs 4 = BitVec.ofNat 64 sp →
      s'.regs 5 = S.regs 5 → s'.regs 14 = BitVec.ofNat 64 g → s'.fsBase = S.fsBase → s'.xmm 15 = 0 → s'.df = false →
      s'.regs 0 = BitVec.ofNat 64 zzp → s'.regs 2 = BitVec.ofNat 64 zzc → s'.regs 8 = BitVec.ofNat 64 zp →
      s'.regs 11 = BitVec.ofNat 64 n → s'.regs 12 = BitVec.ofNat 64 zc → s'.regs 3 = BitVec.ofNat 64 mp →
      s'.regs 6 = BitVec.ofNat 64 k0 → s'.regs 10 = BitVec.ofNat 64 mc →
      s'.regs 9 = BitVec.ofNat 64 ((yi * 2 ^ 4) % 2 ^ 64) → s'.regs 15 = BitVec.ofNat 64 c - 1#64 →
      s'.regs 7 = BitVec.ofNat 64 yp → s'.regs 13 = BitVec.ofNat 64 ylen → s'.regs 1 = BitVec.ofNat 64 i →
      Mem R b L g sp M0 s'.mem zzp zzc zp zc →
      s'.mem.readLE (sp + 0x140) 8 = n → s'.mem.readLE (sp + 0xe8) 8 = i →
      s'.mem.readLE zp (8 * n) = S.mem.readLE zp (8 * n) →
      s'.mem.readLE zzp (8 * n) =
        Exp.montgomery n (S.mem.readLE zp (8 * n)) (tbl (yi / 2 ^ (64 - 4))) (M0.readLE mp (8 * n)) k0 →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he := hst.1
  have hn := hst.2.1; have hmc := hst.2.2.2.1; have hmc' := hst.2.2.2.2.1; have hk0 := hst.2.2.2.2.2.1
  have hsp1 : 4296 ≤ sp := he.2.1; have hsp2 : sp + 0x3c0 ≤ 2 ^ 48 := he.2.2.1
  have hzc := hB.1.2.1; have hzp := hB.1.2.2.2.1; have hzzc := hB.2.1.2.1; have hzzp := hB.2.1.2.2.2.1
  have hmp : mp < 2 ^ 48 := by have := hst.2.2.2.2.2.2.2.2.1.2.1; omega
  have hyp : yp < 2 ^ 48 := by have := hst.2.2.2.2.2.2.2.2.2.1.2.1; have := hst.2.2.2.2.2.2.1; omega
  have hyl := hst.2.2.2.2.2.2.2.1
  have hn16 := hst.2.2.1
  have hacc : S.mem.accessible (sp - 4296) (4296 + 0x3c0) true = true := by
    rw [hM.1.1.accessible]; exact he.2.2.2.1
  obtain ⟨q3a8, q3b0, q3b8, qd8, q390, q398⟩ := Static.rd hst hM.1 hB.1 hB.2.1
  have hd : yi / 2 ^ 60 < 16 := by omega
  obtain ⟨hpI, -, hpc64, t0, t1, t2⟩ := hst.2.2.2.2.2.2.2.2.2.2.2.1 (yi / 2 ^ 60) hd
  have rT0 : S.mem.readLE (sp + 0x1a8 + 24 * (yi / 2 ^ 60)) 8 = pp (yi / 2 ^ 60) := by
    rw [FL.slot hM.1 he hB.1 hB.2.1 (by omega) (by omega)
      (by simp only [fw, outside_cons, outside_nil, and_true]; omega)]; exact t0
  have rT1 : S.mem.readLE (sp + 0x1b0 + 24 * (yi / 2 ^ 60)) 8 = n := by
    rw [FL.slot hM.1 he hB.1 hB.2.1 (by omega) (by omega)
      (by simp only [fw, outside_cons, outside_nil, and_true]; omega)]; exact t1
  have rT2 : S.mem.readLE (sp + 0x1b8 + 24 * (yi / 2 ^ 60)) 8 = pcap (yi / 2 ^ 60) := by
    rw [FL.slot hM.1 he hB.1 hB.2.1 (by omega) (by omega)
      (by simp only [fw, outside_cons, outside_nil, and_true]; omega)]; exact t2
  have hsh : BitVec.ofNat 64 yi >>> 60 = BitVec.ofNat 64 (yi / 2 ^ 60) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 6184288) ?_
  janus64_run [hsh, q3a8, q3b0, q3b8, qd8, rP, r98, rC, rb0] until [6184288]
  have hra : RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) (6205536 + 0xfc7) :=
    ra_of hap mont_not 0xfc7 (by decide)
  have hzI := hB.1.inp
  have hzzz := hB.2.2.1
  have hzt := (hB.2.2.2.2.2.2.2.1 (yi / 2 ^ 60) hd).2
  have e9 : S.mem.readLE (sp + (yi / 1152921504606846976 + yi / 1152921504606846976 * 2) * 8 + 424) 8 =
      pp (yi / 2 ^ 60) := by
    rw [show sp + (yi / 1152921504606846976 + yi / 1152921504606846976 * 2) * 8 + 424 =
      sp + 0x1a8 + 24 * (yi / 2 ^ 60) by omega]; exact rT0
  have e10 : S.mem.readLE (sp + (yi / 1152921504606846976 + yi / 1152921504606846976 * 2) * 8 + 432) 8 = n := by
    rw [show sp + (yi / 1152921504606846976 + yi / 1152921504606846976 * 2) * 8 + 432 =
      sp + 0x1b0 + 24 * (yi / 2 ^ 60) by omega]; exact rT1
  refine callF hap hclr hmv (b := b) (xq := pp (yi / 2 ^ 60)) hst hB.swap hzI hpI.c
    (by have := hzzz; unfold Apart at this ⊢; omega) hzt hra (by rw [montE])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact bv_sub8 (by omega) (by omega))
    (by simp (disch := omega) only [Arm64.Memory.readLE_writeLE_self])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e9])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e10])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14) hfs hx15 (by first | rfl | exact hdf)
    ?mem ?a0 ?a1 ?a2 ?a3 ?a4 ?K
  case mem =>
    repeat (first | exact hM.swap | refine Mem.wr ?_ he _ (by omega))
  case K =>
    intro s' hrip e4 e5 e14 efs e15 edf r0 r3 r1 hM' hsl hzz hz
    have k1 : s'.mem.readLE (sp + 0xb0) 8 = yi := by rw [hsl _ (by omega) (by omega)]; rdw; exact rb0
    have k2 : s'.mem.readLE (sp + 0xe0) 8 = c := by rw [hsl _ (by omega) (by omega)]; rdw; exact re0
    have k3 : s'.mem.readLE (sp + 0xd8) 8 = k0 := by rw [hsl _ (by omega) (by omega)]; rdw; exact qd8
    have k4 : s'.mem.readLE (sp + 0x390) 8 = yp := by rw [hsl _ (by omega) (by omega)]; rdw; exact q390
    have k5 : s'.mem.readLE (sp + 0x3b8) 8 = mc := by rw [hsl _ (by omega) (by omega)]; rdw; exact q3b8
    have k6 : s'.mem.readLE (sp + 0x398) 8 = ylen := by rw [hsl _ (by omega) (by omega)]; rdw; exact q398
    have k7 : s'.mem.readLE (sp + 0x138) 8 = zc := by rw [hsl _ (by omega) (by omega)]; rdw
    have k8 : s'.mem.readLE (sp + 0x140) 8 = n := by rw [hsl _ (by omega) (by omega)]; rdw
    have k9 : s'.mem.readLE (sp + 0x370) 8 = zp := by rw [hsl _ (by omega) (by omega)]; rdw
    have k10 : s'.mem.readLE (sp + 0xe8) 8 = i := by rw [hsl _ (by omega) (by omega)]; rdw; exact re8
    have k11 : s'.mem.readLE (sp + 0x3a8) 8 = mp := by rw [hsl _ (by omega) (by omega)]; rdw; exact q3a8
    have hacc' : s'.mem.accessible (sp - 4296) (4296 + 0x3c0) true = true := by
      rw [hM'.1.1.accessible]; exact he.2.2.2.1
    clear hsl
    refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 6209681) ?_
    janus64_run [k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] until [test]
    refine K _ ?rip ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?r9 ?_ ?_ ?_ ?_ ?mem2 ?m140 ?me8 ?vz ?vzz
    case rip => rw [show test = 6209681 by simp only [test, fnE_eq]]
    case r9 =>
      simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    case mem2 =>
      have := Mem.wr hM' he n (a := sp + 0x140) (by omega)
      exact this
    case m140 => rdw
    case me8 => rdw; exact k10
    case vz => have := hB.1.2.2.2.2.2.1; unfold Apart at this; rdw; rw [hzz]; rdw
    case vzz =>
      have u1 := hB.1.2.2.2.2.2.1; have u2 := hB.2.1.2.2.2.2.2.1; have u3 := hpI.2.2.2
      unfold Apart at u1 u2 u3; rdw; rw [hz]; rdw
      rw [FL.read hM.1 hpI.2.2.1 hpI.2.2.2 hsp1 (hB.2.2.2.2.2.2.2.1 _ hd).1 (hB.2.2.2.2.2.2.2.1 _ hd).2,
        (hst.2.2.2.2.2.2.2.2.2.2.2.1 _ hd).2.1]
    all_goals first
      | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, r0, r1, r3, e4, e5, e14, efs, e15, edf]; done)
      | skip
  all_goals rdw

end FvModexp.Amd64.W4Loop
