import FvModexp.Proofs.Amd64.Exp.W4Pow
import FvModexp.Proofs.Amd64.Exp.W4Seg
import FvModexp.Proofs.Common.MaskWord

set_option autoImplicit false

/-!
# window-4 prologue (amd64): `powers[1] = buf[n:2n:3n].montgomery(x, RR, m, k0, numWords)` (nat.go:1419;
agent expmc s49)

From the return of the `powers[0]` call (fn+0x8bf, its header in `AX, BX, CX`): the header store `powers[0]`
(`0x1a8`), the bounds checks `3n ≤ cap buf`, `2n ≤ 3n`, the slicing `buf[n:2n:3n]`, the call (`callP`, `d = 1`,
return fn+0x995), the header store `powers[1]` (`0x1c0`), `i = 2` and the jump to the table-loop head.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf InpC Inp.c ra_of mont_not)

theorem sl3 {n : Nat} (hn16 : n ≤ 2 ^ 16) : BitVec.ofNat 64 (3 * n) - BitVec.ofNat 64 n = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem sl2 {n : Nat} (hn16 : n ≤ 2 ^ 16) : BitVec.ofNat 64 (2 * n) - BitVec.ofNat 64 n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- the slice pointer of `buf[n:2n:3n]` -/
theorem slc1 {n bp : Nat} (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hbp : bp + 8 * n < 2 ^ 64) :
    ((0#64 - BitVec.ofNat 64 (2 * n)).sshiftRight 63 &&& BitVec.ofNat 64 n <<< 3) + BitVec.ofNat 64 bp =
      BitVec.ofNat 64 (bp + 8 * (1 * n)) := by
  rw [FvModexp.sshr63_allOnes _ (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega), BitVec.allOnes_and]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem p1 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 bp bc xp xc rrp rrc V0 : Nat} {M0 : Memory}
    (hs : PStatic R L g fs sp n mp mc k0 bp bc M0) {ret : W64} {Q : State → Prop} {r5 : W64}
    (hx : Inp R L sp n M0 xp) (hbx : Apart bp (8 * bc) xp (8 * n))
    (hrr : Inp R L sp n M0 rrp) (hbr : Apart bp (8 * bc) rrp (8 * n))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6207775) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n))
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (hF : FP R L sp bp bc M0 S.mem) (hinv : R.inv b L g (view R.rt L S.mem)) (hrg : S.mem.regions = M0.regions)
    (hsl : PSl sp n mp mc k0 bp bc S.mem) (s130 : S.mem.readLE (sp + 0x130) 8 = 3 * n)
    (s370 : S.mem.readLE (sp + 0x370) 8 = xp) (s138 : S.mem.readLE (sp + 0x138) 8 = n)
    (s140 : S.mem.readLE (sp + 0x140) 8 = xc) (s338 : S.mem.readLE (sp + 0x338) 8 = rrp)
    (sf8 : S.mem.readLE (sp + 0xf8) 8 = n) (s100 : S.mem.readLE (sp + 0x100) 8 = rrc)
    (hv0 : S.mem.readLE bp (8 * n) = V0)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 powHead → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 2 → S'.regs 5 = r5 → S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs →
      S'.xmm 15 = 0 → S'.df = false →
      FP R L sp bp bc M0 S'.mem → R.inv b L g (view R.rt L S'.mem) → S'.mem.regions = M0.regions →
      PSl sp n mp mc k0 bp bc S'.mem → Ent sp n (tp bp n) (tc n) (fun _ => V0) S'.mem 0 →
      Ent sp n (tp bp n) (tc n) (fun _ => Exp.montgomery n (M0.readLE xp (8 * n)) (M0.readLE rrp (8 * n))
        (M0.readLE mp (8 * n)) k0) S'.mem 1 →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he := hs.1
  have hn := hs.2.1; have hn16 := hs.2.2.1
  have hsp1 : 4296 ≤ sp := he.2.1; have hsp2 : sp + 0x3c0 ≤ 2 ^ 48 := he.2.2.1
  have hbc := hs.2.2.2.2.2.2.2.1; have hbc' := hs.2.2.2.2.2.2.2.2.1
  have hbb := hs.2.2.2.2.2.2.2.2.2.2.1
  have hacc : S.mem.accessible (sp - 4296) (4296 + 0x3c0) true = true := by
    rw [hF.1.accessible]; exact he.2.2.2.1
  obtain ⟨q3a8, q3b0, q3b8, qd8, q78, qf0, q330⟩ := hsl
  have c1 : (BitVec.ofNat 64 bc < BitVec.ofNat 64 (3 * n)) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show bc < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 3 * n < 2 ^ 64 by omega), eq_iff_iff, iff_false]; omega
  have c2 : (BitVec.ofNat 64 (3 * n) < BitVec.ofNat 64 (2 * n)) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 * n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 3 * n < 2 ^ 64 by omega), eq_iff_iff, iff_false]; omega
  have hrx0 : Apart (bp + 8 * (1 * n)) (8 * (2 * n)) xp (8 * n) := by unfold Apart at hbx ⊢; omega
  have hry0 : Apart (bp + 8 * (1 * n)) (8 * (2 * n)) rrp (8 * n) := by unfold Apart at hbr ⊢; omega
  have hxF := FP.read hF hx.2.2.1 hsp1 hx.2.2.2 hbx.symm
  have hrF := FP.read hF hrr.2.2.1 hsp1 hrr.2.2.2 hbr.symm
  have e3 := sl3 hn16
  have e2 := sl2 hn16
  have es := slc1 (bp := bp) hn hn16 (by omega)
  refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 6184288) ?_
  janus64_run [q3a8, q3b0, q3b8, qd8, q78, qf0, q330, s130, s370, s138, s140, s338, sf8, s100, c1, c2, e3, e2, es]
    until [6184288]
  have hra : RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) (6205536 + 0x995) :=
    ra_of hap mont_not 0x995 (by decide)
  have hLs := he.2.2.2.2.2.2.2.2.2.2.1
  have hwrt : Outside (sp - 4296) (4296 + 0x3c0) R.rt := he.2.2.2.2.2.2.2.1
  have hmp : mp < 2 ^ 64 := by have := hs.2.2.2.2.2.2.1.2.1; omega
  have hmc' : mc < 2 ^ 64 := by have := hs.2.2.2.2.1; omega
  have hk0 : k0 < 2 ^ 64 := hs.2.2.2.2.2.1
  have hbp : bp < 2 ^ 64 := by omega
  have hbw := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxw := hx.2.2.2
  have hrw := hrr.2.2.2
  unfold Apart at hbw hbx hbr hxw hrw
  refine callP hap hclr hmv (b := b) hs (d := 1) (by omega) hx.c hrr.c hrx0 hry0
    hra (by rw [montE']) (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact sub8 (by omega) (by omega))
    (by rdwP) (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, Nat.one_mul])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte])
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte] <;> rfl)
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14) hfs hx15 (by first | rfl | exact hdf)
    ?fp ?inv (by rdwP) (by rdwP) (by rdwP) (by rdwP) (by rdwP) ?K
  case fp =>
    repeat (first | exact hF | refine FP.write ?_ hLs hsp1 _ (by omega))
  case inv =>
    repeat (first | exact hinv | refine FvModexp.Expmc.inv_writeLE (Or.inr (hwrt.of_sub (by omega) (by omega))) ?_)
  case K =>
    intro s' hrip e4 e5 e14 efs e15 edf r0 r3 r1 hF' hinv' hrg' hsl hheld hval
    have hfs' : s'.fsBase.toNat = fs := by rw [efs]; exact hfs
    have hacc' : s'.mem.accessible (sp - 4296) (4296 + 0x3c0) true = true := by
      rw [hF'.1.accessible]; exact he.2.2.2.1
    refine SegProg.lift W4Seg.codeIn (r := BitVec.ofNat 64 powHead) ?_
    janus64_run [] until [powHead]
    have sl : ∀ K, 0x60 ≤ K → K + 8 ≤ 0x3c0 → (K + 8 ≤ 0x1a8 ∨ 0x1d8 ≤ K) →
        (((s'.mem.writeLE (sp + 448) 8 (bp + 8 * n)).writeLE (sp + 456) 8 n).writeLE (sp + 464) 8 (2 * n)).readLE
          (sp + K) 8 = S.mem.readLE (sp + K) 8 := by
      intro K k1 k2 k3
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hsl _ (by omega) (by omega)]
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
    have s0 : ∀ K, 0x1a8 ≤ K → K + 8 ≤ 0x1c0 →
        (((s'.mem.writeLE (sp + 448) 8 (bp + 8 * n)).writeLE (sp + 456) 8 n).writeLE (sp + 464) 8 (2 * n)).readLE
          (sp + K) 8 = (((S.mem.writeLE (sp + 424) 8 bp).writeLE (sp + 432) 8 n).writeLE (sp + 440) 8 (2 * n)).readLE
          (sp + K) 8 := by
      intro K k1 k2
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hsl _ (by omega) (by omega)]
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
    refine K _ rfl ?_ ?_ ?_ ?_ hfs' ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact e4
    · simp only [setRegF_apply, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e5]
      simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact e14
    · exact e15
    · repeat (first | exact hF' | refine FP.write ?_ hLs hsp1 _ (by omega))
    · repeat (first | exact hinv' | refine FvModexp.Expmc.inv_writeLE (Or.inr (hwrt.of_sub (by omega) (by omega))) ?_)
    · simp only [Arm64.Memory.regions_writeLE, hrg', hrg]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [sl 0x3a8 (by omega) (by omega) (by omega)]; exact q3a8
      · rw [sl 0x3b0 (by omega) (by omega) (by omega)]; exact q3b0
      · rw [sl 0x3b8 (by omega) (by omega) (by omega)]; exact q3b8
      · rw [sl 0xd8 (by omega) (by omega) (by omega)]; exact qd8
      · rw [sl 0x78 (by omega) (by omega) (by omega)]; exact q78
      · rw [sl 0xf0 (by omega) (by omega) (by omega)]; exact qf0
      · rw [sl 0x330 (by omega) (by omega) (by omega)]; exact q330
    · have hdh := (inp_ent hs (d := 0) (by omega)).2.2.1
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [tp, Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at hdh ⊢
        simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hheld _ _ hdh (by unfold Apart; omega) (by unfold Apart; omega)]
        simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
        exact hv0
      · rw [show sp + 0x1a8 + 24 * 0 = sp + 0x1a8 by omega, s0 _ (by omega) (by omega)]; rdwP; simp [tp]
      · rw [show sp + 0x1b0 + 24 * 0 = sp + 0x1b0 by omega, s0 _ (by omega) (by omega)]; rdwP
      · rw [show sp + 0x1b8 + 24 * 0 = sp + 0x1b8 by omega, s0 _ (by omega) (by omega)]; rdwP
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [tp]
        simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hval]
        simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hxF, hrF]
      · rw [show sp + 0x1a8 + 24 * 1 = sp + 448 by omega]; rdwP; simp [tp]
      · rw [show sp + 0x1b0 + 24 * 1 = sp + 456 by omega]; rdwP
      · rw [show sp + 0x1b8 + 24 * 1 = sp + 464 by omega]; rdwP

end FvModexp.Amd64.W4Pro
