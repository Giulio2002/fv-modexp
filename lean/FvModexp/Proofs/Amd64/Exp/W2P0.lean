import FvModexp.Proofs.Amd64.Exp.W2Pow
import FvModexp.Proofs.Amd64.Exp.W2Seg
import FvModexp.Proofs.Amd64.Exp.W2ExA

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `powers[0] = buf[0:n:2n].montgomery(one, RR, m, k0, numWords)` (nat.go:1551;
agent expmc s49)

From the return of `stk.nat(5n)` (`p01` = fn+0x852, `AX = bp`, `CX = cap`) through the bounds checks, the spills
`bc → 0xf0`, `bp → 0x218`, `3n → 0x148`, `k0 = -t → 0xd8` (`computeMontgomeryk0` returns `-t`, nat.go:1280), the
call (`callP`, `d = 0`) up to its return fn+0x8ff.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf InpC Inp.c ra_of mont_not OneIn OneIn.c)

theorem negk {t : Nat} (ht : t < 2 ^ 64) : -BitVec.ofNat 64 t = BitVec.ofNat 64 ((2 ^ 64 - t) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem p0 {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc t bp bc onep rrp rrc : Nat} {M : Memory}
    (hs : PStatic R L g fs sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) bp bc M) (ht : t < 2 ^ 64)
    {ret : W64} {Q : State → Prop} {r5 : W64}
    (hone : OneIn R L sp n M onep) (hbo : Apart bp (8 * bc) onep (8 * n))
    (hrr : Inp R L sp n M rrp) (hbr : Apart bp (8 * bc) rrp (8 * n))
    (s78 : M.readLE (sp + 0x78) 8 = 2 * n) (s3b0 : M.readLE (sp + 0x298) 8 = n) (s3a8 : M.readLE (sp + 0x290) 8 = mp)
    (s3b8 : M.readLE (sp + 0x2a0) 8 = mc) (sd8 : M.readLE (sp + 0xd8) 8 = t) (s328 : M.readLE (sp + 0x210) 8 = onep)
    (s338 : M.readLE (sp + 0x220) 8 = rrp) (sf8 : M.readLE (sp + 0xf8) 8 = n) (s100 : M.readLE (sp + 0x100) 8 = rrc)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 p01) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h1 : S.regs 1 = BitVec.ofNat 64 bc)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 6212863 → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 bp → S'.regs 3 = BitVec.ofNat 64 n → S'.regs 1 = BitVec.ofNat 64 (2 * n) →
      S'.regs 5 = r5 → S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      FP R L sp bp bc M S'.mem → R.inv b L g (view R.rt L S'.mem) → S'.mem.regions = M.regions →
      PSl sp n mp mc ((2 ^ 64 - t) % 2 ^ 64) bp bc S'.mem → S'.mem.readLE (sp + 0x148) 8 = 3 * n →
      (∀ K, 0x60 ≤ K → K + 8 ≤ 0x2a8 → (K + 8 ≤ 0xd8 ∨ 0xe0 ≤ K) → (K + 8 ≤ 0xf0 ∨ 0xf8 ≤ K) →
        (K + 8 ≤ 0x148 ∨ 0x150 ≤ K) → (K + 8 ≤ 0x218 ∨ 0x220 ≤ K) → S'.mem.readLE (sp + K) 8 = M.readLE (sp + K) 8) →
      S'.mem.readLE bp (8 * n) =
        Exp.montgomery n (M.readLE onep (8 * n)) (M.readLE rrp (8 * n)) (M.readLE mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64) →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he := hs.1
  have hn := hs.2.1; have hn16 := hs.2.2.1
  have hsp1 : 4296 ≤ sp := he.2.1; have hsp2 : sp + 0x2a8 ≤ 2 ^ 48 := he.2.2.1
  have hbc := hs.2.2.2.2.2.2.2.1; have hbc' := hs.2.2.2.2.2.2.2.2.1
  have hacc : M.accessible (sp - 4296) (4296 + 0x2a8) true = true := he.2.2.2.1
  have c1 : (BitVec.ofNat 64 bc < BitVec.ofNat 64 (2 * n)) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]; omega
  have c2 : (BitVec.ofNat 64 (2 * n) < BitVec.ofNat 64 n) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]; omega
  have nk := negk ht
  have hrx0 : Apart (bp + 8 * (0 * n)) (8 * (2 * n)) onep (8 * n) := by unfold Apart at hbo ⊢; omega
  have hry0 : Apart (bp + 8 * (0 * n)) (8 * (2 * n)) rrp (8 * n) := by unfold Apart at hbr ⊢; omega
  have hbp : bp < 2 ^ 64 := by have := hs.2.2.2.2.2.2.2.2.2.2.1; omega
  refine SegProg.lift W2Seg.codeIn (r := BitVec.ofNat 64 6184288) ?_
  janus64_run [s78, s3b0, s3a8, s3b8, sd8, s328, s338, sf8, s100, c1, c2, nk] until [6184288]
  have hra : RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) (6210560 + 0x8ff) :=
    ra_of hap mont_not 0x8ff (by decide)
  have hLs := he.2.2.2.2.2.2.2.2.2.2.1
  have hwrt : Outside (sp - 4296) (4296 + 0x2a8) R.rt := he.2.2.2.2.2.2.2.1
  have hmp : mp < 2 ^ 64 := by have := hs.2.2.2.2.2.2.1.2.1; omega
  have hmc' : mc < 2 ^ 64 := by have := hs.2.2.2.2.1; omega
  have hbw := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrw := hrr.2.2.2
  unfold Apart at hbw hbo hbr hrw
  have hxI := OneIn.c he hone
  have hFM : FP R L sp bp bc M M := ⟨MemFrame.refl _ _, LiveFrame.refl _ _ _⟩
  refine callP hap hclr hmv (b := b) hs (d := 0) (by omega) hxI hrr.c hrx0 hry0
    hra (by rw [montE']) (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact sub8 (by omega) (by omega))
    (by rdwP) (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [h0]; simp)
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
    repeat (first | exact hFM | refine FP.write ?_ hLs hsp1 _ (by omega))
  case inv =>
    repeat (first | exact hinv | refine FvModexp.Expmc.inv_writeLE (Or.inr (hwrt.of_sub (by omega) (by omega))) ?_)
  case K =>
    intro s' hrip e4 e5 e14 efs e15 edf r0 r3 r1 hF' hinv' hrg' hsl hheld hval
    have sl : ∀ K, 0x60 ≤ K → K + 8 ≤ 0x2a8 → (K + 8 ≤ 0xd8 ∨ 0xe0 ≤ K) → (K + 8 ≤ 0xf0 ∨ 0xf8 ≤ K) →
        (K + 8 ≤ 0x148 ∨ 0x150 ≤ K) → (K + 8 ≤ 0x218 ∨ 0x220 ≤ K) → s'.mem.readLE (sp + K) 8 = M.readLE (sp + K) 8 := by
      intro K k1 k2 k3 k4 k5 k6
      rw [hsl _ (by omega) (by omega)]
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
    refine K s' hrip e4 (by rw [r0]; simp) r3 r1 (by rw [e5]; try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; try exact h5)
      (by rw [e14]; try simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; try exact h14) (by rw [efs]; exact hfs) e15 edf
      hF' hinv' (by rw [hrg']; simp only [Arm64.Memory.regions_writeLE]) ?_ ?_ sl ?_
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [sl 0x290 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact s3a8
      · rw [sl 0x298 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact s3b0
      · rw [sl 0x2a0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact s3b8
      · rw [hsl _ (by omega) (by omega)]; rdwP
      · rw [sl 0x78 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact s78
      · rw [hsl _ (by omega) (by omega)]; rdwP
      · rw [hsl _ (by omega) (by omega)]; rdwP
    · rw [hsl _ (by omega) (by omega)]; rdwP; omega
    · have e0 : bp + 8 * (0 * n) = bp := by simp
      rw [e0] at hval
      rw [hval]
      refine (congrArg (fun a => Exp.montgomery n a _ (Arm64.Memory.readLE M mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64)) ?_).trans
        (congrArg (fun b => Exp.montgomery n (Arm64.Memory.readLE M onep (8 * n)) b (Arm64.Memory.readLE M mp (8 * n)) ((2 ^ 64 - t) % 2 ^ 64)) ?_)
      · rcases hone with h | ⟨rfl, h4⟩
        · have := h.2.2.2; unfold Apart at this; rdwP
        · rdwP
      · rdwP

end FvModexp.Amd64.W2Pro
