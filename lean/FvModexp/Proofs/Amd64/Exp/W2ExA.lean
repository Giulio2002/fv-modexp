import FvModexp.Proofs.Amd64.Exp.W2Posts
import FvModexp.Proofs.Amd64.Exp.W2S1

set_option autoImplicit false

/-!
# window-2 (amd64), loop exit → entry of the first `zz.cmp(m)` (nat.go:1478, 1485; agent expmc s46)

Twin of `Arm64.W2Loop.exA`. From the loop exit (+0xf97, `W2Loop.loop`'s `hexit` state): the stack arguments, the call
`zz = zz.montgomery(z, one, m, k0, numWords)` (`callF` on the swapped buffers; `one` = `[sp + 0x210]`, a held array
or — `n ≤ 4`, the compiler's non-escaping buffer — the frame words `[sp + 0x150, sp + 0x170)`, never written by the loop),
its return +0xfe5, the spills `zz → 0x190/0x98/0xa0`, the arguments of `zz.cmp(m)` and the `CALL` (return +0x101a),
up to `nat.cmp`'s entry `0x5e5cc0`. Continuation form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Loop

abbrev cmpE : Nat := 6184128

/-- `one` reads as at the anchor (both cases of `OneIn`) -/
theorem FL.readOne {R : RtInv} {L : List (Nat × Nat)} {g fs sp n zp zc zzp zzc p : Nat} {M0 M : Memory}
    (h : FL R L sp zp zc zzp zzc M0 M) (he : Env R L g fs sp M0) (ho : OneIn R L sp n M0 p)
    (h2 : Apart zp (8 * zc) p (8 * n)) (h3 : Apart zzp (8 * zzc) p (8 * n)) :
    M.readLE p (8 * n) = M0.readLE p (8 * n) := by
  have hs : 4296 ≤ sp := he.2.1
  rcases ho with ⟨-, -, hh, h1⟩ | ⟨rfl, hn⟩
  · exact FL.read h hh h1 hs h2 h3
  · refine h.1.readLE _ _ ?_
    unfold Apart at h2 h3
    have hro : Outside (sp + 0x150) (8 * n) R.rt := he.2.2.2.2.2.2.2.1.of_sub (by omega) (by omega)
    simp only [lw, fw, outside_append, outside_cons, outside_nil, and_true, hro, true_and]
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- loop exit → entry of the first `zz.cmp(m)` (after `zz = zz.montgomery(z, one, …)`) -/
theorem exA {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y : Nat} {tbl pp pcap : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory}
    (hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp pcap M0) {ret : W64} {Q : State → Prop}
    {onep : Nat} (hone : OneIn R L sp n M0 onep) (hone1 : M0.readLE onep (8 * n) = 1)
    (r328 : M0.readLE (sp + 0x210) 8 = onep)
    (S : State) (r5 : W64) (zp zc zzp zzc V : Nat)
    (hpc : S.rip = BitVec.ofNat 64 exit) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (h5 : S.regs 5 = r5)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc) (h8 : S.regs 8 = BitVec.ofNat 64 zzp)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (h12 : S.regs 12 = BitVec.ofNat 64 zzc)
    (h3 : S.regs 3 = BitVec.ofNat 64 mp) (h6 : S.regs 6 = BitVec.ofNat 64 k0) (h10 : S.regs 10 = BitVec.ofNat 64 mc)
    (hB : Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 S.mem zp zc zzp zzc)
    (r140 : S.mem.readLE (sp + 0x148) 8 = n) (hV : S.mem.readLE zp (8 * n) = V)
    (hzo : Apart zp (8 * zc) onep (8 * n)) (hzzo : Apart zzp (8 * zzc) onep (8 * n))
    (KA : ∀ S' : State, S'.rip = BitVec.ofNat 64 cmpE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.mem.readLE (sp - 8) 8 = fnE + 0x101a → S'.regs 5 = r5 → S'.regs 14 = BitVec.ofNat 64 g →
      S'.fsBase = S.fsBase → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 0 = BitVec.ofNat 64 zzp → S'.regs 3 = BitVec.ofNat 64 n → S'.regs 1 = BitVec.ofNat 64 zzc →
      S'.regs 7 = BitVec.ofNat 64 mp → S'.regs 6 = BitVec.ofNat 64 n → S'.regs 8 = BitVec.ofNat 64 mc →
      Mem R b L g sp M0 S'.mem zp zc zzp zzc →
      S'.mem.readLE (sp + 0x190) 8 = zzp → S'.mem.readLE (sp + 0x98) 8 = n → S'.mem.readLE (sp + 0xa0) 8 = zzc →
      S'.mem.readLE zzp (8 * n) = Exp.montgomery n V 1 (M0.readLE mp (8 * n)) k0 →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he := hst.1
  have hsp1 : 4296 ≤ sp := he.2.1; have hsp2 : sp + 0x2a8 ≤ 2 ^ 48 := he.2.2.1
  have hzc := hB.1.2.1; have hzp := hB.1.2.2.2.1; have hzzc := hB.2.1.2.1; have hzzp := hB.2.1.2.2.2.1
  have hn := hst.2.1; have hmc' := hst.2.2.2.2.1; have hk0 := hst.2.2.2.2.2.1
  have hmp : mp < 2 ^ 48 := by have := hst.2.2.2.2.2.2.2.2.1.2.1; omega
  have hn16 := hst.2.2.1
  have hacc : S.mem.accessible (sp - 4296) (4296 + 0x2a8) true = true := by
    rw [hM.1.1.accessible]; exact he.2.2.2.1
  have r3b0 : S.mem.readLE (sp + 0x298) 8 = n := (Static.rd hst hM.1 hB.1 hB.2.1).2.1
  have r328M : S.mem.readLE (sp + 0x210) 8 = onep := by
    rw [FL.slot hM.1 he hB.1 hB.2.1 (by omega) (by omega)
      (by simp only [fw, outside_cons, outside_nil, and_true]; omega)]; exact r328
  have hop : onep + 8 * n ≤ 2 ^ 48 := (OneIn.c he hone).2.1
  janus64_run [r140, r3b0, r328M] until [6184288]
  have hra : RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) 6214629 :=
    ra_of hap mont_not 0xfe5 (by decide)
  have hzI := hB.1.inp
  have hzzz := hB.2.2.1
  refine callF hap hclr hmv (b := b) hst hB.swap hzI (OneIn.c he hone)
    (by have := hzzz; unfold Apart at this ⊢; omega) hzzo hra (by rw [montE])
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
    (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14) hfs hx15 (by first | rfl | exact hdf)
    ?mem ?a0 ?a1 ?a2 ?a3 ?a4 ?K
  case mem =>
    repeat (first | exact hM.swap | refine Mem.wr ?_ he _ (by omega))
  case K =>
    intro s' hrip e4 e5 e14 efs e15 edf r0 r3 r1 hM' hsl hzz hz
    have hM'' := hM'.swap
    have hacc' : s'.mem.accessible (sp - 4296) (4296 + 0x2a8) true = true := by
      rw [hM''.1.1.accessible]; exact he.2.2.2.1
    have hrd := Static.rd hst hM''.1 hB.1 hB.2.1
    have q8 : s'.mem.readLE (sp + 0x290) 8 = mp := hrd.1
    have q0 : s'.mem.readLE (sp + 0x298) 8 = n := hrd.2.1
    have qb : s'.mem.readLE (sp + 0x2a0) 8 = mc := hrd.2.2.1
    have hval : s'.mem.readLE zzp (8 * n) = Exp.montgomery n V 1 (M0.readLE mp (8 * n)) k0 := by
      rw [hz]
      have u1 := hB.1.2.2.2.2.2.1; have u2 := (OneIn.c he hone).2.2.2; unfold Apart at u1 u2
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hV, FL.readOne hM.1 he hone hzo hzzo, hone1]
    clear hz hzz hsl
    janus64_run [q8, q0, qb] until [cmpE]
    refine KA _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rfl
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact bv_sub8 (by omega) (by omega)
    · rdw; rw [fnE_eq]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [e5]
      simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact e14
    · exact efs
    · exact e15
    · rfl
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact r0
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact r3
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact r1
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · repeat (first | exact hM'' | refine Mem.wr ?_ he _ (by omega))
    · rdw
    · rdw
    · rdw
    · have u1 := hB.2.1.2.2.2.2.2.1; unfold Apart at u1
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; exact hval
  all_goals rdw

end FvModexp.Amd64.W2Loop
