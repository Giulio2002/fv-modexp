import FvModexp.Proofs.Amd64.Exp.W4PowDefs

set_option autoImplicit false

/-!
# window-4 prologue (amd64): one table `nat.montgomery` call at the callee entry (agent expmc s49)

`callP`: a call `buf[d·n:(d+1)·n:(d+2)·n].montgomery(x, y, m, k0, n)` (`d ≤ 15`) of the table code at the callee
entry (`RSP = sp - 8`, return address pushed, stack arguments `m, len m, cap m, k0, n` at `sp … sp + 0x20`) returns to
`ra` with the table frame `FP` re-established, the frame words above the callee window unchanged, every held object
apart from the frame and from the written slice unchanged, and the slice = `montgomery(x, y, m, k0)` (`m` at the
anchor). Proved once (SPEED LESSONS: stop at the callee entry).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W4Pro

open FvModexp.Amd64.W4Loop (Env Inp Buf InpC montCall sp_add8)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem callP {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 bp bc : Nat} {M0 : Memory}
    (hs : PStatic R L g fs sp n mp mc k0 bp bc M0)
    {d xp xq : Nat} {zl xc yc : BitVec 64} {S : State} {ret : W64} {Q : State → Prop} {ra : Nat} (hd : d ≤ 15)
    (hx : InpC R L sp n M0 xp) (hy : InpC R L sp n M0 xq)
    (hrx : Apart (bp + 8 * (d * n)) (8 * (2 * n)) xp (8 * n)) (hry : Apart (bp + 8 * (d * n)) (8 * (2 * n)) xq (8 * n))
    (hra : RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr LibW.program MontHyp.fn))
    (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8)) (hrd : S.mem.readLE (sp - 8) 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 (bp + 8 * (d * n))) (h3 : S.regs 3 = zl) (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n))
    (h7 : S.regs 7 = BitVec.ofNat 64 xp) (h6 : S.regs 6 = BitVec.ofNat 64 n) (h8 : S.regs 8 = xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 xq) (h10 : S.regs 10 = BitVec.ofNat 64 n) (h11 : S.regs 11 = yc)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hF : FP R L sp bp bc M0 S.mem) (hinv : R.inv b L g (view R.rt L S.mem))
    (a0 : S.mem.readLE sp 8 = mp) (a1 : S.mem.readLE (sp + 8) 8 = n) (a2 : S.mem.readLE (sp + 16) 8 = mc)
    (a3 : S.mem.readLE (sp + 24) 8 = k0) (a4 : S.mem.readLE (sp + 32) 8 = n)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = BitVec.ofNat 64 sp → s'.regs 5 = S.regs 5 →
      s'.regs 14 = BitVec.ofNat 64 g → s'.fsBase = S.fsBase → s'.xmm 15 = 0 → s'.df = false →
      s'.regs 0 = BitVec.ofNat 64 (bp + 8 * (d * n)) → s'.regs 3 = BitVec.ofNat 64 n →
      s'.regs 1 = BitVec.ofNat 64 (2 * n) →
      FP R L sp bp bc M0 s'.mem → R.inv b L g (view R.rt L s'.mem) → s'.mem.regions = S.mem.regions →
      (∀ a, sp + 96 ≤ a → a + 8 ≤ sp + 0x3c0 → s'.mem.readLE a 8 = S.mem.readLE a 8) →
      (∀ a k, (InRanges a k L ∨ Outside a k R.rt) → Apart a k (sp - 4296) (4296 + 0x60) →
        Apart a k (bp + 8 * (d * n)) (8 * (2 * n)) → s'.mem.readLE a k = S.mem.readLE a k) →
      s'.mem.readLE (bp + 8 * (d * n)) (8 * n) =
        Exp.montgomery n (S.mem.readLE xp (8 * n)) (S.mem.readLE xq (8 * n)) (M0.readLE mp (8 * n)) k0 →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hB := buf_sub hs hd
  have hdn : d * n + 2 * n ≤ bc := by
    have := Nat.mul_le_mul_right n (show d + 2 ≤ 17 by omega); rw [Nat.add_mul] at this; have := hs.2.2.2.2.2.2.2.1
    omega
  obtain ⟨he, hn, -, hmc, hmc', hk0, hm, -, -, -, -, -, hbw, hbg, hbf, hbm, hok⟩ := hs
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', hfacc, hfrd, h15', h16', hadx⟩ := he
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hB
  have sub : ∀ p k, Apart p k (sp - 4296) (4296 + 0x3c0) → Apart p k (sp - 8 - 4288) (4288 + 104) := by
    intro p k h; unfold Apart at h ⊢; omega
  have subC : ∀ p k, Apart p k (sp - 4296) (4296 + 0x60) → Apart p k (sp - 8 - 4288) (4288 + 104) := by
    intro p k h; unfold Apart at h ⊢; omega
  have hrm : Apart (bp + 8 * (d * n)) (8 * (2 * n)) mp (8 * n) := by unfold Apart at hbm ⊢; omega
  have hc : MontW.MCall R L g (M0.readLE (g + 16) 8) fs (sp - 8) n mp mc (bp + 8 * (d * n)) (2 * n) xp xq := by
    refine ⟨by omega, by omega, by omega, h5', by omega,
      h8'.of_sub (by omega) (by omega), sub _ _ h9', h10', ?_, h12', sub _ _ h15', h16', hn, r1, r2, hmc, hmc', r4, r5,
      sub _ _ r6, r7, r8,
      ⟨hx.2.1, hx.2.2.1, subC _ _ hx.2.2.2⟩, ⟨hy.2.1, hy.2.2.1, subC _ _ hy.2.2.2⟩,
      ⟨hm.2.1, hm.2.2.1, sub _ _ hm.2.2.2⟩, hrx, hry, hrm, (hok _).1, (hok _).2⟩
    intro r hr
    have := h11' r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  obtain ⟨hFm, hLF⟩ := hF
  have hF0 := hFm
  simp only [pl, pw, List.append_assoc, List.cons_append, List.nil_append] at hF0
  have u0 := hbw; unfold Apart at u0
  have hgM : S.mem.readLE (g + 16) 8 = M0.readLE (g + 16) 8 := by
    refine hF0.readLE _ _ ?_
    have u1 := h9'; have u2 := hbg
    unfold Apart at u1 u2
    simp only [outside_append, outside_cons, outside_nil, and_true, h10', true_and]
    omega
  have hfM : S.mem.readLE (fs - 8) 8 = M0.readLE (fs - 8) 8 := by
    refine hF0.readLE _ _ ?_
    have u1 := h15'; have u2 := hbf
    unfold Apart at u1 u2
    simp only [outside_append, outside_cons, outside_nil, and_true, h16', true_and]
    omega
  have hsN : (S.regs 4).toNat = sp - 8 := by rw [hsp]; exact MontW.toNat_of (by omega)
  have hdy : MontW.MDyn R b L g (M0.readLE (g + 16) 8) fs (sp - 8) n mp mc (bp + 8 * (d * n)) (2 * n) xp xq k0 S := by
    refine ⟨hsN, by rw [h14]; exact MontW.toNat_of (by omega), hfs, ?_, by rw [hFm.accessible]; exact h6', hgM,
      by rw [hFm.accessible]; exact hfacc, by rw [hfM]; exact hfrd,
      by rw [show sp - 8 + 8 = sp by omega]; exact a0, by rw [show sp - 8 + 16 = sp + 8 by omega]; exact a1,
      by rw [show sp - 8 + 24 = sp + 16 by omega]; exact a2, by rw [show sp - 8 + 32 = sp + 24 by omega]; exact a3,
      by rw [show sp - 8 + 40 = sp + 32 by omega]; exact a4,
      by rw [hFm.accessible]; exact r3, by rw [hFm.accessible]; exact hx.1, by rw [hFm.accessible]; exact hy.1,
      by rw [hFm.accessible]; exact hm.1, by rw [hFm.accessible]; exact hadx, hinv⟩
    rw [hFm.accessible]; exact Arm64.Memory.accessible_sub (m := M0) h4' (Or.inr rfl) (by omega) (by omega)
  refine montCall hap hclr hmv hc hk0 hra hpc (by rw [hsN]; exact hrd) h0 h3 h1 h7 h6 h8 h9 h10 h11 hx15 hdf hdy ?_
  intro s' hrip hq hrg'
  obtain ⟨⟨e4, e5, e14, e15⟩, efs, edf, q0, q3, q1, hval, hinv', hF', hLF'⟩ := hq
  have hfp := FP.call ⟨hFm, hLF⟩ hF' hLF' ⟨by omega, by omega⟩ h2'
  refine K s' hrip (by rw [e4, hsp]; exact sp_add8 (by omega) (by omega)) e5 (by rw [e14, h14]) efs
    (by rw [e15, hx15]) (by rw [edf, hdf]) q0 q3 q1 hfp hinv' hrg' ?_ ?_ ?_
  · intro a ha1 ha2
    refine hF'.readLE _ _ ?_
    have u1 := r6; unfold Apart at u1
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨h8'.of_sub (by omega) (by omega), by omega⟩, by omega⟩
  · intro a k hh ha1 ha2
    unfold Apart at ha1 ha2
    exact FvModexp.Expmc.held_readLE hh hF' hLF' (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  · rw [hval, FP.read ⟨hFm, hLF⟩ hm.2.2.1 h2' hm.2.2.2 (by unfold Apart at hbm ⊢; omega)]

end FvModexp.Amd64.W4Pro
