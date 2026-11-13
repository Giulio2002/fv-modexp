import FvModexp.Proofs.Amd64.Exp.W2MC

set_option autoImplicit false

/-!
# window-2 (amd64): one `nat.montgomery` call of the main loop at the callee entry (agent expmc s60, ported from the window-4 twin)

`callF`: every one of the three calls of the loop body (nat.go:1586-1589) writes into one of the two buffers; stated for
the FIRST buffer `zp` of `Bufs`/`Mem` (calls into `zz` use `Bufs.swap`/`FL.swap`). At the callee entry (`RSP = sp - 8`,
return address pushed, stack arguments `m, len m, cap m, k0, n` at `sp … sp + 0x20`) the call returns to `ra` with the
loop's frame facts re-established (`Mem`), the frame slots above the callee window unchanged, the other buffer unchanged
and `z = montgomery(x, y, m, k0)` (`m` read at the anchor). Proved once; the body segments only run to the entry.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.W2Loop

theorem Buf.inp {R : RtInv} {L : List (Nat × Nat)} {g fs sp n : Nat} {M0 : Memory} {p c : Nat}
    (h : Buf R L g fs sp n M0 p c) : Inp R L sp n M0 p :=
  ⟨M0.accessible_sub h.2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega), by omega,
    h.2.2.2.2.1.imp (fun h' => h'.sub (Nat.le_refl _) (by omega)) (fun h' => h'.of_sub (Nat.le_refl _) (by omega)),
    by have := h.2.2.2.2.2.1; unfold Apart at this ⊢; omega⟩

theorem sp_add8 {sp : Nat} (h1 : 8 ≤ sp) (h2 : sp < 2 ^ 64) :
    BitVec.ofNat 64 (sp - 8) + 8#64 = BitVec.ofNat 64 sp := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- the input facts `MontW.MCall` needs of an operand (apart from the callee window `[sp - 4296, sp + 0x60)` only;
`one` may be the frame buffer `sp + 0x150` for `n ≤ 4`) -/
@[reducible] def InpC (R : RtInv) (L : List (Nat × Nat)) (sp n : Nat) (M0 : Memory) (p : Nat) : Prop :=
  M0.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧ (InRanges p (8 * n) L ∨ Outside p (8 * n) R.rt) ∧
  Apart p (8 * n) (sp - 4296) (4296 + 0x60)

theorem Inp.c {R : RtInv} {L : List (Nat × Nat)} {sp n : Nat} {M0 : Memory} {p : Nat}
    (h : Inp R L sp n M0 p) : InpC R L sp n M0 p :=
  ⟨h.1, h.2.1, h.2.2.1, by have := h.2.2.2; unfold Apart at this ⊢; omega⟩

set_option maxRecDepth 20000 in
theorem mcall_ofC {R : RtInv} {L : List (Nat × Nat)} {g fs sp n mp mc rp rc xp yp : Nat} {M0 : Memory}
    (he : Env R L g fs sp M0) (hn : 0 < n) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hr : Buf R L g fs sp n M0 rp rc)
    (hx : Inp R L sp n M0 xp) (hy : InpC R L sp n M0 yp) (hm : Inp R L sp n M0 mp)
    (hrx : Apart rp (8 * rc) xp (8 * n)) (hry : Apart rp (8 * rc) yp (8 * n)) (hrm : Apart rp (8 * rc) mp (8 * n))
    (hok : R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, n * 8]) :
    MontW.MCall R L g (M0.readLE (g + 16) 8) fs (sp - 8) n mp mc rp rc xp yp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, -, h15, h16, -⟩ := he
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := hr
  have sub : ∀ p k, Apart p k (sp - 4296) (4296 + 0x2a8) → Apart p k (sp - 8 - 4288) (4288 + 104) := by
    intro p k h; unfold Apart at h ⊢; omega
  have subC : ∀ p k, Apart p k (sp - 4296) (4296 + 0x60) → Apart p k (sp - 8 - 4288) (4288 + 104) := by
    intro p k h; unfold Apart at h ⊢; omega
  refine ⟨by omega, by omega, by omega, h5, by omega,
    h8.of_sub (by omega) (by omega), sub _ _ h9, h10, ?_, h12, sub _ _ h15, h16, hn, r1, r2, hmc, hmc', r4, r5,
    sub _ _ r6, r7, r8,
    ⟨hx.2.1, hx.2.2.1, sub _ _ hx.2.2.2⟩, ⟨hy.2.1, hy.2.2.1, subC _ _ hy.2.2.2⟩,
    ⟨hm.2.1, hm.2.2.1, sub _ _ hm.2.2.2⟩, hrx, hry, hrm, hok.1, hok.2⟩
  intro r hr
  have := h11 r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **one montgomery call of the loop body** (into the first buffer), at the callee entry -/
theorem callF {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y : Nat} {tbl pp pcap : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory}
    (hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp pcap M0)
    {zp zc zzp zzc xp xq : Nat} {zl xc yc : BitVec 64} {S : State} {ret : W64} {Q : State → Prop} {ra : Nat}
    (hB : Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc)
    (hx : Inp R L sp n M0 xp) (hy : InpC R L sp n M0 xq)
    (hrx : Apart zp (8 * zc) xp (8 * n)) (hry : Apart zp (8 * zc) xq (8 * n))
    (hra : RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) ra)
    (hpc : S.rip = BitVec.ofNat 64 (segAddr LibW.program MontHyp.fn))
    (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8)) (hrd : S.mem.readLE (sp - 8) 8 = ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h3 : S.regs 3 = zl) (h1 : S.regs 1 = BitVec.ofNat 64 zc)
    (h7 : S.regs 7 = BitVec.ofNat 64 xp) (h6 : S.regs 6 = BitVec.ofNat 64 n) (h8 : S.regs 8 = xc)
    (h9 : S.regs 9 = BitVec.ofNat 64 xq) (h10 : S.regs 10 = BitVec.ofNat 64 n) (h11 : S.regs 11 = yc)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (hM : Mem R b L g sp M0 S.mem zp zc zzp zzc)
    (a0 : S.mem.readLE sp 8 = mp) (a1 : S.mem.readLE (sp + 8) 8 = n) (a2 : S.mem.readLE (sp + 16) 8 = mc)
    (a3 : S.mem.readLE (sp + 24) 8 = k0) (a4 : S.mem.readLE (sp + 32) 8 = n)
    (K : ∀ s' : State, s'.rip = BitVec.ofNat 64 ra → s'.regs 4 = BitVec.ofNat 64 sp → s'.regs 5 = S.regs 5 →
      s'.regs 14 = BitVec.ofNat 64 g → s'.fsBase = S.fsBase → s'.xmm 15 = 0 → s'.df = false →
      s'.regs 0 = BitVec.ofNat 64 zp → s'.regs 3 = BitVec.ofNat 64 n → s'.regs 1 = BitVec.ofNat 64 zc →
      Mem R b L g sp M0 s'.mem zp zc zzp zzc →
      (∀ a, sp + 96 ≤ a → a + 8 ≤ sp + 0x2a8 → s'.mem.readLE a 8 = S.mem.readLE a 8) →
      s'.mem.readLE zzp (8 * n) = S.mem.readLE zzp (8 * n) →
      s'.mem.readLE zp (8 * n) =
        Exp.montgomery n (S.mem.readLE xp (8 * n)) (S.mem.readLE xq (8 * n)) (M0.readLE mp (8 * n)) k0 →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  obtain ⟨he, hn, -, hmc, hmc', hk0, -, -, hm, -, -, -, -, -, -, -, -, -, hok⟩ := hst
  have hc := mcall_ofC he hn hmc hmc' hB.1 hx hy hm hrx hry hB.2.2.2.1 (hok zp)
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he
  obtain ⟨⟨hF, hLF⟩, hinv, hrg⟩ := hM
  obtain ⟨hBz, hBzz, hzzz, hzm, hzzm, -, -, -, -⟩ := hB
  have hz3 := hBz.2.2.1; have hz6 := hBz.2.2.2.2.2.1; have hz7 := hBz.2.2.2.2.2.2.1; have hz8 := hBz.2.2.2.2.2.2.2
  have hzz6 := hBzz.2.2.2.2.2.1; have hzz7 := hBzz.2.2.2.2.2.2.1; have hzz8 := hBzz.2.2.2.2.2.2.2
  have hF0 := hF
  simp only [lw, fw, List.append_assoc, List.cons_append, List.nil_append] at hF0
  have hgM : S.mem.readLE (g + 16) 8 = M0.readLE (g + 16) 8 := by
    refine hF0.readLE _ _ ?_
    have u1 := hgw; have u2 := hz7; have u3 := hzz7
    clear hz6 hzz6 hzzz hzm hzzm hz8 hzz8 hfw
    unfold Apart at u1 u2 u3
    simp only [outside_append, outside_cons, outside_nil, and_true, hgrt, true_and]
    omega
  have hfM : S.mem.readLE (fs - 8) 8 = M0.readLE (fs - 8) 8 := by
    refine hF0.readLE _ _ ?_
    have u1 := hfw; have u2 := hz8; have u3 := hzz8
    clear hz6 hzz6 hzzz hzm hzzm hz7 hzz7 hgw
    unfold Apart at u1 u2 u3
    simp only [outside_append, outside_cons, outside_nil, and_true, hfrt, true_and]
    omega
  have hsN : (S.regs 4).toNat = sp - 8 := by rw [hsp]; exact MontW.toNat_of (by omega)
  have hd : MontW.MDyn R b L g (M0.readLE (g + 16) 8) fs (sp - 8) n mp mc zp zc xp xq k0 S := by
    refine ⟨hsN, by rw [h14]; exact MontW.toNat_of (by omega), hfs, ?_, by rw [hF.accessible]; exact hg2, hgM,
      by rw [hF.accessible]; exact hfacc, by rw [hfM]; exact hfrd,
      by rw [show sp - 8 + 8 = sp by omega]; exact a0, by rw [show sp - 8 + 16 = sp + 8 by omega]; exact a1,
      by rw [show sp - 8 + 24 = sp + 16 by omega]; exact a2, by rw [show sp - 8 + 32 = sp + 24 by omega]; exact a3,
      by rw [show sp - 8 + 40 = sp + 32 by omega]; exact a4,
      by rw [hF.accessible]; exact hz3, by rw [hF.accessible]; exact hx.1, by rw [hF.accessible]; exact hy.1,
      by rw [hF.accessible]; exact hm.1, by rw [hF.accessible]; exact hadx, hinv⟩
    rw [hF.accessible]; exact M0.accessible_sub hwacc (Or.inr rfl) (by omega) (by omega)
  refine montCall hap hclr hmv hc hk0 hra hpc (by rw [hsN]; exact hrd) h0 h3 h1 h7 h6 h8 h9 h10 h11 hx15 hdf hd ?_
  intro s' hrip hq hrg'
  obtain ⟨⟨e4, e5, e14, e15⟩, efs, edf, r0, r3, r1, hval, hinv', hF', hLF'⟩ := hq
  have hfl := FL.call ⟨hF, hLF⟩ hF' hLF' (Or.inl ⟨rfl, rfl⟩) hsp1
  clear hz7 hzz7 hz8 hzz8 hgw hfw hrx hry
  refine K s' hrip (by rw [e4, hsp]; exact sp_add8 (by omega) (by omega)) e5 (by rw [e14, h14]) efs
    (by rw [e15, hx15]) (by rw [edf, hdf]) r0 r3 r1 ⟨hfl, hinv', by rw [hrg', hrg]⟩ ?_ ?_ ?_
  · intro a ha1 ha2
    refine hF'.readLE _ _ ?_
    have u1 := hz6; unfold Apart at u1
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hwrt.of_sub (by omega) (by omega), by omega⟩, by omega⟩
  · refine FvModexp.Expmc.held_readLE
      (hBzz.2.2.2.2.1.imp (fun h' => h'.sub (Nat.le_refl _) (by omega)) (fun h' => h'.of_sub (Nat.le_refl _) (by omega)))
      hF' hLF' (by have u0 := hBzz.1; have u1 := hzz6; unfold Apart at u1; simp only [outside_cons, outside_nil, and_true]; omega)
      (by have u0 := hBzz.1; have u1 := hzzz; unfold Apart at u1; simp only [outside_cons, outside_nil, and_true]; omega)
  · rw [hval, FL.read ⟨hF, hLF⟩ hm.2.2.1 hm.2.2.2 hsp1 hzm hzzm]

end FvModexp.Amd64.W2Loop
