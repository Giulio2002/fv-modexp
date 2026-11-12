import FvModexp.Proofs.Arm64.Exp.W2P01Defs

/-!
# window-2 prologue (arm64): `powers[0]`, `powers[1]` (nat.go:1411-1414), `p01 → powHead`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W2Pro

open FvModexp.Arm64.W2Loop (Env Inp Buf)

theorem neg_ofNat (t : Nat) (ht : t < 2 ^ 64) : 0#64 - BitVec.ofNat 64 t = BitVec.ofNat 64 ((2 ^ 64 - t) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `buf[n:2n:3n]`'s pointer as the executor computes it (slice mask of `n - 3n < 0`) -/
theorem slice1 (bp n : Nat) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hb : bp + 8 * n < 2 ^ 64) :
    BitVec.ofNat 64 bp + (BitVec.ofNat 64 n &&& (BitVec.ofNat 64 n - BitVec.ofNat 64 (n + n * 2)).sshiftRight 63) <<< 3 =
      BitVec.ofNat 64 (bp + 8 * n) := by
  have h3 : (n + n * 2) % 2 ^ 64 = 3 * n := by
    rw [Nat.mod_eq_of_lt (show n + n * 2 < 2 ^ 64 by omega)]; omega
  have h4 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)
  have h5 : (2 ^ 64 - 3 * n + n) % 2 ^ 64 = 2 ^ 64 - 2 * n := by
    rw [show 2 ^ 64 - 3 * n + n = 2 ^ 64 - 2 * n by omega]; exact Nat.mod_eq_of_lt (by omega)
  rw [FvModexp.sshr63_allOnes _ (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h3, h4, h5]; omega),
    BitVec.and_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem sub_nn (n : Nat) (_hn16 : n ≤ 2 ^ 16) : BitVec.ofNat 64 (2 * n) - BitVec.ofNat 64 n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem sub_3n (n : Nat) (hn16 : n ≤ 2 ^ 16) :
    BitVec.ofNat 64 (n + n * 2) - BitVec.ofNat 64 n = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem p01run (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc t bp onep rrp rrc xp xc : Nat) (M : Memory) (r18 r29 : BitVec 64)
    (he : Env R L g sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (ht : t < 2 ^ 64)
    (hm : Inp R L sp n M mp)
    (hba : M.accessible bp (8 * (5 * n)) true = true) (hbb : bp + 8 * (5 * n) ≤ 2 ^ 48)
    (hbh : InRanges bp (8 * (5 * n)) L ∨ Outside bp (8 * (5 * n)) R.rt)
    (hbw : Apart bp (8 * (5 * n)) (sp - 4288) (4288 + 752)) (hbg : Apart (g + 16) 8 bp (8 * (5 * n)))
    (hbm : Apart bp (8 * (5 * n)) mp (8 * n))
    (hone : OneIn R L sp n M onep) (hbo : Apart bp (8 * (5 * n)) onep (8 * n))
    (hrr : Inp R L sp n M rrp) (hbR : Apart bp (8 * (5 * n)) rrp (8 * n))
    (hx : Inp R L sp n M xp) (hbx : Apart bp (8 * (5 * n)) xp (8 * n))
    (r728 : M.readLE (sp + 728) 8 = mp) (r736 : M.readLE (sp + 736) 8 = n) (r744 : M.readLE (sp + 744) 8 = mc)
    (r224 : M.readLE (sp + 224) 8 = t) (r128 : M.readLE (sp + 128) 8 = 2 * n) (r528 : M.readLE (sp + 528) 8 = onep)
    (r544 : M.readLE (sp + 544) 8 = rrp) (r256 : M.readLE (sp + 256) 8 = n) (r264 : M.readLE (sp + 264) 8 = rrc)
    (r616 : M.readLE (sp + 616) 8 = xp) (r328 : M.readLE (sp + 328) 8 = xc) (r320 : M.readLE (sp + 320) 8 = n)
    (hok : ∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.pc = BitVec.ofNat 64 p01) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h1 : S.regs 1 = BitVec.ofNat 64 (5 * n))
    (h2 : S.regs 2 = BitVec.ofNat 64 (5 * n))
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (K : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 powHead → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 2 → S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 →
      S'.mem = M' → FQ R L sp bp (5 * n) M M' → R.inv b L g (view R.rt L M') → M'.regions = M.regions →
      M'.readLE (sp + 224) 8 = (2 ^ 64 - t) % 2 ^ 64 → M'.readLE (sp + 248) 8 = 5 * n →
      M'.readLE (sp + 536) 8 = bp →
      Ent sp n bp (fun _ => Exp.montgomery n (M.readLE onep (8 * n)) (M.readLE rrp (8 * n)) (M.readLE mp (8 * n))
        ((2 ^ 64 - t) % 2 ^ 64)) M' 0 →
      Ent sp n bp (fun _ => Exp.montgomery n (M.readLE xp (8 * n)) (M.readLE rrp (8 * n)) (M.readLE mp (8 * n))
        ((2 ^ 64 - t) % 2 ^ 64)) M' 1 →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he0
  have hk0 : (2 ^ 64 - t) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hng := neg_ofNat t ht
  -- buffer slices of `buf` (capacity 17n)
  have hB0 : Buf R L g sp n M bp (2 * n) := by
    refine ⟨Nat.le_refl _, by omega, M.accessible_sub hba (Or.inr rfl) (by omega) (by omega), by omega,
      hbh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)), ?_, ?_⟩
    · unfold Apart at hbw ⊢; omega
    · unfold Apart at hbg ⊢; omega
  have hB1 : Buf R L g sp n M (bp + 8 * n) (2 * n) := by
    refine ⟨Nat.le_refl _, by omega, M.accessible_sub hba (Or.inr rfl) (by omega) (by omega), by omega,
      hbh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)), ?_, ?_⟩
    · unfold Apart at hbw ⊢; omega
    · unfold Apart at hbg ⊢; omega
  have hA := MontW.sum impl hap R hclr hmv b L g sp n mp mc bp (2 * n) onep rrp ((2 ^ 64 - t) % 2 ^ 64)
    (BitVec.ofNat 64 n) (BitVec.ofNat 64 n) (BitVec.ofNat 64 rrc) (M.readLE (g + 16) 8)
    (mcall_ofC he hn hmc hmc' hB0 (OneIn.c he hone) (Inp.c hrr) hm (by unfold Apart at hbo ⊢; omega)
      (by unfold Apart at hbR ⊢; omega) (by unfold Apart at hbm ⊢; omega) (hok _)) hk0
  have hA1 := MontW.sum impl hap R hclr hmv b L g sp n mp mc (bp + 8 * n) (2 * n) xp rrp ((2 ^ 64 - t) % 2 ^ 64)
    (BitVec.ofNat 64 n) (BitVec.ofNat 64 xc) (BitVec.ofNat 64 rrc) (M.readLE (g + 16) 8)
    (mcall_ofC he hn hmc hmc' hB1 (Inp.c hx) (Inp.c hrr) hm (by unfold Apart at hbx ⊢; omega)
      (by unfold Apart at hbR ⊢; omega) (by unfold Apart at hbm ⊢; omega) (hok _)) hk0
  have hoa := (OneIn.c he hone).1
  have hra := hrr.1
  have hxa := hx.1
  have hma := hm.1
  have hB0a := hB0.2.2.1
  have hB1a := hB1.2.2.1
  janus_run [r728, r736, r744, r224, r128, r528, r544, r256, r264, r616, r328, r320, hng, fnBase'] until [1803452]
    calls [hP1 := hA]
  janus_run [r728, r736, r744, r224, r128, r528, r544, r256, r264, r616, r328, r320, hng, fnBase', slice1 bp n hn hn16 (by omega),
    sub_nn n hn16, sub_3n n hn16] until [powHead]
    calls [hP2 := hA1]
  rename_i v1 i1 F1 L1 hb0 a0 c1 c2 c3 c4 e0 e1 e2 v2 i2 F2 L2
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := p01post he hn hn16 ht hm hbb hbh hbw hbm hone hbo hrr hbR hx hbx
    v1 i1 F1 L1 hP1_regions v2 i2 F2 L2 hP2_regions
  refine K _ _ ?_ ?_ ?_ ?_ ?_ ?_ rfl q1 q2 q3 q4 q5 q6 q7 q8
  all_goals first | (janus_simp; done) | skip

end FvModexp.Arm64.W2Pro
