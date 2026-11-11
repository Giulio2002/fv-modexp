import FvModexp.Proofs.Arm64.Exp.W4Defs

/-!
# window-4 main loop (arm64), part 1: loop test → return of the 2nd squaring (nat.go:1446, 1453-1454)

From the test `TBZ $63, R21` with `k = c ≥ 0`: the stores of `z`, `k`, `yi` to their spill slots, the squarings
`zz = zz.montgomery(z, z, …)` and `z = z.montgomery(zz, zz, …)`, up to the return of the second (`mid`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Loop

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
theorem body1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y : Nat) (tbl pp pcap : Nat → Nat) (M0 : Memory)
    (r18 r29 : BitVec 64)
    (hst : Static R L g sp n mp mc k0 yp ylen Y tbl pp pcap M0)
    (S : State) (i c yi zp zc zzp zzc : Nat) (M : Memory) (hc : c < 16) (hyi : yi < 2 ^ 64)
    (hpc : S.pc = BitVec.ofNat 64 test) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h13 : S.regs 13 = BitVec.ofNat 64 n) (h14 : S.regs 14 = BitVec.ofNat 64 zc)
    (h1 : S.regs 1 = BitVec.ofNat 64 zzp) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h15 : S.regs 15 = BitVec.ofNat 64 zzc)
    (h2 : S.regs 2 = BitVec.ofNat 64 n) (h20 : S.regs 20 = BitVec.ofNat 64 yi) (h21 : S.regs 21 = BitVec.ofNat 64 c)
    (h9 : S.regs 9 = BitVec.ofNat 64 mp) (h11 : S.regs 11 = BitVec.ofNat 64 mc) (h12 : S.regs 12 = BitVec.ofNat 64 k0)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (hB : Bufs R L g sp n mp yp ylen pp M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 M zp zc zzp zzc)
    (r240 : M.readLE (sp + 240) 8 = i)
    (K : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 mid → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 1 = BitVec.ofNat 64 n → S'.regs 2 = BitVec.ofNat 64 zc →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      Mem R b L g sp M0 M' zp zc zzp zzc →
      M'.readLE (sp + 400) 8 = zzp → M'.readLE (sp + 160) 8 = n → M'.readLE (sp + 168) 8 = zzc →
      M'.readLE (sp + 184) 8 = yi → M'.readLE (sp + 232) 8 = c → M'.readLE (sp + 240) 8 = i →
      M'.readLE zp (8 * n) = sq n (M0.readLE mp (8 * n)) k0 (sq n (M0.readLE mp (8 * n)) k0 (M.readLE zp (8 * n))) →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  obtain ⟨he, hn, hn16, hmc, hmc', hk0, hyl, hyl', hm, hy, hY, hpw, r1016, r1024, r1032, r224, r1000, r992, hok⟩ := hst
  have h63 : (BitVec.ofNat 64 c).getLsbD 63 = false := by
    simp only [BitVec.getLsbD_ofNat]; simp [Nat.testBit, Nat.shiftRight_eq_div_pow]; omega
  obtain ⟨hF, hLF, hinv⟩ := hM
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
  have he' : Env R L g sp M0 := ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩
  obtain ⟨hBz, hBzz, hzzz, hzm, hzzm, hzy, hzzy, hzp⟩ := hB
  have hzI : Inp R L sp n M0 zp := ⟨M0.accessible_sub hBz.2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega),
    by omega, hBz.2.2.2.2.1.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega)),
    by have := hBz.2.2.2.2.2.1; unfold Apart at this ⊢; omega⟩
  have hzzI : Inp R L sp n M0 zzp := ⟨M0.accessible_sub hBzz.2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega),
    by omega, hBzz.2.2.2.2.1.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega)),
    by have := hBzz.2.2.2.2.2.1; unfold Apart at this ⊢; omega⟩
  have hA := MontW.sum impl hap R hclr hmv b L g sp n mp mc zzp zzc zp zp k0 (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 zc) (M0.readLE (g + 16) 8)
    (mcall_of he' hn hmc hmc' hBzz hzI hzI hm (by have := hzzz; unfold Apart at this ⊢; omega)
      (by have := hzzz; unfold Apart at this ⊢; omega) hzzm (hok _)) hk0
  have hBs := MontW.sum impl hap R hclr hmv b L g sp n mp mc zp zc zzp zzp k0 (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 zzc) (BitVec.ofNat 64 zzc) (M0.readLE (g + 16) 8)
    (mcall_of he' hn hmc hmc' hBz hzzI hzzI hm (by have := hzzz; unfold Apart at this ⊢; omega)
      (by have := hzzz; unfold Apart at this ⊢; omega) hzm (hok _)) hk0
  have hF0 := hF
  simp only [lw, fw, List.append_assoc, List.cons_append, List.nil_append] at hF
  have hgM : M.readLE (g + 16) 8 = M0.readLE (g + 16) 8 := by
    refine hF.readLE _ _ ?_
    have h1 := hgw; have h2 := hBz.2.2.2.2.2.2; have h3 := hBzz.2.2.2.2.2.2
    unfold Apart at h1 h2 h3
    simp only [outside_append, outside_cons, outside_nil, and_true, hgrt, true_and]
    omega
  obtain ⟨hma, hmb, hmh, hmw⟩ := hm
  obtain ⟨hzc1, hzc2, hza, hzb, hzh, hzw, hzg⟩ := hBz
  obtain ⟨hzzc1, hzzc2, hzza, hzzb, hzzh, hzzw, hzzg⟩ := hBzz
  janus_run [r1016, r1024, r1032, r224, r1000, r992, r240, h63] until [segAddr LibExp.program fn + 0x92c]
    calls [hP1 := hA]
  janus_run [r1016, r1024, r1032, r224, r1000, r992, r240] until [mid]
    calls [hP2 := hBs]
  obtain ⟨_, _, _, _, v1, i1, F1, L1⟩ := hP1
  obtain ⟨_, _, _, _, v2, i2, F2, L2⟩ := hP2
  refine K _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mem ?_ ?_ ?_ ?_ ?_ ?_ ?val
  all_goals first | rfl | (janus_simp; done) | (janus_simp [r240]; done) | skip
  case mem =>
    have fc1 : FL R L sp zp zc zzp zzc M0 (((((M.writeLE (sp + 288) 8 zc).writeLE (sp + 280) 8 n).writeLE
        (sp + 864) 8 zp).writeLE (sp + 232) 8 c).writeLE (sp + 184) 8 yi) := by
      repeat (first | exact ⟨hF0, hLF⟩ | refine FL.write ?_ hLs _ (by omega))
    have fc3 : FL R L sp zp zc zzp zzc M0 s'.mem := by
      refine FL.call ?_ F2 L2 (Or.inl ⟨rfl, rfl⟩)
      repeat (first | exact fc1 | refine FL.write ?_ hLs _ (by omega) | refine FL.call ?_ F1 L1 (Or.inr ⟨rfl, rfl⟩))
    exact ⟨fc3.1, fc3.2, i2⟩
  case val =>
    have fc1 : FL R L sp zp zc zzp zzc M0 (((((M.writeLE (sp + 288) 8 zc).writeLE (sp + 280) 8 n).writeLE
        (sp + 864) 8 zp).writeLE (sp + 232) 8 c).writeLE (sp + 184) 8 yi) := by
      repeat (first | exact ⟨hF0, hLF⟩ | refine FL.write ?_ hLs _ (by omega))
    have em1 := FL.read fc1 hmh hmw hsp1 hzm hzzm
    have u1 := hmw; have u2 := hzzm; have u3 := hzzw; have u4 := hzw
    unfold Apart at u1 u2 u3 u4
    rw [em1] at v1
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint] at v2
    rw [FvModexp.Expmc.held_readLE hmh F1 L1 (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega), em1] at v2
    rw [v2, v1]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]

end FvModexp.Arm64.W4Loop
