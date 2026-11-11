import FvModexp.Proofs.Arm64.Exp.W4Defs

/-!
# window-4 main loop (arm64), part 2: return of the 2nd squaring → loop test (nat.go:1455-1461, 1446)

The 3rd and 4th squarings, `zz = zz.montgomery(z, powers[yi>>60], …)`, `z, zz = zz, z`, `yi <<= 4`, `k--`, back to the
test `TBZ $63, R21`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Loop

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
theorem body2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y : Nat) (tbl pp pcap : Nat → Nat) (M0 : Memory)
    (r18 r29 : BitVec 64)
    (hst : Static R L g sp n mp mc k0 yp ylen Y tbl pp pcap M0)
    (S : State) (i c yi zp zc zzp zzc : Nat) (M : Memory) (hc : c < 16) (hyi : yi < 2 ^ 64)
    (hpc : S.pc = BitVec.ofNat 64 mid) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 n) (h2 : S.regs 2 = BitVec.ofNat 64 zc)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (hB : Bufs R L g sp n mp yp ylen pp M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 M zp zc zzp zzc)
    (r400 : M.readLE (sp + 400) 8 = zzp) (r160 : M.readLE (sp + 160) 8 = n) (r168 : M.readLE (sp + 168) 8 = zzc)
    (r184 : M.readLE (sp + 184) 8 = yi) (r232 : M.readLE (sp + 232) 8 = c) (r240 : M.readLE (sp + 240) 8 = i)
    (K : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 test → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 zzp → S'.regs 13 = BitVec.ofNat 64 n → S'.regs 14 = BitVec.ofNat 64 zzc →
      S'.regs 1 = BitVec.ofNat 64 zp → S'.regs 3 = BitVec.ofNat 64 n → S'.regs 15 = BitVec.ofNat 64 zc →
      S'.regs 2 = BitVec.ofNat 64 n → S'.regs 9 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 mc →
      S'.regs 12 = BitVec.ofNat 64 k0 → S'.regs 16 = BitVec.ofNat 64 ylen → S'.regs 17 = BitVec.ofNat 64 i →
      S'.regs 19 = BitVec.ofNat 64 yp → S'.regs 20 = BitVec.ofNat 64 ((yi * 2 ^ 4) % 2 ^ 64) →
      S'.regs 21 = BitVec.ofNat 64 c - 1#64 →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      Mem R b L g sp M0 M' zzp zzc zp zc → M'.readLE (sp + 240) 8 = i →
      M'.readLE zzp (8 * n) = Exp.montgomery n (sq n (M0.readLE mp (8 * n)) k0 (sq n (M0.readLE mp (8 * n)) k0
        (M.readLE zp (8 * n)))) (tbl (yi / 2 ^ 60)) (M0.readLE mp (8 * n)) k0 →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  obtain ⟨he, hn, hn16, hmc, hmc', hk0, hyl, hyl', hm, hy, hY, hpw, r1016, r1024, r1032, r224, r1000, r992, hok⟩ := hst
  have hd : yi / 2 ^ 60 < 16 := by omega
  obtain ⟨hpi, hpv, hpc', rp0, rp1, rp2⟩ := hpw _ hd
  obtain ⟨hF, hLF, hinv⟩ := hM
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
  have he' : Env R L g sp M0 := ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩
  obtain ⟨hBz, hBzz, hzzz, hzm, hzzm, hzy, hzzy, hzp⟩ := hB
  obtain ⟨hzp1, hzzp1⟩ := hzp _ hd
  have hBzz' := hBzz
  have hm' := hm
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
  have hF0 := hF
  simp only [lw, fw, List.append_assoc, List.cons_append, List.nil_append] at hF
  have hgM : M.readLE (g + 16) 8 = M0.readLE (g + 16) 8 := by
    refine hF.readLE _ _ ?_
    have h1 := hgw; have h2 := hBz.2.2.2.2.2.2; have h3 := hBzz.2.2.2.2.2.2
    unfold Apart at h1 h2 h3
    simp only [outside_append, outside_cons, outside_nil, and_true, hgrt, true_and]
    omega
  obtain ⟨hma, hmb, hmh, hmw⟩ := hm
  have hC := MontW.sum impl hap R hclr hmv b L g sp n mp mc zzp zzc zp (pp (yi / 2 ^ 60)) k0 (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 (pcap (yi / 2 ^ 60))) (M0.readLE (g + 16) 8)
    (mcall_of he' hn hmc hmc' hBzz' hzI hpi hm' (by have := hzzz; unfold Apart at this ⊢; omega) hzzp1 hzzm (hok _)) hk0
  obtain ⟨hpa, hpb, hph, hpw'⟩ := hpi
  obtain ⟨hzc1, hzc2, hza, hzb, hzh, hzw, hzg⟩ := hBz
  obtain ⟨hzzc1, hzzc2, hzza, hzzb, hzzh, hzzw, hzzg⟩ := hBzz
  janus_run [r1016, r1024, r1032, r224, r1000, r992, r240, r400, r160, r168, r184, r232]
    until [segAddr LibExp.program fn + 0x9bc] calls [hP3 := hA]
  janus_run [r1016, r1024, r1032, r224, r1000, r992, r240, r184, r232] until [segAddr LibExp.program fn + 0xa04]
    calls [hP4 := hBs]
  have hd' : yi / 1152921504606846976 < 16 := hd
  have e0 : sp + 432 + (8 * (yi / 1152921504606846976) + 2 * (8 * (yi / 1152921504606846976))) =
      sp + 432 + 24 * (yi / 2 ^ 60) := by
    rw [show (2 : Nat) ^ 60 = 1152921504606846976 from rfl]; omega
  have q0 : M0.readLE (sp + 432 + (8 * (yi / 1152921504606846976) + 2 * (8 * (yi / 1152921504606846976)))) 8 =
      pp (yi / 2 ^ 60) := by rw [e0]; exact rp0
  have q1 : M0.readLE (sp + 432 + (8 * (yi / 1152921504606846976) + 2 * (8 * (yi / 1152921504606846976))) + 8) 8 =
      n := by rw [e0, show sp + 432 + 24 * (yi / 2 ^ 60) + 8 = sp + 440 + 24 * (yi / 2 ^ 60) by omega]; exact rp1
  have q2 : M0.readLE (sp + 432 + (8 * (yi / 1152921504606846976) + 2 * (8 * (yi / 1152921504606846976))) + 16) 8 =
      pcap (yi / 2 ^ 60) := by
    rw [e0, show sp + 432 + 24 * (yi / 2 ^ 60) + 16 = sp + 448 + 24 * (yi / 2 ^ 60) by omega]; exact rp2
  clear e0
  janus_run [r1016, r1024, r1032, r224, r1000, r992, r240, r184, r232, rot60 yi hyi, q0, q1, q2] until [test]
    calls [hP5 := hC]
  obtain ⟨_, _, _, _, v3, i3, F3, L3⟩ := hP3
  obtain ⟨_, _, _, _, v4, i4, F4, L4⟩ := hP4
  obtain ⟨_, _, _, _, v5, i5, F5, L5⟩ := hP5
  refine K _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mem ?s240 ?val
  case mem =>
    have fc : FL R L sp zp zc zzp zzc M0 _ := FL.call ?_ F5 L5 (Or.inr ⟨rfl, rfl⟩)
    · exact ⟨fc.swap.1, fc.swap.2, i5⟩
    repeat (first | exact ⟨hF0, hLF⟩ | refine FL.write ?_ hLs _ (by omega) |
      refine FL.call ?_ F4 L4 (Or.inl ⟨rfl, rfl⟩) | refine FL.call ?_ F3 L3 (Or.inr ⟨rfl, rfl⟩))
  case s240 =>
    have u3 := hzzw; have u4 := hzw
    unfold Apart at u3 u4
    have t3 := FvModexp.Expmc.slot_read F3 hwrt (a := sp + 240) (k := 8) (by omega) (by omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega) (by simp only [outside_cons, outside_nil, and_true]; omega)
    have t4 := FvModexp.Expmc.slot_read F4 hwrt (a := sp + 240) (k := 8) (by omega) (by omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega) (by simp only [outside_cons, outside_nil, and_true]; omega)
    have t5 := FvModexp.Expmc.slot_read F5 hwrt (a := sp + 240) (k := 8) (by omega) (by omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega) (by simp only [outside_cons, outside_nil, and_true]; omega)
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, t3, t4, t5, r240]
  case val =>
    have u1 := hmw; have u2 := hzzm; have u3 := hzzw; have u4 := hzw; have u5 := hzm; have u6 := hpw'
    have u7 := hzp1; have u8 := hzzp1
    unfold Apart at u1 u2 u3 u4 u5 u6 u7 u8
    have a3m := FvModexp.Expmc.held_readLE hmh F3 L3 (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
    have a4m := FvModexp.Expmc.held_readLE hmh F4 L4 (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
    have a3p := FvModexp.Expmc.held_readLE hph F3 L3 (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
    have a4p := FvModexp.Expmc.held_readLE hph F4 L4 (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
    have bm := FL.read ⟨hF0, hLF⟩ hmh hmw hsp1 hzm hzzm
    have bp := FL.read ⟨hF0, hLF⟩ hph hpw' hsp1 hzp1 hzzp1
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, a3m, a4m, a3p, a4p, bm, bp, hpv] at v3 v4 v5
    rw [v5, v4, v3]
  all_goals first | rfl | (janus_simp; done) | (janus_simp [lsl4' yi]; done)

end FvModexp.Arm64.W4Loop
