import FvModexp.Proofs.Arm64.Exp.W4Fin
import FvModexp.Proofs.Arm64.Exp.CallW

/-!
# window-4 (arm64), loop exit → join (nat.go:1478-1488)

`zz = zz.montgomery(z, one, m, k0, numWords)` (convert to regular number), then the final reduction
`if zz.cmp(m) >= 0 { zz = zz.sub(zz, m); if zz.cmp(m) >= 0 { _, zz = nat(nil).div(stk, nil, zz, m) } }`, up to the join
point `njoin` (the inline `zz.norm()`, `W4Fin.fin`). Continuation form; callee calls by hand (`CallW`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Loop

/-- the return address of the first `zz.cmp(m)` -/
abbrev cmp1Ret : Nat := 1801336
/-- `nat.cmp`'s entry (literal: the executor must not evaluate a name lookup in `until`) -/
abbrev cmpEntry : Nat := 1782608

theorem cmpEntry_eq : segAddr LibExp.program ExpHyp.fnCmp = cmpEntry := by decide

theorem fnBase : segAddr LibExp.program fn = 1798512 := by decide

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
/-- loop exit → entry of the first `zz.cmp(m)` (after `zz = zz.montgomery(z, one, …)`) -/
theorem exA (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y : Nat) (tbl pp pcap : Nat → Nat) {ext : List (Nat × Nat)} (M0 : Memory)
    (r18 r29 : BitVec 64) (onep : Nat)
    (hst : Static R L g sp n mp mc k0 yp ylen Y tbl pp pcap M0)
    (hone : Inp R L sp n M0 onep) (hone1 : M0.readLE onep (8 * n) = 1) (r816 : M0.readLE (sp + 816) 8 = onep)
    (S : State) (zp zc zzp zzc : Nat) (M : Memory)
    (hpc : S.pc = BitVec.ofNat 64 exit) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zzp)
    (h13 : S.regs 13 = BitVec.ofNat 64 n) (h14 : S.regs 14 = BitVec.ofNat 64 zc) (h15 : S.regs 15 = BitVec.ofNat 64 zzc)
    (h2 : S.regs 2 = BitVec.ofNat 64 n) (h3 : S.regs 3 = BitVec.ofNat 64 n) (h9 : S.regs 9 = BitVec.ofNat 64 mp)
    (h11 : S.regs 11 = BitVec.ofNat 64 mc) (h12 : S.regs 12 = BitVec.ofNat 64 k0)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (hB : Bufs R L g sp n mp yp ylen pp ext M0 zp zc zzp zzc) (hM : Mem R b L g sp M0 M zp zc zzp zzc)
    (hzo : Apart zp (8 * zc) onep (8 * n)) (hzzo : Apart zzp (8 * zzc) onep (8 * n))
    (KA : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 cmpEntry →
      S'.regs 30 = BitVec.ofNat 64 cmp1Ret → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 zzp → S'.regs 1 = BitVec.ofNat 64 n → S'.regs 2 = BitVec.ofNat 64 zzc →
      S'.regs 3 = BitVec.ofNat 64 mp → S'.regs 4 = BitVec.ofNat 64 n → S'.regs 5 = BitVec.ofNat 64 mc →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      Mem R b L g sp M0 M' zp zc zzp zzc →
      M'.readLE (sp + 400) 8 = zzp → M'.readLE (sp + 160) 8 = n → M'.readLE (sp + 168) 8 = zzc →
      M'.readLE zzp (8 * n) = Exp.montgomery n (M.readLE zp (8 * n)) 1 (M0.readLE mp (8 * n)) k0 →
      Reaches ((LibExp.program.link impl).withExit ret) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  obtain ⟨he, hn, hn16, hmc, hmc', hk0, hyl, hyl', hm, hy, hY, hpw, r1016, r1024, r1032, r224, r1000, r992, hok⟩ := hst
  obtain ⟨hF, hLF, hinv, hrg0⟩ := hM
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
  have he' : Env R L g sp M0 := ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩
  obtain ⟨hBz, hBzz, hzzz, hzm, hzzm, hzy, hzzy, hzp, hal8z, hal8zz, hstz, hstzz, hext⟩ := hB
  have hzI : Inp R L sp n M0 zp := ⟨M0.accessible_sub hBz.2.2.1 (Or.inr rfl) (Nat.le_refl _) (by omega),
    by omega, hBz.2.2.2.2.1.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega)),
    by have := hBz.2.2.2.2.2.1; unfold Apart at this ⊢; omega⟩
  have hA := MontW.sum impl hap R hclr hmv b L g sp n mp mc zzp zzc zp onep k0 (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 zc) (BitVec.ofNat 64 n) (M0.readLE (g + 16) 8)
    (mcall_of he' hn hmc hmc' hBzz hzI hone hm (by have := hzzz; unfold Apart at this ⊢; omega) hzzo hzzm (hok _)) hk0
  have hF0 := hF
  simp only [lw, fw, List.append_assoc, List.cons_append, List.nil_append] at hF
  have hgM : M.readLE (g + 16) 8 = M0.readLE (g + 16) 8 := by
    refine hF.readLE _ _ ?_
    have h1 := hgw; have h2 := hBz.2.2.2.2.2.2; have h3 := hBzz.2.2.2.2.2.2
    unfold Apart at h1 h2 h3
    simp only [outside_append, outside_cons, outside_nil, and_true, hgrt, true_and]
    omega
  have r816M : M.readLE (sp + 816) 8 = onep := by
    rw [← r816]; refine hF.readLE _ _ ?_
    have h1 := hwrt; have h2 := hBz.2.2.2.2.2.1; have h3 := hBzz.2.2.2.2.2.1
    unfold Apart at h2 h3
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h1.of_sub (by omega) (by omega), by omega⟩
  have r1016M : M.readLE (sp + 1016) 8 = mp := by
    rw [← r1016]; refine hF.readLE _ _ ?_
    have h1 := hwrt; have h2 := hBz.2.2.2.2.2.1; have h3 := hBzz.2.2.2.2.2.1
    unfold Apart at h2 h3
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h1.of_sub (by omega) (by omega), by omega⟩
  have r1024M : M.readLE (sp + 1024) 8 = n := by
    rw [← r1024]; refine hF.readLE _ _ ?_
    have h1 := hwrt; have h2 := hBz.2.2.2.2.2.1; have h3 := hBzz.2.2.2.2.2.1
    unfold Apart at h2 h3
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h1.of_sub (by omega) (by omega), by omega⟩
  have r1032M : M.readLE (sp + 1032) 8 = mc := by
    rw [← r1032]; refine hF.readLE _ _ ?_
    have h1 := hwrt; have h2 := hBz.2.2.2.2.2.1; have h3 := hBzz.2.2.2.2.2.1
    unfold Apart at h2 h3
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h1.of_sub (by omega) (by omega), by omega⟩
  obtain ⟨hma, hmb, hmh, hmw⟩ := hm
  obtain ⟨hoa, hob, hoh, how⟩ := hone
  obtain ⟨hzc1, hzc2, hza, hzb, hzh, hzw, hzg⟩ := hBz
  obtain ⟨hzzc1, hzzc2, hzza, hzzb, hzzh, hzzw, hzzg⟩ := hBzz
  janus_run [r816M, r1016M, r1024M, r1032M, fnBase] until [cmpEntry] calls [hP1 := hA]
  obtain ⟨_, _, _, _, v1, i1, F1, L1⟩ := hP1
  refine KA _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mem ?_ ?_ ?_ ?val
  all_goals first | (janus_simp; done) | skip
  case mem =>
    dsimp only
    have fc1 : FL R L sp zp zc zzp zzc M0 s'.mem := FL.call ⟨hF0, hLF⟩ F1 L1 (Or.inr ⟨rfl, rfl⟩)
    have fc2 : FL R L sp zp zc zzp zzc M0 (((s'.mem.writeLE (sp + 400) 8 zzp).writeLE (sp + 160) 8 n).writeLE
        (sp + 168) 8 zzc) := by
      repeat (first | exact fc1 | refine FL.write ?_ hLs _ (by omega))
    have w := hwrt
    refine ⟨fc2.1, fc2.2, ?_, ?_⟩
    · repeat (first | exact i1 | refine FvModexp.Expmc.inv_writeLE (Or.inr (w.of_sub (by omega) (by omega))) ?_)
    · simp only [Memory.regions_writeLE, hP1_regions]
      first | exact hrg0 | (subst hmem; exact hrg0)
  case val =>
    dsimp only
    have u1 := hzzw
    unfold Apart at u1
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [v1, FL.read ⟨hF0, hLF⟩ hoh how hsp1 hzo hzzo, hone1, FL.read ⟨hF0, hLF⟩ hmh hmw hsp1 hzm hzzm]

end FvModexp.Arm64.W4Loop
