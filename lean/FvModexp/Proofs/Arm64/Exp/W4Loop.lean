import FvModexp.Proofs.Arm64.Exp.W4Body1
import FvModexp.Proofs.Arm64.Exp.W4Body2

/-!
# `expNNOddMontgomeryWindowSize4` (arm64): the main loop, nat.go:1450-1475

The inner loop (4 squarings + 1 multiplication by `powers[yi>>60]`, `z, zz = zz, z`, `yi <<= 4`, `k--`: `W4Body1` +
`W4Body2`) and the outer step (`if i == 0 {break}; i--; yi = y[i]; k = 15`) as ONE lemma by induction on `17·i + c`
(`c = k + 1`) from the loop test `TBZ $63, R21` (entry + 0xaa0) to the loop exit (entry + 0xab8), in continuation-passing
form. The value is the model's `outerLoop 4 step y 16 i yi c z` (ExpWindow.lean) with `step` = the window step of
`expNNOddMont 4` (ExpOdd.lean).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Loop

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem loop (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y : Nat) (tbl pp pcap : Nat → Nat) {ext : List (Nat × Nat)} (M0 : Memory)
    (r18 r29 : BitVec 64) (V : Nat)
    (hst : Static R L g sp n mp mc k0 yp ylen Y tbl pp pcap M0)
    (hexit : ∀ (S : State) (zp zc zzp zzc : Nat) (M : Memory), S.pc = BitVec.ofNat 64 exit →
      S.sp = BitVec.ofNat 64 sp → S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 zzp →
      S.regs 13 = BitVec.ofNat 64 n → S.regs 14 = BitVec.ofNat 64 zc → S.regs 15 = BitVec.ofNat 64 zzc →
      S.regs 2 = BitVec.ofNat 64 n → S.regs 3 = BitVec.ofNat 64 n → S.regs 9 = BitVec.ofNat 64 mp →
      S.regs 11 = BitVec.ofNat 64 mc → S.regs 12 = BitVec.ofNat 64 k0 →
      S.regs 18 = r18 → S.regs 28 = BitVec.ofNat 64 g → S.regs 29 = r29 → S.mem = M →
      Bufs R L g sp n mp yp ylen pp ext M0 zp zc zzp zzc → Mem R b L g sp M0 M zp zc zzp zzc →
      M.readLE zp (8 * n) = V → Reaches ((LibExp.program.link impl).withExit ret) S Q) :
    ∀ (f : Nat) (S : State) (i c yi zp zc zzp zzc : Nat) (M : Memory), f = 17 * i + c → c ≤ 16 → i < ylen →
      yi < 2 ^ 64 → S.pc = BitVec.ofNat 64 test → S.sp = BitVec.ofNat 64 sp →
      S.regs 0 = BitVec.ofNat 64 zp → S.regs 13 = BitVec.ofNat 64 n → S.regs 14 = BitVec.ofNat 64 zc →
      S.regs 1 = BitVec.ofNat 64 zzp → S.regs 3 = BitVec.ofNat 64 n → S.regs 15 = BitVec.ofNat 64 zzc →
      S.regs 2 = BitVec.ofNat 64 n → S.regs 9 = BitVec.ofNat 64 mp → S.regs 11 = BitVec.ofNat 64 mc →
      S.regs 12 = BitVec.ofNat 64 k0 → S.regs 16 = BitVec.ofNat 64 ylen → S.regs 17 = BitVec.ofNat 64 i →
      S.regs 19 = BitVec.ofNat 64 yp → S.regs 20 = BitVec.ofNat 64 yi → S.regs 21 = BitVec.ofNat 64 c - 1#64 →
      S.regs 18 = r18 → S.regs 28 = BitVec.ofNat 64 g → S.regs 29 = r29 → S.mem = M →
      Bufs R L g sp n mp yp ylen pp ext M0 zp zc zzp zzc → Mem R b L g sp M0 M zp zc zzp zzc →
      M.readLE (sp + 240) 8 = i →
      Exp.outerLoop 4 (step n (M0.readLE mp (8 * n)) k0 tbl) Y 16 i yi c (M.readLE zp (8 * n)) = V →
      Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  have hst' := hst
  obtain ⟨he, hn, hn16, hmc, hmc', hk0, hyl, hyl', hm, hy, hY, hpw, r1016, r1024, r1032, r224, r1000, r992, hok⟩ := hst
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
  intro S i c yi zp zc zzp zzc M hf hc hi hyi hpc hsp h0 h13 h14 h1 h3 h15 h2 h9 h11 h12 h16 h17 h19 h20 h21
    h18 h28 h29 hmem hB hM r240 hV
  rcases c with _ | c
  · have h63 : (BitVec.ofNat 64 0 - 1#64).getLsbD 63 = true := by decide
    rcases i with _ | i
    · janus_run [h63] until [exit]
      refine hexit _ zp zc zzp zzc M ?_ rfl h0 h1 h13 h14 h15 h2 h3 h9 h11 h12 h18 h28 h29 rfl hB hM ?_
      · first | rfl | decide
      · rw [outer_done] at hV; exact hV
    · obtain ⟨hF, hLF, hinv, hrg0⟩ := hM
      obtain ⟨hya, hyb, hyh, hyw⟩ := hy
      obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
      janus_run [h63, r1016, r1024, r1032, r224, r1000, r992, r240] until [test]
      have hlt : M.readLE (yp + 8 * i) 8 < 2 ^ 64 := by
        have := FvModexp.Expmc.readLE_lt_B M (yp + 8 * i) 1
        rw [Nat.mul_one, Nat.pow_one, Exp.B_def] at this; exact this
      have sub1 : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
        apply BitVec.eq_of_toNat_eq; simp; omega
      have fw' : FL R L sp zp zc zzp zzc M0 (M.writeLE (sp + 240) 8 i) := FL.write ⟨hF, hLF⟩ hLs i (by omega)
      refine ih (17 * i + 16) (by omega) _ i 16 (M.readLE (yp + 8 * i) 8) zp zc zzp zzc (M.writeLE (sp + 240) 8 i)
        rfl (by omega) (by omega) hlt ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl hB
        ⟨fw'.1, fw'.2, FvModexp.Expmc.inv_writeLE (Or.inr (hwrt.of_sub (by omega) (by omega))) hinv,
          by rw [Memory.regions_writeLE]; exact hrg0⟩ ?r240 ?val
      case r240 =>
        rw [FvModexp.Expmc.readLE_writeLE_same rfl]; omega
      case val =>
        have hzy := hB.2.2.2.2.2.1; have hzzy := hB.2.2.2.2.2.2.1
        have hzc := hB.1.1; have hzzc := hB.2.1.1
        unfold Apart at hzy hzzy hyw
        have ey : M.readLE (yp + 8 * i) 8 = Exp.wd Y i := by
          rw [FL.read ⟨hF, hLF⟩ (hyh.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
            (by unfold Apart; omega) hsp1 (by unfold Apart; omega) (by unfold Apart; omega),
            FvModexp.Expmc.readLE_wd M0 yp i ylen (by omega), hY]
        have hBz := hB.1.2.2.2.2.2.1
        unfold Apart at hBz
        rw [ey, Memory.readLE_writeLE_of_disjoint (a := sp + 240) (n := 8) (b := zp) (k := 8 * n) (m := M) i (by omega)]
        rw [outer_zero] at hV; exact hV
      all_goals first | rfl | (janus_simp; done) | (janus_simp [sub1]; done) | decide
  · have e21 : BitVec.ofNat 64 (c + 1) - 1#64 = BitVec.ofNat 64 c := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e21] at h21
    refine body1 impl hap R hclr hmv ret hret Q b L g sp n mp mc k0 yp ylen Y tbl pp pcap M0 r18 r29 hst' S i c yi
      zp zc zzp zzc M (by omega) hyi hpc hsp h0 h13 h14 h1 h3 h15 h2 h20 h21 h9 h11 h12 h18 h28 h29 hmem hB hM r240 ?_
    intro S1 M1 p1 s1 a0 a1 a2 a18 a28 a29 m1 hM1 q400 q160 q168 q184 q232 q240 hv1
    refine body2 impl hap R hclr hmv ret hret Q b L g sp n mp mc k0 yp ylen Y tbl pp pcap M0 r18 r29 hst' S1 i c yi
      zp zc zzp zzc M1 (by omega) hyi p1 s1 a0 a1 a2 a18 a28 a29 m1 hB hM1 q400 q160 q168 q184 q232 q240 ?_
    intro S2 M2 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 hM2 w240 hv2
    rw [outer_succ] at hV
    refine ih (17 * i + c) (by omega) S2 i c ((yi * 2 ^ 4) % 2 ^ 64) zzp zzc zp zc M2 rfl (by omega) hi (by omega)
      b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 hB.swap hM2 w240 ?_
    rw [hv2, hv1, ← Exp.B_def]; exact hV

end FvModexp.Arm64.W4Loop
