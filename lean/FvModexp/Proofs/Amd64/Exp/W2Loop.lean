import FvModexp.Proofs.Amd64.Exp.W2S2
import FvModexp.Proofs.Amd64.Exp.W2S3

set_option autoImplicit false

/-!
# `expNNOddMontgomeryWindowSize2` (amd64): the main loop, nat.go:1579-1599 (agent expmc s60)

Twin of `Arm64.W2Loop.loop` / `Amd64.W4Loop.loop`. The inner loop body (segments `W2S1` … `W2S3`: 2 squarings + the
multiplication by `powers[yi >> 62]`, `yi <<= 2`, `k--`, the swap `z, zz = zz, z`) and the outer step (`if i == 0
{break}; i--; yi = y[i]; k = 31`) as ONE lemma by strong induction on `33·i + c` (`c = k + 1`, `R15 = c - 1`) from the
loop test `TESTQ R15, R15` (+0xf76) to the loop exit (+0xf97), continuation form. The value is the model's
`outerLoop 2 step y 32 i yi c z` (ExpWindow.lean) with `step` = the window step of `expNNOddMont 2` (ExpOdd.lean).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Loop

theorem m1_eq : BitVec.ofNat 64 0 - 1#64 = 18446744073709551615#64 := by decide

theorem sub1_succ (c : Nat) (_h : c + 1 < 2 ^ 64) : BitVec.ofNat 64 (c + 1) - 1#64 = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem loop {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {g fs sp n mp mc k0 yp ylen Y : Nat} {tbl pp pcap : Nat → Nat}
    {ext : List (Nat × Nat)} {M0 : Memory}
    (hst : Static R L g fs sp n mp mc k0 yp ylen Y tbl pp pcap M0) {ret : W64} {Q : State → Prop}
    (r5 : W64) (V : Nat) (Pz : Nat → Nat → Nat → Nat → Prop) (hPs : ∀ a b c d, Pz a b c d → Pz c d a b)
    (hexit : ∀ (S : State) (zp zc zzp zzc : Nat), S.rip = BitVec.ofNat 64 exit → S.regs 4 = BitVec.ofNat 64 sp →
      S.regs 5 = r5 → S.regs 14 = BitVec.ofNat 64 g → S.fsBase.toNat = fs → S.xmm 15 = 0 → S.df = false →
      S.regs 0 = BitVec.ofNat 64 zp → S.regs 2 = BitVec.ofNat 64 zc → S.regs 8 = BitVec.ofNat 64 zzp →
      S.regs 11 = BitVec.ofNat 64 n → S.regs 12 = BitVec.ofNat 64 zzc → S.regs 3 = BitVec.ofNat 64 mp →
      S.regs 6 = BitVec.ofNat 64 k0 → S.regs 10 = BitVec.ofNat 64 mc →
      Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc → Mem R b L g sp M0 S.mem zp zc zzp zzc →
      S.mem.readLE (sp + 0x148) 8 = n → S.mem.readLE zp (8 * n) = V → Pz zp zc zzp zzc →
      ReachesRet (LibW.program.link impl) ret S Q) :
    ∀ (f : Nat) (S : State) (i c yi zp zc zzp zzc : Nat), f = 33 * i + c → c ≤ 32 → i < ylen → yi < 2 ^ 64 →
      S.rip = BitVec.ofNat 64 test → S.regs 4 = BitVec.ofNat 64 sp → S.regs 5 = r5 →
      S.regs 14 = BitVec.ofNat 64 g → S.fsBase.toNat = fs → S.xmm 15 = 0 → S.df = false →
      S.regs 0 = BitVec.ofNat 64 zp → S.regs 2 = BitVec.ofNat 64 zc → S.regs 8 = BitVec.ofNat 64 zzp →
      S.regs 11 = BitVec.ofNat 64 n → S.regs 12 = BitVec.ofNat 64 zzc → S.regs 3 = BitVec.ofNat 64 mp →
      S.regs 6 = BitVec.ofNat 64 k0 → S.regs 10 = BitVec.ofNat 64 mc → S.regs 9 = BitVec.ofNat 64 yi →
      S.regs 15 = BitVec.ofNat 64 c - 1#64 → S.regs 7 = BitVec.ofNat 64 yp → S.regs 13 = BitVec.ofNat 64 ylen →
      S.regs 1 = BitVec.ofNat 64 i →
      Bufs R L g fs sp n mp yp ylen pp ext M0 zp zc zzp zzc → Mem R b L g sp M0 S.mem zp zc zzp zzc →
      S.mem.readLE (sp + 0x148) 8 = n → S.mem.readLE (sp + 0xe8) 8 = i →
      Exp.outerLoop 2 (step n (M0.readLE mp (8 * n)) k0 tbl) Y 32 i yi c (S.mem.readLE zp (8 * n)) = V →
      Pz zp zc zzp zzc → ReachesRet (LibW.program.link impl) ret S Q := by
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
  intro S i c yi zp zc zzp zzc hf hc hi hyi hpc hsp h5 h14 hfs hx15 hdf h0 h2 h8 h11 h12 h3 h6 h10 h9 h15 h7 h13 h1
    hB hM r140 re8 hV hPz
  have he := hst.1
  have hsp1 : 4296 ≤ sp := he.2.1; have hsp2 : sp + 0x2a8 ≤ 2 ^ 48 := he.2.2.1
  have hyl' := hst.2.2.2.2.2.2.2.2.1
  rcases c with _ | c
  · rw [m1_eq] at h15
    have hm1 : (18446744073709551615#64 : BitVec 64).msb = true := by decide
    rcases i with _ | i
    · janus64_run [hm1, BitVec.msb_eq_decide] until [exit]
      refine hexit _ zp zc zzp zzc ?_ hsp h5 h14 hfs hx15 rfl h0 h2 h8 h11 h12 h3 h6 h10 hB hM r140 ?_ hPz
      · rw [show exit = 6214551 by simp only [exit, fnE_eq]]
      · rw [outer_done] at hV; exact hV
    · have hy := hst.2.2.2.2.2.2.2.2.2.1
      have hY := hst.2.2.2.2.2.2.2.2.2.2.1
      have hacc : S.mem.accessible (sp - 4296) (4296 + 0x2a8) true = true := by
        rw [hM.1.1.accessible]; exact he.2.2.2.1
      have hyacc : S.mem.accessible yp (8 * ylen) false = true := by rw [hM.1.1.accessible]; exact hy.1
      have hyp : yp + 8 * ylen ≤ 2 ^ 48 := hy.2.1
      have ey : S.mem.readLE (yp + 8 * i) 8 = Exp.wd Y i := by
        have hzy := hB.2.2.2.2.2.1; have hzzy := hB.2.2.2.2.2.2.1
        have hzc := hB.1.1; have hzzc := hB.2.1.1; have hyw := hy.2.2.2
        unfold Apart at hzy hzzy hyw
        rw [FL.read hM.1 (hy.2.2.1.imp (fun h => h.sub (by omega) (by omega)) (fun h => h.of_sub (by omega) (by omega)))
          (by unfold Apart; omega) hsp1 (by unfold Apart; omega) (by unfold Apart; omega),
          FvModexp.Expmc.readLE_wd M0 yp i ylen (by omega), hY]
      have hwd : Exp.wd Y i < 2 ^ 64 := by
        have := FvModexp.Expmc.readLE_lt_B S.mem (yp + 8 * i) 1
        rw [Nat.mul_one, Nat.pow_one, Exp.B_def, ey] at this; exact this
      janus64_run [hm1, ey, BitVec.msb_eq_decide] until [test]
      have hM' := Mem.wr hM he i (a := sp + 0xe8) (by omega)
      refine ih (33 * i + 32) (by omega) _ i 32 (Exp.wd Y i) zp zc zzp zzc rfl (by omega) (by omega) hwd ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hB hM' ?_ ?_ ?_ hPz
      · rw [show test = 6214518 by simp only [test, fnE_eq]]
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hsp
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h5
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
      · exact hfs
      · exact hx15
      · rfl
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h0
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h2
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h8
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h11
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h12
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h3
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h6
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h10
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
        rw [show yp + (i + 1) * 8 - 8 = yp + 8 * i by omega, ey]
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; decide
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h7
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h13
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact sub1_succ i (by omega)
      · show (Arm64.Memory.writeLE S.mem (sp + 232) 8 i).readLE (sp + 328) 8 = n
        rdw; exact r140
      · show (Arm64.Memory.writeLE S.mem (sp + 232) 8 i).readLE (sp + 232) 8 = i
        rdw
      · show Exp.outerLoop 2 (step n (M0.readLE mp (8 * n)) k0 tbl) Y 32 i (Exp.wd Y i) 32
          ((Arm64.Memory.writeLE S.mem (sp + 232) 8 i).readLE zp (8 * n)) = V
        have u1 := hB.1.2.2.2.2.2.1; have u0 := hB.1.1; unfold Apart at u1
        simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint]; rw [outer_zero] at hV; exact hV
  · rw [sub1_succ c (by omega)] at h15
    refine seg1 hap hclr hmv hst S c yi zp zc zzp zzc (by omega) hyi hpc hsp h0 h2 h8 h11 h12 h3 h6 h10 h9 h15 h14 hfs
      hx15 hdf hB hM r140 ?_
    intro s1 p1 q4 q5 q14 qfs qx qdf a0 a3 a1 hM1 w110 w358 we0 wb0 w140 we8 vz1 vzz1
    refine seg2 hap hclr hmv hst s1 zp zc zzp zzc p1 q4 a0 a3 a1 q14 (by rw [qfs]; exact hfs) qx qdf hB hM1 w358 w140
      w110 ?_
    intro s2 p2 t4 t5 t14 tfs tx tdf b0 b3 b1 hM2 u188 u98 ua0 kp2 vzz2 vz2
    have eb0 : s2.mem.readLE (sp + 0xb0) 8 = yi := by
      rw [kp2 _ (by omega) (by omega) (by omega)]; exact wb0
    have ee0 : s2.mem.readLE (sp + 0xe0) 8 = c := by
      rw [kp2 _ (by omega) (by omega) (by omega)]; exact we0
    have ee8 : s2.mem.readLE (sp + 0xe8) 8 = i := by
      rw [kp2 _ (by omega) (by omega) (by omega), we8]; exact re8
    refine seg3 hap hclr hmv hst s2 i c yi zp zc zzp zzc (by omega) hyi p2 t4 b0 b3 b1 t14
      (by rw [tfs, qfs]; exact hfs) tx tdf hB hM2 u188 u98 ua0 eb0 ee0 ee8 ?_
    intro s5 p5 n4 n5 n14 nfs nx ndf e0 e2 e8 e11 e12 e3 e6 e10 e9 e15 e7 e13 e1 hM5 z140 ze8 vz5 vzz5
    rw [outer_succ] at hV
    refine ih (33 * i + c) (by omega) s5 i c ((yi * 2 ^ 2) % 2 ^ 64) zzp zzc zp zc rfl (by omega) hi (by omega)
      p5 n4 (by rw [n5, t5, q5, h5]) n14 (by rw [nfs, tfs, qfs]; exact hfs) nx ndf e0 e2 e8 e11
      e12 e3 e6 e10 e9 e15 e7 e13 e1 hB.swap hM5 z140 ze8 ?_ (hPs _ _ _ _ hPz)
    rw [vzz5, vz2, vzz1, ← Exp.B_def]
    exact hV

end FvModexp.Amd64.W2Loop
