import FvModexp.Proofs.Arm64.Exp.MontW
import FvModexp.Proofs.Common.ExpOdd
import FvModexp.Proofs.Common.ExpWindow
import FvModexp.Proofs.Common.ExpmcFrame
import FvModexp.Proofs.Common.ExpmcWin

/-!
# `expNNOddMontgomeryWindowSize4` (arm64): the main loop, nat.go:1450-1475

The inner loop (4 squarings + 1 multiplication by `powers[yi>>60]`, `z, zz = zz, z`, `yi <<= 4`, `k--`) and the outer step
(`if i == 0 {break}; i--; yi = y[i]; k = 15`) as ONE lemma by induction on `17·i + c` (`c = k + 1`) from the loop test
`TBZ $63, R21` (entry + 0xaa0) to the loop exit (entry + 0xab8), in continuation-passing form. The value is the model's
`outerLoop 4 step y 16 i yi c z` (ExpWindow.lean) with `step` = the window step of `expNNOddMont 4` (ExpOdd.lean).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Loop

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4"
/-- the loop test `TBZ $63, R21` -/
abbrev test : Nat := segAddr LibExp.program fn + 0xaa0
/-- the loop exit (after `if i == 0 { break }`): the final `zz.montgomery(z, one, …)` -/
abbrev exit : Nat := segAddr LibExp.program fn + 0xab8

/-- the window step of `expNNOddMont 4` (ExpOdd.lean) -/
abbrev step (n Mv k : Nat) (tbl : Nat → Nat) (z d : Nat) : Nat :=
  Exp.montgomery n (Exp.iter (fun z => Exp.montgomery n z z Mv k) 4 z) (tbl d) Mv k

/-- per-array facts of the two Montgomery buffers `z`, `zz` (writable, roomy, held, apart from the call windows) -/
@[reducible] def Buf (R : RtInv) (L : List (Nat × Nat)) (g sp n : Nat) (M0 : Memory) (p c : Nat) : Prop :=
  2 * n ≤ c ∧ c < 2 ^ 40 ∧ M0.accessible p (8 * c) true = true ∧ p + 8 * c ≤ 2 ^ 48 ∧
  (InRanges p (8 * c) L ∨ Outside p (8 * c) R.rt) ∧ Apart p (8 * c) (sp - 4288) (4288 + 1040) ∧
  Apart (g + 16) 8 p (8 * c)

/-- the frame ranges the loop writes (callee windows + spills), without the two buffers -/
@[reducible] def fw (sp : Nat) : List (Nat × Nat) :=
  [(sp - 4288, sp + 224), (sp + 232, sp + 432), (sp + 864, sp + 872), (sp + 904, sp + 912)]

/-- everything the loop may change since the anchor `M0` -/
@[reducible] def lw (R : RtInv) (sp zp zc zzp zzc : Nat) : List (Nat × Nat) :=
  R.rt ++ fw sp ++ [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)]

/-- a read-only input `p[0:n]` (readable, held, apart from the whole window `[sp-4288, sp+1040)`) -/
@[reducible] def Inp (R : RtInv) (L : List (Nat × Nat)) (sp n : Nat) (M0 : Memory) (p : Nat) : Prop :=
  M0.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧ (InRanges p (8 * n) L ∨ Outside p (8 * n) R.rt) ∧
  Apart p (8 * n) (sp - 4288) (4288 + 1040)

/-- the stack/guard environment of the loop at the anchor `M0` -/
@[reducible] def Env (R : RtInv) (L : List (Nat × Nat)) (g sp : Nat) (M0 : Memory) : Prop :=
  sp % 16 = 0 ∧ 4288 ≤ sp ∧ sp + 1040 ≤ 2 ^ 48 ∧ M0.accessible (sp - 4288) (4288 + 1040) true = true ∧
  g + 24 ≤ 2 ^ 48 ∧ M0.accessible (g + 16) 8 false = true ∧ M0.readLE (g + 16) 8 + 4288 < sp ∧
  Outside (sp - 4288) (4288 + 1040) R.rt ∧ Apart (g + 16) 8 (sp - 4288) (4288 + 1040) ∧ Outside (g + 16) 8 R.rt ∧
  LiveSep L [(sp - 4288, sp + 1040)]

theorem mcall_of {R : RtInv} {L : List (Nat × Nat)} {g sp n mp mc rp rc xp yp : Nat} {M0 : Memory}
    (he : Env R L g sp M0) (hn : 0 < n) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40) (hr : Buf R L g sp n M0 rp rc)
    (hx : Inp R L sp n M0 xp) (hy : Inp R L sp n M0 yp) (hm : Inp R L sp n M0 mp)
    (hrx : Apart rp (8 * rc) xp (8 * n)) (hry : Apart rp (8 * rc) yp (8 * n)) (hrm : Apart rp (8 * rc) mp (8 * n))
    (hok : R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
      R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n]) :
    MontW.MCall R L g (M0.readLE (g + 16) 8) sp n mp mc rp rc xp yp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := he
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hr
  have sub : ∀ p k, Apart p k (sp - 4288) (4288 + 1040) → Apart p k (sp - 4288) (4288 + 120) := by
    intro p k h; unfold Apart at h ⊢; omega
  refine ⟨h1, h2, by omega, h5, h7,
    h8.of_sub (Nat.le_refl _) (by omega), sub _ _ h9, h10, ?_, hn, r1, r2, hmc, hmc', r4, r5, sub _ _ r6, r7,
    ⟨hx.2.1, hx.2.2.1, sub _ _ hx.2.2.2⟩, ⟨hy.2.1, hy.2.2.1, sub _ _ hy.2.2.2⟩,
    ⟨hm.2.1, hm.2.2.1, sub _ _ hm.2.2.2⟩, hrx, hry, hrm, hok.1, hok.2⟩
  intro r hr
  have := h11 r hr
  simp only [outside_cons, outside_nil, and_true] at this ⊢
  omega

/-- `LSR $60` as the executor states it (rotate + mask) -/
theorem rot60 (yi : Nat) (h : yi < 2 ^ 64) :
    ((BitVec.ofNat 64 yi).rotateRight 60).toNat % 16 = yi / 1152921504606846976 := by
  rw [BitVec.toNat_rotateRight]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  rw [show (16 : Nat) = 2 ^ 4 by rfl, Nat.or_mod_two_pow, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h1 : yi * 2 ^ (64 - 60 % 64) % 2 ^ 64 % 2 ^ 4 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (by decide)]; simp [Nat.mul_mod_left]
  rw [h1, Nat.or_zero]
  have : yi / 2 ^ (60 % 64) < 2 ^ 4 := by simp; omega
  rw [Nat.mod_eq_of_lt this]

/-- the static facts of the loop (anchor memory `M0` = the memory at the first arrival at the test) -/
def Static (R : RtInv) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y : Nat) (tbl pp pcap : Nat → Nat)
    (M0 : Memory) : Prop :=
  Env R L g sp M0 ∧ 0 < n ∧ n ≤ 2 ^ 16 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧ k0 < 2 ^ 64 ∧ 0 < ylen ∧ ylen < 2 ^ 40 ∧
  Inp R L sp n M0 mp ∧ Inp R L sp ylen M0 yp ∧ M0.readLE yp (8 * ylen) = Y ∧
  (∀ d, d < 16 → Inp R L sp n M0 (pp d) ∧ M0.readLE (pp d) (8 * n) = tbl d ∧ pcap d < 2 ^ 64 ∧
    M0.readLE (sp + 432 + 24 * d) 8 = pp d ∧ M0.readLE (sp + 440 + 24 * d) 8 = n ∧
    M0.readLE (sp + 448 + 24 * d) 8 = pcap d) ∧
  M0.readLE (sp + 1016) 8 = mp ∧ M0.readLE (sp + 1024) 8 = n ∧ M0.readLE (sp + 1032) 8 = mc ∧
  M0.readLE (sp + 224) 8 = k0 ∧ M0.readLE (sp + 1000) 8 = ylen ∧ M0.readLE (sp + 992) 8 = yp ∧
  (∀ rp, R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
    R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n])

/-- the two buffers at a loop state -/
@[reducible] def Bufs (R : RtInv) (L : List (Nat × Nat)) (g sp n mp yp ylen : Nat) (pp : Nat → Nat) (M0 : Memory)
    (zp zc zzp zzc : Nat) : Prop :=
  Buf R L g sp n M0 zp zc ∧ Buf R L g sp n M0 zzp zzc ∧ Apart zp (8 * zc) zzp (8 * zzc) ∧
  Apart zp (8 * zc) mp (8 * n) ∧ Apart zzp (8 * zzc) mp (8 * n) ∧
  Apart zp (8 * zc) yp (8 * ylen) ∧ Apart zzp (8 * zzc) yp (8 * ylen) ∧
  (∀ d, d < 16 → Apart zp (8 * zc) (pp d) (8 * n) ∧ Apart zzp (8 * zzc) (pp d) (8 * n))

/-- the memory facts at a loop state `M` -/
@[reducible] def Mem (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp : Nat) (M0 M : Memory) (zp zc zzp zzc : Nat) :
    Prop :=
  MemFrame M0 M (lw R sp zp zc zzp zzc) ∧ LiveFrame M0 M L [(zp, zp + 8 * zc), (zzp, zzp + 8 * zzc)] ∧
  R.inv b L g (view R.rt L M)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
theorem loop (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibExp.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc k0 yp ylen Y : Nat) (tbl pp pcap : Nat → Nat) (M0 : Memory)
    (r18 r29 : BitVec 64) (V : Nat)
    (hst : Static R L g sp n mp mc k0 yp ylen Y tbl pp pcap M0)
    (hexit : ∀ (S : State) (zp zc zzp zzc : Nat) (M : Memory), S.pc = BitVec.ofNat 64 exit →
      S.sp = BitVec.ofNat 64 sp → S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 zzp →
      S.regs 13 = BitVec.ofNat 64 n → S.regs 14 = BitVec.ofNat 64 zc → S.regs 15 = BitVec.ofNat 64 zzc →
      S.regs 2 = BitVec.ofNat 64 n → S.regs 3 = BitVec.ofNat 64 n → S.regs 9 = BitVec.ofNat 64 mp →
      S.regs 11 = BitVec.ofNat 64 mc → S.regs 12 = BitVec.ofNat 64 k0 →
      S.regs 18 = r18 → S.regs 28 = BitVec.ofNat 64 g → S.regs 29 = r29 → S.mem = M →
      Bufs R L g sp n mp yp ylen pp M0 zp zc zzp zzc → Mem R b L g sp M0 M zp zc zzp zzc →
      M.readLE zp (8 * n) = V → Reaches ((LibExp.program.link impl).withExit ret) S Q) :
    ∀ (f : Nat) (S : State) (i c yi zp zc zzp zzc : Nat) (M : Memory), f = 17 * i + c → c ≤ 16 → i < ylen →
      yi < 2 ^ 64 → S.pc = BitVec.ofNat 64 test → S.sp = BitVec.ofNat 64 sp →
      S.regs 0 = BitVec.ofNat 64 zp → S.regs 13 = BitVec.ofNat 64 n → S.regs 14 = BitVec.ofNat 64 zc →
      S.regs 1 = BitVec.ofNat 64 zzp → S.regs 3 = BitVec.ofNat 64 n → S.regs 15 = BitVec.ofNat 64 zzc →
      S.regs 2 = BitVec.ofNat 64 n → S.regs 9 = BitVec.ofNat 64 mp → S.regs 11 = BitVec.ofNat 64 mc →
      S.regs 12 = BitVec.ofNat 64 k0 → S.regs 16 = BitVec.ofNat 64 ylen → S.regs 17 = BitVec.ofNat 64 i →
      S.regs 19 = BitVec.ofNat 64 yp → S.regs 20 = BitVec.ofNat 64 yi → S.regs 21 = BitVec.ofNat 64 c - 1#64 →
      S.regs 18 = r18 → S.regs 28 = BitVec.ofNat 64 g → S.regs 29 = r29 → S.mem = M →
      Bufs R L g sp n mp yp ylen pp M0 zp zc zzp zzc → Mem R b L g sp M0 M zp zc zzp zzc →
      M.readLE (sp + 240) 8 = i →
      Exp.outerLoop 4 (step n (M0.readLE mp (8 * n)) k0 tbl) Y 16 i yi c (M.readLE zp (8 * n)) = V →
      Reaches ((LibExp.program.link impl).withExit ret) S Q := by
  obtain ⟨he, hn, hn16, hmc, hmc', hk0, hyl, hyl', hm, hy, hY, hpw, r1016, r1024, r1032, r224, r1000, r992, hok⟩ := hst
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
  intro S i c yi zp zc zzp zzc M hf hc hi hyi hpc hsp h0 h13 h14 h1 h3 h15 h2 h9 h11 h12 h16 h17 h19 h20 h21
    h18 h28 h29 hmem hB hM r240 hV
  rcases c with _ | c
  · sorry
  · -- the inner-loop body: 4 squarings, the multiplication by `powers[yi >> 60]`, the swap
    have hd : yi / 2 ^ 60 < 16 := by omega
    obtain ⟨hpi, hpv, hpc', rp0, rp1, rp2⟩ := hpw _ hd
    have e21 : BitVec.ofNat 64 (c + 1) - 1#64 = BitVec.ofNat 64 c := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e21] at h21
    have h63 : (BitVec.ofNat 64 c).getLsbD 63 = false := by
      simp only [BitVec.getLsbD_ofNat]; simp [Nat.testBit, Nat.shiftRight_eq_div_pow]; omega
    obtain ⟨hF, hLF, hinv⟩ := hM
    obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩ := he
    have he' : Env R L g sp M0 := ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs⟩
    obtain ⟨hBz, hBzz, hzzz, hzm, hzzm, hzy, hzzy, hzp⟩ := hB
    obtain ⟨hzp1, hzzp1⟩ := hzp _ hd
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
    have hC := MontW.sum impl hap R hclr hmv b L g sp n mp mc zzp zzc zp (pp (yi / 2 ^ 60)) k0 (BitVec.ofNat 64 n)
      (BitVec.ofNat 64 zc) (BitVec.ofNat 64 (pcap (yi / 2 ^ 60))) (M0.readLE (g + 16) 8)
      (mcall_of he' hn hmc hmc' hBzz hzI hpi hm (by have := hzzz; unfold Apart at this ⊢; omega) hzzp1 hzzm (hok _)) hk0
    simp only [lw, fw, List.append_assoc, List.cons_append, List.nil_append] at hF
    have hgM : M.readLE (g + 16) 8 = M0.readLE (g + 16) 8 := by
      refine hF.readLE _ _ ?_
      have h1 := hgw; have h2 := hBz.2.2.2.2.2.2; have h3 := hBzz.2.2.2.2.2.2
      unfold Apart at h1 h2 h3
      simp only [outside_append, outside_cons, outside_nil, and_true, hgrt, true_and]
      omega
    obtain ⟨hma, -, -, -⟩ := hm
    obtain ⟨hpa, -, -, -⟩ := hpi
    obtain ⟨hzc1, hzc2, hza, hzb, hzh, hzw, hzg⟩ := hBz
    obtain ⟨hzzc1, hzzc2, hzza, hzzb, hzzh, hzzw, hzzg⟩ := hBzz
    janus_run [r1016, r1024, r1032, r224, r1000, r992, r240, h63] until [segAddr LibExp.program fn + 0x92c]
      calls [hP1 := hA]
    janus_run [r1016, r1024, r1032, r224, r1000, r992, r240] until [segAddr LibExp.program fn + 0x974]
      calls [hP2 := hBs]
    janus_run [r1016, r1024, r1032, r224, r1000, r992, r240] until [segAddr LibExp.program fn + 0x9bc]
      calls [hP3 := hA]
    janus_run [r1016, r1024, r1032, r224, r1000, r992, r240] until [segAddr LibExp.program fn + 0xa04]
      calls [hP4 := hBs]
    have hd' : yi / 1152921504606846976 < 16 := hd
    have q0 : M0.readLE (sp + 432 + (8 * (yi / 1152921504606846976) + 2 * (8 * (yi / 1152921504606846976)))) 8 =
        pp (yi / 2 ^ 60) := by rw [← rp0]; congr 1; omega
    have q1 : M0.readLE (sp + 432 + (8 * (yi / 1152921504606846976) + 2 * (8 * (yi / 1152921504606846976))) + 8) 8 =
        n := by rw [← rp1]; congr 1; omega
    have q2 : M0.readLE (sp + 432 + (8 * (yi / 1152921504606846976) + 2 * (8 * (yi / 1152921504606846976))) + 16) 8 =
        pcap (yi / 2 ^ 60) := by rw [← rp2]; congr 1; omega
    janus_run [r1016, r1024, r1032, r224, r1000, r992, r240, rot60 yi hyi, q0, q1, q2] until [test]
      calls [hP5 := hC]
    sorry

end FvModexp.Arm64.W4Loop
