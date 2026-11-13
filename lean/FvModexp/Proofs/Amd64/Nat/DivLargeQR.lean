import FvModexp.Proofs.Amd64.Nat.DivLargeQRel

set_option autoImplicit false

/-!
# `divLarge` (amd64): `alias(z, u)` (false) and `q = z.make(m + 1)` reusing `z` (`m + 1 ≤ cap z`), aliasPt → `joinQ`

`+0x452`: `R13 = cap z` (`RSP + 72`); `TESTQ R13` (`> 0`); `TESTQ SI = C` (`> 0`); `R15 = z.ptr` (`RSP + 56`); the last
elements' addresses differ (`z` apart from `u`'s array); `BX = m = [SP' + 0xb0]`, `R9 = m + 1`; `CMPQ R13, R9; JL`
not taken, `JAE joinQ`. Port of `Arm64/Nat/DivLargeQR.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivLarge

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem qR (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (c : Nat) (zp zc st up uc ip il vp vl : Nat) (s : State)
    (t w1 c1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (Lk : List (Nat × Nat)) (bk P C sh : Nat)
    (hE : Env R b L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) (S : State)
    (hS : AtAl R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh S) (hz : il - vl + 1 ≤ zc)
    (Q : State → Prop)
    (k : ∀ T, AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh zp zc T →
      ReachesRet (LibDivL.program.link impl) (retAddrOf s) T Q) :
    ReachesRet (LibDivL.program.link impl) (retAddrOf s) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hil9 := hl.il9; have hvil := hl.vil
  have hU := hS.ua
  have hcap := hU.cap; have hc40 := hU.c40; have hp48 := hU.p48
  have hz40 := hE.pre.zo.1
  have hz0 : 0 < zc := by omega
  have hz48 := ((hE.pre.zo.2.1 hz0).2.2.2)
  have hpz := hU.pz hz0
  unfold Apart at hpz
  have hne : zp + 8 * (zc - 1) ≠ P + 8 * (C - 1) := by omega
  have hM := hS.mem.mem
  have m1 := hM.s3; have m2 := hM.s1; have m3 := hM.mm
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -⟩ := hE.pre.ce
  simp only [regSP] at hb' ha hw
  have hwacc : S.mem.accessible ((s.regs 4).toNat - 41272) (41272 + 112) true = true := by
    rw [hM.fr.accessible]; exact hw
  have hpc := hS.pc; have hsp := hS.sp; have hr6 := hS.r6; have hr8 := hS.r8
  janus64_run [m1, m2, m3] until [joinQ]
  have hb2 := hS.bud2
  refine k _ ⟨rfl, ?sp, ?r5, ?r14, ?fs, ?x15, ?df, ?r0, ?r1, ?r2, ?r6, ?r7, ?r8, ?r9, ?r11, ?r12, ?r13, ?r15,
    hS.mem, hS.ua, qarr_reuse hE hS.ua hS.ext2 (fun a n w => hM.fr.accessible a n w) hz, hS.ext2, by omega, hS.sh63,
    hS.vval, hS.vtop, hS.uval, hS.reg⟩
  all_goals (try janus64_simp)
  all_goals first
    | exact hS.sp | exact hS.r5 | exact hS.r14 | exact hS.fs | exact hS.x15 | exact hS.df | exact hS.r0
    | exact hS.r1 | exact hS.r2 | exact hS.r6 | exact hS.r7 | exact hS.r8 | exact hS.r11 | exact hS.r12 | rfl

end FvModexp.Amd64.DivLarge
