import FvModexp.Proofs.Arm64.Nat.BasicSqrStep
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

/-!
# `basicSqr` (arm64): after the loop (`i = n`, natmul.go:131-133)

`t[2n-1] = lshVU(t[1:2n-1], t[1:2n-1], 1)` (`lshVU.abi0`), `addVV(z, z, t)` (`addVV.abi0`), the deferred
`stk.restore(…)` (an indirect `CALL (R0)` of the closure `basicSqr.deferwrap1`, `Restore.sum`), the epilogue.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees

namespace FvModexp.Arm64.BasicSqr

abbrev retLsh : Nat := segAddr Extracted.program fn + 0x21c
abbrev retVV : Nat := segAddr Extracted.program fn + 0x260

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
theorem fin1 (impl : List Segment) (R : RtInv)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1) (Q : State → Prop)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 head) (hsp : S.sp = s.sp - 208#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 216#64) (h18 : S.regs 18 = s.regs 18) (r0 : S.regs 0 = BitVec.ofNat 64 t)
    (r2 : S.regs 2 = BitVec.ofNat 64 (2 * xl.toNat)) (r3 : S.regs 3 = xl) (r6 : S.regs 6 = xl)
    (hI : Inv R L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat xc.toNat s t L1 b1 w1 c1 xl.toNat S.mem) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) S Q := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have ht48 := hl.t48
  have hbig := hE.big
  have hpre := hE.pre
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, -, -⟩ := hce
  have hscr := hE.scr
  have hI' := hI
  obtain ⟨hM, -, -, -⟩ := hI'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf, minv⟩ := hM
  have htacc : s.mem.accessible (t + 8) (8 * (2 * xl.toNat - 2)) true = true :=
    Memory.accessible_mono _ hscr.acc (by omega) (by omega)
  have htacc' := Memory.accessible_weaken _ htacc
  have htH : Held R L1 (t + 8) (8 * (2 * xl.toNat - 2)) := hscr.held.sub (by omega) (by omega)
  have hro : Outside (s.sp.toNat - 208 + 64) 8 R.rt := hout.of_sub (by omega) (by omega)
  have htg : Apart (t + 8) (8 * (2 * xl.toNat - 2)) ((s.regs 28).toNat + 16) 8 := by
    rcases hscr.loc with ⟨h0, h1, h2⟩ | ⟨hin, -⟩
    · have := (hpre.starr h0).2; unfold Apart at this ⊢; have := hpre.stok.2.2.2.2.2.1; omega
    · have := (hin.apart hgr).symm; unfold Apart at this ⊢; omega
  have hrg : Apart (s.sp.toNat - 208 + 64) 8 ((s.regs 28).toNat + 16) 8 := by unfold Apart at hga ⊢; omega
  have htr : Apart (t + 8) (8 * (2 * xl.toNat - 2)) (s.sp.toNat - 208 + 64) 8 := by
    unfold Apart; have := hl.tw; omega
  have hneg : (0#64 - (BitVec.ofNat 64 (2 * xl.toNat) - 1#64)).getLsbD 63 = true := by
    apply getLsbD63_true
    have e : (BitVec.ofNat 64 (2 * xl.toNat) - 1#64).toNat = 2 * xl.toNat - 1 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simp only [BitVec.toNat_sub, e, BitVec.toNat_ofNat]; omega
  clear hpre hscr
  janus_run [hneg, and8_or, and8_or', m3, m4, m5, m6, toInt_small xl (by omega), toInt_small (BitVec.ofNat 64 xl.toNat) (by simp; omega)]
    until [retLsh] calls [hLsh b1 L1]
  trace_state
  all_goals sorry

end FvModexp.Arm64.BasicSqr
