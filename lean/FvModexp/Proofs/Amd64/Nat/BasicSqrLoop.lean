import FvModexp.Proofs.Amd64.Nat.BasicSqrBody
import FvModexp.Proofs.Common.DivmcBits
import FvModexp.Proofs.Common.BitLemmas

/-!
# `basicSqr` (amd64): the loop `for i := 1; i < n; i++` (natmul.go:124-130)

One iteration from the head `+0x1c0`: `z[2i+1], z[2i] = mulWW(x[i], x[i])`, the slice expressions `t[i:2i]`, `x[0:i]`,
the `addMulVVWW.abi0` frame `[RSP - 192, RSP - 104)` (`body2` from the `CALL`). The loop exits to the continuation
`hfin` at `i = n`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.BasicSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem step (impl : List Amd64.Segment) (R : RtInv)
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1) (Q : State → Prop)
    (i : Nat) (h1 : 1 ≤ i) (hiy : i < xl.toNat)
    (hk : HeadK impl R L st zp zl zc xp xl xc s t L1 b1 w1 c1 Q (i + 1)) :
    HeadK impl R L st zp zl zc xp xl xc s t L1 b1 w1 c1 Q i := by
  intro S hpc hsp h5 h14 hfs hx15 hdf r0 r3 r1 r7 r6 r8 r9 r10 hI
  have hI' := hI
  obtain ⟨hM, hz, ht, h0⟩ := hI'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf,
    minv⟩ := hM
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl := hl.zl2; have hx0 := hl.x0; have hz48 := hl.z48
  have ht48 := hl.t48
  have hzwA : Apart zp.toNat (16 * xl.toNat) ((s.regs 4).toNat - 4424) 4488 := by unfold Apart; have := hl.zw; omega
  have hxwA : Apart xp.toNat (8 * xl.toNat) ((s.regs 4).toNat - 4424) 4488 := by unfold Apart; have := hl.xw; omega
  have htwA : Apart t (16 * xl.toNat) ((s.regs 4).toNat - 4424) 4488 := by unfold Apart; have := hl.tw; omega
  have htxA : Apart t (16 * xl.toNat) xp.toNat (8 * xl.toNat) := by unfold Apart; have := hl.tx; omega
  have htzA : Apart t (16 * xl.toNat) zp.toNat (16 * xl.toNat) := by unfold Apart; have := hl.tz; omega
  have hzxA : Apart zp.toNat (16 * xl.toNat) xp.toNat (8 * xl.toNat) := by unfold Apart; have := hl.zx; omega
  have hpre := hE.pre
  have hce := hpre.ce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, -, -, ⟨htb, htr, htg⟩, htrt, htw⟩ := hce
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  have hzlv := hpre.zlive; have hzg := hpre.zg; have hxacc := hpre.xacc; have hx48 := hpre.x48
  obtain ⟨hzal, hzh, hzacc, -⟩ := hzlv (by omega)
  have hscr := hE.scr
  rw [← mfr.accessible] at hxacc hzacc
  have htacc : S.mem.accessible t (8 * (2 * xl.toNat)) true = true := by rw [mfr.accessible]; exact hscr.acc
  have hzh1 := hE.ext.held hzh
  rw [hzl] at hzh1
  have hxi : S.mem.readLE (xp.toNat + 8 * i) 8 = s.mem.readLE (xp.toNat + 8 * i) 8 :=
    mxs _ _ (by omega) (by omega)
  have hmask : ((0#64 - (BitVec.ofNat 64 (2 * xl.toNat) - BitVec.ofNat 64 i)).sshiftRight 63).toNat =
      18446744073709551615 := by
    have hz := hpre.zcb; have hzc := hpre.zlc
    refine sshr63_of_lt _ _ ?_ ?_ <;> simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega
  clear hpre hscr hzlv hg1 hg2
  janus64_run [BitVec.msb_eq_decide, hxi, hfs, hmask, and_ones64 (8 * i) (by omega), m3, m4, m5, m10, m11, m12, m13, m14, m15,
    and_ones64 (i * 8) (by omega), mod64_of_lt (t + 8 * i) (by omega)] until [callMV]
  refine body2 impl R hMV' b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE Q i h1 hiy S.mem hI hk _ ?_ ?_ ?_ ?_ ?_ ?_
    ?F ?z0 ?z1 ?_ ?_ ?_ ?_ ?f5 ?_ ?_ ?_ ?_ ?inv
  case F => janus_frame
  case inv =>
    refine RtInv.inv_frame' (ws := [(zp.toNat + 16 * i, zp.toNat + 16 * i + 16),
      ((s.regs 4).toNat - 192, (s.regs 4).toNat - 104), ((s.regs 4).toNat - 72, (s.regs 4).toNat - 48)])
      (by janus_frame) (fun r hr => ?_) minv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact (hzh1.sub (by omega) (by omega)).symm
    · left; exact hout.of_sub (by omega) (by omega)
    · left; exact hout.of_sub (by omega) (by omega)
  all_goals (try janus64_simp)
  all_goals (try simp only [Nat.mul_comm i 8, Nat.mul_comm i 16])
  all_goals first | exact hfs | exact hdf | omega | skip

theorem loop (impl : List Amd64.Segment) (R : RtInv)
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (t : Nat) (L1 : List (Nat × Nat)) (b1 w1 c1 : Nat)
    (hE : Env R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s t L1 b1 w1 c1) (Q : State → Prop)
    (hfin : HeadK impl R L st zp zl zc xp xl xc s t L1 b1 w1 c1 Q xl.toNat) :
    ∀ k i, i + k = xl.toNat → 1 ≤ i → HeadK impl R L st zp zl zc xp xl xc s t L1 b1 w1 c1 Q i := by
  intro k
  induction k with
  | zero => intro i hi _; obtain rfl : i = xl.toNat := by omega
            exact hfin
  | succ k ih =>
    intro i hi h1
    exact step impl R hMV' b L st zp zl zc xp xl xc s t L1 b1 w1 c1 hE Q i h1 (by omega)
      (ih (i + 1) (by omega) (by omega))

end FvModexp.Amd64.BasicSqr
