import FvModexp.Proofs.Arm64.Nat.BasicSqrPro

/-!
# `basicSqr(stk, z, x)` (go-bigmodexpfix natmul.go:113), arm64: the summary

`pro1`: entry → `CALL (*stack).nat` (large path); `full`: the `Summary` at the entry (`n < 12`: `small`; else `pro1`);
`ens`: the `Ensures` of CONVENTIONS §3; `sum`: `ens` as a callee summary.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.BasicSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem pro1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (stkSN abSN : Nat) (hSN : ExpHyp.StackNatHyp impl R [ExpHyp.fnStackNat] stkSN abSN)
    (hk1 : stkSN ≤ 4224) (hk2 : abSN ≤ 96)
    (hmc : MemclrNoHeapPointersLive (LibBasicSqr.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hLsh : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program lshVUfn) (LshLPre R b L)
      (LshLQ R b L))
    (hVV : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addVVfn) (VVLPre R b L)
      (VVLQ R b L))
    (hMV' : ∀ b L, Summary0 (LibBasicSqr.program.link impl) (segAddr Extracted.program addMulVVWWfn)
      (VVWWLPre R b L) (VVWWLQ R b L))
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = st) (h1 : s.regs 1 = zp)
    (h2 : s.regs 2 = zl) (h3 : s.regs 3 = zc) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hbig : 12 ≤ xl.toNat) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hce := hpre.ce; have hthA := hpre.thA; have hthV := hpre.thV; have hthO := hpre.thO
  have hzl := hpre.zl2; have hzc40 := hpre.zcb; have hzc := hpre.zlc
  have hlen := hpre.stlen
  have hce' := hce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hce'
  have hstok := hpre.stok
  obtain ⟨-, -, hstacc, hst48, -, -, -⟩ := hstok
  have hsw := hpre.stw; simp only [win, outside_cons, outside_nil, and_true] at hsw
  have eA : thrA = 7147152 := rfl
  rw [eA] at hthA hthV hthO
  simp only [win, outside_cons, outside_nil, and_true] at hthO
  have eD : segAddr LibBasicSqr.program (fn ++ ".deferwrap1") = 1817392 := by decide
  have hxx : BitVec.ofNat 64 (2 * xl.toNat) = xl + xl := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_add]; omega
  janus_run [hthV, toInt_small xl (by omega), toInt_small (BitVec.ofNat 64 12) (by decide)] until [callNat]
  refine pro2 impl hap R stkSN abSN hSN hk1 hk2 hmc hLsh hVV hMV' b L st zp zl zc xp xl xc s hpre hbig hl4 hl48 _
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?qF, ?qR, ?_, ?_, ?_, ?qD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?qI
  case qF => janus_frame
  case qR => simp only [Memory.writeLE_regions]
  case qD => rw [eD]; janus_simp
  case qI =>
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 216, s.sp.toNat - 200), (s.sp.toNat - 89, s.sp.toNat - 88),
      (s.sp.toNat - 56, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 64)]) (by janus_frame) (fun r hr => ?_) hpre.inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (left; exact hout.of_sub (by omega) (by omega))
  all_goals try (rw [hxx])
  all_goals janus_simp

end FvModexp.Arm64.BasicSqr
