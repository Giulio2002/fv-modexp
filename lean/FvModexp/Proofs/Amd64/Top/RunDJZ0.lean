import FvModexp.Proofs.Amd64.Top.RunDJDefs

/-! # `Run` (amd64): operand 0, fresh `makeslice` buffer, `dst = src` — the join `J0` to the `setBytes` call `pcE0`

The `JE` is taken: the copy is skipped. This is possible only with nothing to copy (`n = 0`: a fresh object is apart
from the input when it has a byte at `src`).

At `J0` (`fn + 0x6a2`) the zeroed 32-byte stack buffer `e - 392` (`SI`) receives the `n = R10` available input bytes
from `src = BX` (`CMPQ SI, BX; JE` never taken: the input is outside the frame window), `memmove` returns at
`fn + 0x6ba`, the registers are reloaded, `e - 520 = min(h0, len - 96) + h1` is stored and the `setBytes` arguments
`buf = (DI, SI, R8) = (e - 392, h0, h0)`, `z = nil` are set up. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dJZ0 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hokM : ∀ d sr n, n ≤ 2 ^ 20 → R.ok (cA "runtime.memmove") [d, sr, n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (L0 : List (Nat × Nat)) (bk src dst e : Nat)
    (hj : JoinE R b L c p len cp s ret 0 L0 [(dst, e)] bk dst src S) (hfr : FreshDst R s (hdrV s p len 0) dst e)
    (heq0 : dst = src)
    (hpc : S.rip = BitVec.ofNat 64 pcJ0)
    (hr6 : (S.regs 6).toNat = dst) (hr3 : (S.regs 3).toNat = src)
    (hr10 : (S.regs 10).toNat = min (hdrV s p len 0) (len.toNat - 96)) (hr1 : (S.regs 1).toNat = hdrV s p len 0)
    (hr2 : (S.regs 2).toNat = min (hdrV s p len 0) (len.toNat - 96)) (hr13 : (S.regs 13).toNat = hdrV s p len 1)
    (hk : ∀ S2, AtE R b L c p len cp s ret 0 pcE0 S2 → Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) S Q := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  have hin0 := hin
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hrel, hsl0, hzb, hsrc0, hsrc1, hsrc2, hd48, hdacc, hextL0, hsepb, -⟩ := hj
  obtain ⟨hfe, hfrt, hfw⟩ := hfr
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, s1, s2, s3, s4, s5, s6, l0, l1, l2, lnz, -, hz,
    hdS, hinS, hcS, hext, hbk, hinv, hLsS, hMF, hLF, -, -⟩ := hrel
  have hsl := hsl0 rfl
  simp only [opLen, opAvail, opStart, stkBuf, ↓reduceIte, Nat.sub_zero, Nat.add_zero, Nat.mul_zero] at hzb hsrc1 hsrc2 hd48 hdacc
  obtain ⟨hz0, hz1, hz2, hz3⟩ := hz (by decide)
  obtain ⟨ho0, ho1, ho2, ho3⟩ := opAt_eqs (j := 0) hb' (by decide)
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero] at ho0 ho1 ho2 ho3
  simp only [opAt, Nat.mul_zero, Nat.sub_zero, ho1, ho2, ho3] at hz0 hz1 hz2 hz3
  rw [hx0] at hx15
  rw [hdf0] at hdf
  have hmv' : MemmoveLive64 (LibRun.program.link impl) (cA "runtime.memmove") 4096 R :=
    MemmoveLive64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hmv
  have hLs0 := hLsS
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  simp only [stk] at hg3 hb' ha hw hout hga hLs hpw hcw hLsS hMF
  obtain ⟨⟨hfs8, hfsacc, hfsg⟩, hfsrt, hfsw⟩ := htls
  unfold Apart at hfsw hga
  simp only [stk] at hfsw
  have hwS : S.mem.accessible ((s.regs 4).toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 608 := by rw [hsp]; exact toNat_sub_k (Nat.le_trans (by decide) hb') (by decide)
  simp only [LiveSep, win] at hLsS
  simp only [win, Outside, and_true] at hpw hcw
  have hLsL1 : LiveSep (L0 ++ [(dst, e)]) (win s 4800 40) := hLs0
  have hwrt : ∀ r ∈ win s 4800 40, Outside r.1 (r.2 - r.1) R.rt := fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
    exact hout.of_sub (Nat.le_refl _) (win_len hb')
  have hstk : stk = 4800 := rfl
  -- the copy: `memmove(e - 392, src, n)`, `n = min(h0, len - 96) ≤ 32`
  have hn0 : min (hdrV s p len 0) (len.toNat - 96) = 0 :=
    n0_of_eq heq0 hfe hfrt hheld hextL0 hsepb (fun hn => hsrc2 hn) hsrc1 (Nat.min_le_left _ _)
  have heq : (S.regs 6 = S.regs 3) = True := eq_true (BitVec.eq_of_toNat_eq (by rw [hr6, hr3]; exact heq0))
  simp only [win, stk, Janus.outside_cons, Janus.outside_nil, and_true] at hfw
  have hLsL0 : LiveSep L0 (win s 4800 40) := fun r hr => hLsL1 r (List.mem_append_left _ hr)
  clear hpw hcw hga hfsw hokM hmv hmv' hsl0 hz
  janus64_run [hr6, hr3, hr10, hr1, hr2, hr13, heq, hm1, s1, s2, s3, s4, s5, s6, hsl, hz0, hz1, hz2, hz3, hx15,
    hdf, toInt_ite, toNat_ite, BitVec.msb_eq_decide] until [pcE0]
  refine hk _ ⟨L0 ++ [(dst, e)], bk, RelD.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ l0 l1 l2 lnz ?_ ?_ ?_ hext ?_
    ?_ hLs0 ?_ ?_ (fun j hj => absurd hj (Nat.not_lt_zero j)) (fun _ _ _ h => absurd h (Nat.not_lt_zero _)), by janus64_simp,
    by janus64_simp, by janus64_simp, by janus64_simp, ?buf⟩
  all_goals try (janus64_simp; done)
  all_goals try (first | (dsimp only; rw [hfs]; done) | (dsimp only; exact hdf.trans hdf0.symm; done) | (simp only [hfs]; done) | (simp only [hdf, hdf0]; done))
  case refine_19 =>
    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd h (by decide)⟩
    · janus64_simp
    · janus64_simp
  case refine_20 =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp only [opAt, Nat.mul_zero, Nat.sub_zero, ho1, ho2, ho3]
    all_goals janus64_simp [hz0, hz1, hz2, hz3]
  case refine_21 => janus64_callpre
  case refine_22 => simp only [cstD, cstE] at hbk ⊢; exact hbk
  case refine_23 =>
    dsimp only
    rw [view_writeLE_out (hout.of_sub (buf_in_win (k := 520) (n := 8) hb' (by decide) (by decide)).1
      (buf_in_win (k := 520) (n := 8) hb' (by decide) (by decide)).2)]
    first | exact hinv | exact RtInv.inv_congr hinv rfl (by janus64_simp) rfl
  case refine_24 => dsimp only; simp only [win, stk] at hMF ⊢; janus_frame
  case refine_25 =>
    dsimp only
    exact hLF.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL0) (fun _ _ h => hextL0.inRanges_old h)
  case buf =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try janus64_simp [hr6, hr1]
    · simp only [opLen, ↓reduceIte]
    · simp only [opV, opStart, opLen, ↓reduceIte, Nat.add_zero]
      rw [beVal_writeLE_disj (fresh_slot hb' (by decide) (by decide) hfw
        (by have := Nat.le_trans (Nat.le_add_right _ _) hfe; omega))]
      refine padded_val (n := 0) (mW := S.mem) (src := src) (fun i hi => absurd hi (Nat.not_lt_zero i))
        (fun h => absurd h (Nat.lt_irrefl 0)) ?_ hn0.symm
      intro i _ h2
      exact hzb i h2
    · exact Janus.Arm64.Memory.accessible_read_of_write _ hdacc
    · exact hd48
    · exact Or.inl ⟨(dst, e), by simp, Nat.le_refl _, hfe⟩
    · exact (fresh_call_facts (n := hdrV s p len 0) hb' (by
        rcases hfw with h | h
        · exact Or.inl (Nat.le_trans hfe (by rw [Nat.add_sub_cancel' (Nat.le_trans (Nat.le_add_right _ _) hfe)] at h; exact h))
        · exact Or.inr h)).2.2.2

end FvModexp.Amd64.Run
