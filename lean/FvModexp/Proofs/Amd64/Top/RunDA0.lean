import FvModexp.Proofs.Amd64.Top.RunDE0

/-! # `Run` (amd64): `C0` to `pcE0` — base operand, direct slice (`baseLen ≤ len(input[96:])`)

At `C0` (`fn + 0x5c7`) the lengths are spilled (`e-480` = `cp - k`, `e-216` = `p + k`, `e-488` = `len - 96`, `e-464` = `h0`,
`e-528` = `h1`, `e-472` = `h2`), the base `big.Int` is zeroed, `DX = min(h0, len - 96)` (`e-512`); with `h0 ≤ DX` the buffer
is `input[96:][0:h0]` itself (`SI = BX`, `R8 = DX`, `CX = DI`), then `DX + h1` (`e-520`) and the `setBytes` arguments. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dA0 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokS : ∀ n, n ≤ 128 → R.ok (cA "runtime.makeslice") [SetBytes.wordT, n, makeCap n])
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s) (hbud : cstD 3 ≤ b)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 3 L1 b1 S)
    (T : State) (hTpc : T.rip = BitVec.ofNat 64 pcC0) (hTm : T.mem = S.mem) (hT4 : T.regs 4 = S.regs 4)
    (hT14 : T.regs 14 = S.regs 14) (hT5 : T.regs 5 = S.regs 5) (hTx : T.xmm 15 = S.xmm 15)
    (hTfs : T.fsBase = S.fsBase) (hTdf : T.df = S.df)
    (hl0 : hdrV s p len 0 ≤ 1024) (hl1 : hdrV s p len 1 ≤ 1024) (hl2 : hdrV s p len 2 ≤ 1024)
    (hnz : ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0))
    (hr1 : (T.regs 1).toNat = hdrV s p len 0) (hr13 : (T.regs 13).toNat = hdrV s p len 1)
    (hr0 : (T.regs 0).toNat = hdrV s p len 2) (hr3 : (T.regs 3).toNat = p.toNat + (if 96 < len.toNat then 96 else 0))
    (hr7 : (T.regs 7).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0)) (hr9 : (T.regs 9).toNat = len.toNat - 96)
    (hdir : hdrV s p len 0 ≤ len.toNat - 96)
    (hk : ∀ S2 L2 b2, RelD R b L c p len cp s ret 1 1 (cstD 1) L2 b2 S2 → S2.rip = BitVec.ofNat 64 pcD1 →
      (S2.regs 0).toNat = S2.mem.readLE (opAt s 0 + 8) 8 → (S2.regs 3).toNat = S2.mem.readLE (opAt s 0 + 16) 8 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  have henv0 := henv
  have hin0 := hin
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, -, hdS, hinS, hcS, hext, hbud1, hinv, hLsS, hMF,
    hLF, -⟩ := hrel
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  simp only [stk] at hg3 hb' ha hw hout hpw hcw hMF
  simp only [win, Outside, and_true] at hpw hcw
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 608 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hI1 := toInt_small (T.regs 1) (by omega)
  have hr1' : T.regs 1 = BitVec.ofNat 64 (hdrV s p len 0) := by
    apply BitVec.eq_of_toNat_eq; rw [hr1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hc : ((T.regs 9).toNat < hdrV s p len 0) = False := by simp; omega
  janus64_run [hTm, hT4, hT14, hT5, hTx, hTfs, hTdf, hsp, hr1', hI1, hc, toInt_ite, toNat_ite,
    BitVec.msb_eq_decide] until [pcE0]
  refine dE0 impl hap R hmk hokS b L c p len cp ret hret s hx0 hdf0 henv0 hin0 hbud Q _ L1 b1
    (RelD.mk' hin0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hl0 hl1 hl2 hnz ?_ ?_ ?_ hext ?_ ?_ hLsS ?_ ?_
      (fun j hj => absurd hj (by omega)) (fun _ _ _ h => absurd h (by omega))) (by janus64_simp) (by janus64_simp)
    (by janus64_simp) (by janus64_simp) ?buf hk
  all_goals try (janus64_simp [hTm, hT4, hT14, hT5, hTx, hTfs, hTdf, hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, hr1, hr13, hr0, hr3, hr7, hr9, hc]; done)
  all_goals try (first | (dsimp only; rw [hTfs]; exact hfs; done) | (dsimp only; rw [hTdf]; exact hdf; done))
  case refine_19 =>
    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd h (by decide)⟩
    · janus64_simp [hr1, hr9, hc]; omega
    · janus64_simp [hr1, hr9, hr13, hc]; omega
  case refine_20 =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp only [opAt]
    all_goals first
      | (janus64_simp; done)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          Janus.Arm64.Memory.readLE_writeLE_inside, Nat.zero_div, Nat.zero_mod, hx15, hTx, hx0]; done)
      | janus64_simp [hTx, hx15, hx0]
  case refine_21 => janus64_callpre
  case refine_22 => simp only [cstD, cstE] at hbud1 ⊢; omega
  case refine_23 =>
    dsimp only
    repeat rw [view_writeLE_out (hout.of_sub (by omega) (by omega))]
    first | exact hinv | exact RtInv.inv_congr hinv rfl (by janus64_simp) rfl
  case refine_24 => dsimp only; simp only [win, stk] at hMF ⊢; janus_frame
  case refine_25 =>
    dsimp only
    exact hLF.trans (LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsS) (fun _ _ h => hext.inRanges_old h)
  case buf =>
    have h96 : 96 < len.toNat ∨ hdrV s p len 0 = 0 := by omega
    have hbp : (p.toNat + (if 96 < len.toNat then 96 else 0)) + hdrV s p len 0 ≤ p.toNat + len.toNat := by split <;> omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · janus64_simp; simp [opLen]
    · janus64_simp [hr3]
      simp only [opV, opStart, opLen, ite_true, Nat.add_zero]
      rcases h96 with h96 | h0
      · rw [padBE_inside _ _ _ _ _ (by omega)]
        simp only [if_pos h96]
        refine beVal_of_reads' (by first | rfl | simp [h96] | omega) (by first | rfl | omega) fun i hi => ?_
        repeat rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hinS _ _ (by omega) (by omega)
      · rw [h0]; rfl
    · janus64_simp [hr3]
      exact Janus.Arm64.Memory.accessible_mono _ hpacc (by split <;> omega) (by omega)
    · janus64_simp [hr3]; omega
    · janus64_simp [hr3]
      exact hext.held (hheld.sub (by split <;> omega) hbp)
    · janus64_simp [hr3]
      first | (split <;> omega) | omega | (simp only [Janus.outside_cons, Janus.outside_nil, and_true, Outside]; split <;> omega)

end FvModexp.Amd64.Run
