import FvModexp.Proofs.Amd64.Top.RunDJDefs

/-! # `Run` (amd64): `C0` to `J0` — base operand, padded, `baseLen > 32`: `makeslice(uint8, h0, h0)`

As `RunDP0` up to the `JA` (`h0 > 32` taken): `AX = type:uint8`, `BX = CX = h0`, `makeslice` (call `fn + 0x661`,
return `fn + 0x666`), the registers reloaded from the slots, `SI` = the fresh zeroed buffer, `R10 = min(h0, DX)`: `J0`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem dM0 (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hokB : ∀ n, n ≤ 1024 → R.ok (cA "runtime.makeslice") [uint8T, n, n])
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
    (hndir : len.toNat - 96 < hdrV s p len 0) (hbig : 32 < hdrV s p len 0)
    (hk : ∀ S2 bk dst e, JoinE R b L c p len cp s ret 0 L1 [(dst, e)] bk dst (p.toNat + inOff len) S2 →
      FreshDst R s (hdrV s p len 0) dst e → S2.rip = BitVec.ofNat 64 pcJ0 → (S2.regs 6).toNat = dst → (S2.regs 3).toNat = p.toNat + inOff len →
      (S2.regs 10).toNat = min (hdrV s p len 0) (len.toNat - 96) → (S2.regs 1).toNat = hdrV s p len 0 →
      (S2.regs 2).toNat = min (hdrV s p len 0) (len.toNat - 96) → (S2.regs 13).toNat = hdrV s p len 1 →
      Reaches ((LibRun.program.link impl).withExit ret) S2 Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
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
  have hI9 := toInt_small (T.regs 9) (by omega)
  have hr1' : T.regs 1 = BitVec.ofNat 64 (hdrV s p len 0) := by
    apply BitVec.eq_of_toNat_eq; rw [hr1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hc : ((T.regs 9).toNat < hdrV s p len 0) = True := by simp; omega
  have hc32 : (32 < hdrV s p len 0) = True := by simp; omega
  have hmk' : MakesliceLiveContract64 (LibRun.program.link impl) (cA "runtime.makeslice") 4096 R :=
    MakesliceLiveContract64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hmk
  have hmkP := hmk'.pos L1 b1
  janus_eval_nat h_u : uint8T
  have hokb : R.ok (cA "runtime.makeslice") [7231264, hdrV s p len 0, hdrV s p len 0] := by
    have := hokB _ hl0; rwa [h_u] at this
  have hU2 : S.mem.readLE 7231264 8 = 1 := by
    janus64_data hdS; rw [h_rodata _ _ (by decide)]; decide
  have hU3 : S.mem.readLE 7231272 8 = 0 := by
    janus64_data hdS; rw [h_rodata _ _ (by decide)]; decide
  have hut : Apart 7231264 16 ((s.regs 4).toNat - 4800) (4800 + 40) :=
    apart_of_data (x := 7231264) (l := 16) hd 0 (by decide) (by decide) hw
  unfold Apart at hut
  have hU1 : S.mem.accessible 7231264 16 false = true := by
    rw [hMF.accessible]; janus64_data hd; exact Janus.Arm64.Memory.accessible_mono _ h_data0 (by omega) (by omega)
  have hBS : blockSize (hdrV s p len 0) true ≤ b1 := by
    have := blockSize_le_allocCost (hdrV s p len 0) true
    simp only [cstD, dCost, allocCost, makeCost, makeCap] at this hbud hbud1 ⊢; omega
  have hLSm : ∀ r ∈ L1, Outside r.fst (r.snd - r.fst)
      ([((s.regs 4).toNat - 616 - 4096, (s.regs 4).toNat - 616),
          ((s.regs 4).toNat - 616 + 8, (s.regs 4).toNat - 616 + 8 + 24)] ++
        [((s.regs 4).toNat - 616, (s.regs 4).toNat - 616 + 8)]) := by
    intro r hr; have := hLsS r hr
    simp only [LiveSep, win, stk, Outside, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
    omega
  janus64_run [hTm, hT4, hT14, hT5, hTx, hTfs, hTdf, hsp, hr1', hI1, hI9, hc, hc32, hU2, hU3, toInt_ite, toNat_ite,
    BitVec.msb_eq_decide] until [pcJ0] calls [hmkP]
  rename_i ptr _ _ _ _ m _ _ hLFk hMFk hAp hIn hle hacc h8 _ hzk hsz hapW hinvk
  sorry

end FvModexp.Amd64.Run
