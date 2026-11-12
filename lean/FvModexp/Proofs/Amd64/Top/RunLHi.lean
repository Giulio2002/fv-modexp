import FvModexp.Proofs.Amd64.Top.RunLDefs
import FvModexp.Proofs.Amd64.Top.RunSmall

set_option autoImplicit false

/-! # `Run` (amd64): `P1` to `C0`, `96 < len` — — EIP-7823 (`max BitLen > 64` or `max Uint64 > 1024`: `errors.New`), the empty case,
the input slice

amd64 code: `max` of the bit lengths (`CMOVG`), `input[96:]` (`len > 96`: `DI = cap - 96`, `BX = p + 96`,
`R9 = len - 96`; else `R9 = 0`), the receiver's `eip7823` byte (`CMPB 1(R11), $0`), `CMPQ DX, $64; JG` → error,
`max` of the `Uint64`s (`CMOVA`, `CX` = baseLen), `CMPQ R10, $1024; JBE` → empty test (`CX`, `AX`) or `C0 = 0x654907`;
error: `newobject(errT)` at `0x6548b0`, two stores, `(nil, 0, 0, itab, obj)`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem lbHi (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) (ret : Nat)
    (hret : RetAddr (LibRun.program.link impl) ret) (s : State) (hdf0 : s.df = false)
    (henv : CallEnv R L s stk 40) (hin : InputOK R L c p len cp s)
    (hrecv : s.mem.readLE c.toNat 3 = 65793) (h96 : 96 < len.toNat) (hokn : R.ok (cA "runtime.newobject") [errT])
    (hcostE : 3 * makeCost 4 + allocCost 16 ≤ b)
    (Q : Janus.Amd64.Outcome → Prop)
    (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (hrel : RelH R b L c p len cp s ret 3 L1 b1 S)
    (T : State) (hTpc : T.rip = BitVec.ofNat 64 pcP1) (hTm : T.mem = S.mem) (hT4 : T.regs 4 = S.regs 4)
    (hT14 : T.regs 14 = S.regs 14) (hT5 : T.regs 5 = S.regs 5) (hTx : T.xmm 15 = S.xmm 15)
    (hTfs : T.fsBase = S.fsBase) (hTdf : T.df = S.df)
    (hL0 : LenRegs (hdrV s p len 0) (T.regs 2) (T.regs 10)) (hL1 : LenRegs (hdrV s p len 1) (T.regs 9) (T.regs 13))
    (hL2 : LenRegs (hdrV s p len 2) (T.regs 11) (T.regs 0))
    (hErr : ∀ S' : State, (1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2) →
      ABIReturn s S' → ErrRet S' → RunFrame R b (3 * makeCost 4 + allocCost 16) L s S' → Q (.returned S'))
    (hZero : ∀ S' : State, hdrV s p len 0 = 0 → hdrV s p len 1 ≤ 1024 → hdrV s p len 2 = 0 →
      ABIReturn s S' → S'.regs 3 = 0#64 → S'.regs 7 = 0#64 → RunFrame R b (3 * makeCost 4) L s S' → Q (.returned S'))
    (hk : ∀ T' : State, T'.rip = BitVec.ofNat 64 pcC0 → T'.mem = S.mem → T'.regs 4 = S.regs 4 →
      T'.regs 14 = S.regs 14 → T'.regs 5 = S.regs 5 → T'.xmm 15 = S.xmm 15 → T'.fsBase = S.fsBase → T'.df = S.df →
      hdrV s p len 0 ≤ 1024 → hdrV s p len 1 ≤ 1024 → hdrV s p len 2 ≤ 1024 →
      ¬(hdrV s p len 0 = 0 ∧ hdrV s p len 2 = 0) →
      (T'.regs 1).toNat = hdrV s p len 0 → (T'.regs 13).toNat = hdrV s p len 1 → (T'.regs 0).toNat = hdrV s p len 2 →
      (T'.regs 3).toNat = p.toNat + (if 96 < len.toNat then 96 else 0) →
      (T'.regs 7).toNat = cp.toNat - (if 96 < len.toNat then 96 else 0) → (T'.regs 9).toNat = len.toNat - 96 →
      Reaches ((LibRun.program.link impl).withExit ret) T' Q) :
    Reaches ((LibRun.program.link impl).withExit ret) T Q := by
  obtain ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hLs, hro, htls⟩ := henv
  have hLsL1 : LiveSep L1 (win s 4800 40) := hrel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hcacc, hc48, hcheld, hcw, hp, hlcp, hcp48, hpacc, hheld, hpw⟩ := hin
  obtain ⟨hsp, h14, h5, hx15, hfs, hdf, hm1, hm2, hm3, hm4, hm5, hm6, -, hdS, hinS, hcS, hext, hbud, hinv, hLsS, hMF,
    hLF, -⟩ := hrel
  have hno' : NewobjectLiveContract64 (LibRun.program.link impl) (cA "runtime.newobject") 4096 R :=
    NewobjectLiveContract64.of_codeIn (by rw [LibRun.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibRun.names) hno
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
  have hgS : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hMF.readLE _ _ (by
      simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hgr, by omega⟩)
  have htS : S.mem.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by
    rw [hMF.readLE _ _ (by
      simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hfsrt, by omega⟩)]
    simpa [regG] using hfsg
  rw [hdf0] at hdf
  have hc1 : S.mem.readLE (c.toNat + 1) 1 = 1 := by
    rw [← hcS] at hrecv
    have h3 := Janus.Arm64.Memory.readLE_add S.mem c.toNat 1 2
    have h4 := Janus.Arm64.Memory.readLE_add S.mem (c.toNat + 1) 1 1
    have l1 := Janus.Arm64.Memory.readLE_lt S.mem c.toNat 1
    have l2 := Janus.Arm64.Memory.readLE_lt S.mem (c.toNat + 1) 1
    have l3 := Janus.Arm64.Memory.readLE_lt S.mem (c.toNat + 1 + 1) 1
    rw [hrecv] at h3; rw [h4] at h3; omega
  have hLSn : ∀ r ∈ L1, (r.1 + (r.2 - r.1) ≤ BitVec.toNat (s.regs 4) - 616 - 4096 ∨ BitVec.toNat (s.regs 4) - 616 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ BitVec.toNat (s.regs 4) - 616 ∨ BitVec.toNat (s.regs 4) - 616 + 8 ≤ r.1) := by
    intro r hr; have := hLsS r hr; simp only [LiveSep, win, Outside, and_true] at this; omega
  have hwS : S.mem.accessible ((s.regs 4).toNat - 4800) (4800 + 40) true = true := by rw [hMF.accessible]; exact hw
  have hEw : Apart errT 16 ((s.regs 4).toNat - 4800) (4800 + 40) :=
    apart_of_data hdS 3 (by decide) ⟨by decide, by decide⟩ hwS
  have hdE := errProg_loaded hdS
  janus64_data hdE
  janus_eval_nat h_e : errT
  rw [h_e] at hokn hEw
  unfold Apart at hEw
  have hT2 : ∀ v, (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v).readLE 7355552 8 = 16 := fun v => by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), h_rodata _ _ (by decide)]; decide
  have hT3' : ∀ v, (S.mem.writeLE ((s.regs 4).toNat - 616) 8 v).readLE 7355560 8 = S.mem.readLE 7355560 8 := fun v => by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hT3 : blockSize 16 (S.mem.readLE 7355560 8 == 0) ≤ b1 := by
    have := blockSize_le_allocCost 16 (S.mem.readLE 7355560 8 == 0); simp only [allocCost] at this
    simp only [makeCost, allocCost, makeCap] at hbud hcostE; omega
  have hLSw : ∀ r ∈ L1, Outside r.fst (r.snd - r.fst)
      ([(BitVec.toNat (s.regs 4) - 616 - 4096, BitVec.toNat (s.regs 4) - 616),
          (BitVec.toNat (s.regs 4) - 616 + 8, BitVec.toNat (s.regs 4) - 616 + 8 + 8)] ++
        [(BitVec.toNat (s.regs 4) - 616, BitVec.toNat (s.regs 4) - 616 + 8)]) := by
    intro r hr; have := hLsS r hr
    simp only [LiveSep, win, Outside, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at this ⊢
    omega
  have hnoP := hno'.pos L1 b1
  have hL0' := hL0
  have hL1' := hL1
  have hL2' := hL2
  obtain ⟨hB0, hO0, hU0⟩ := hL0
  obtain ⟨hB1, hO1, hU1⟩ := hL1
  obtain ⟨hB2, hO2, hU2⟩ := hL2
  have hI2 := toInt_small (T.regs 2) (by omega)
  have hI9 := toInt_small (T.regs 9) (by omega)
  have hI11 := toInt_small (T.regs 11) (by omega)
  have hIl : len.toInt = (len.toNat : Int) := toInt_small len (by omega)
  clear hinS hcS hLs hcheld hheld hpw hcw hpacc hd hno hro hrecv
  janus64_run [hTm, hT4, hT14, hT5, hTx, hTfs, hTdf, hsp, hm1, hm2, hm3, hm4, hm5, hm6, hc1, hgS, htS, hfs, hdf, hx15, hT2, hT3', hT3, hI2, hI9, hI11, hIl, toInt_ite, toNat_ite,
    ite3_int_gt, ite3_nat_le, BitVec.msb_eq_decide] until [pcC0, segAddr Extracted.program fn + 0x575] calls [hnoP]
  all_goals first
  | (rename_i ptr _ _ _ _ m _ _ hLFn hMFn hapL hinR hb48 hacc h8 h16 hz _ hapS hinvn
     (try simp (disch := omega) only [cmova_max] at *)
     have hcond : 1024 < hdrV s p len 0 ∨ 1024 < hdrV s p len 1 ∨ 1024 < hdrV s p len 2 := by
       first
       | exact err_of_big hL0' hL1' hL2' (by omega)
       | exact err_of_u hL0' hL1' hL2' (by omega) (by omega)
     have hpo : ptr.toNat + 16 ≤ (s.regs 4).toNat - 4800 ∨ (s.regs 4).toNat + 40 ≤ ptr.toNat := by
       have := InRanges.apart hinR hout; unfold Apart at this; omega
     janus64_run [hm1, hm2]
     refine hErr _ hcond ⟨by janus64_simp [hsp, hT4], by janus64_simp [hm2, regFP], by janus64_simp [h14, hT14, regG],
         by janus64_simp [hx15, hTx]⟩ ⟨by janus64_simp, by janus64_simp, by janus64_simp⟩
       ⟨by janus64_simp [hTfs, hfs], by janus64_simp [hTdf, hdf, hdf0], L1 ++ [(ptr.toNat, ptr.toNat + 16)], b1 - 16, ?_, ?_, ?_, ?_, ?_⟩
     · exact hext.trans (LiveExt.single (by simpa using hinR) (by simpa using hapL))
     · exact bud_err hbud
     · dsimp only
       have hI : ∀ a, ptr.toNat ≤ a → a + 8 ≤ ptr.toNat + 16 → InRanges a 8 (L1 ++ [(ptr.toNat, ptr.toNat + 16)]) :=
         fun a h1 h2 => ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega, by dsimp only; omega⟩
       first
       | exact inv_store_live (inv_store_live hinvn (hI _ (by omega) (by omega))) (hI _ (Nat.le_refl _) (by omega))
       | exact inv_store_live (inv_store_live hinvn (hI _ (Nat.le_refl _) (by omega))) (hI _ (by omega) (by omega))
     · dsimp only
       refine ⟨fun a n h => ?_, fun a n w => by
         simp only [Janus.Arm64.Memory.accessible_writeLE, hMFn.accessible, hMF.accessible, hTm]⟩
       have h' := h
       simp only [win, stk, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h'
       have hd1 := InRanges.apart hinR h'.1
       unfold Apart at hd1
       rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
         hMFn.readLE _ _ (by
           simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
           exact ⟨h'.1, by omega, by omega⟩),
         Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
         hMF.readLE _ _ (by
           simp only [win, Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
           exact ⟨h'.1, by omega⟩)]
     · dsimp only
       have ho := hapL.outside
       refine hLF.trans ((((LiveFrame.of_win (by simp only [win, stk]; janus_frame) hLsL1).trans hLFn (fun _ _ h => h)).writeLE _
         (ho.of_sub (by omega) (by omega))).writeLE _ (ho.of_sub (Nat.le_refl _) (by omega))) (fun _ _ h => hext.inRanges_old h))

  | (guard_target =~ Q _
     (try simp (disch := omega) only [cmova_max] at *)
     have hx0 : (T.regs 2).toNat ≤ 64 := by omega
     have hx1 : (T.regs 9).toNat ≤ 64 := by omega
     have hx2 : (T.regs 11).toNat ≤ 64 := by omega
     have hv0 := hU0 hx0
     have hv1 := hU1 hx1
     have hv2 := hU2 hx2
     refine hZero _ (by first | omega | bv_omega) (by omega) (by first | omega | bv_omega)
       ⟨by janus64_simp [hsp, hT4], by janus64_simp [hm2, regFP], by janus64_simp [h14, hT14, regG],
        by janus64_simp [hx15, hTx]⟩
       (by janus64_simp) (by janus64_simp) ⟨by janus64_simp [hTfs, hfs], by janus64_simp [hTdf, hdf, hdf0], L1, b1, hext,
        by omega, ?_, ?_, ?_⟩
     · dsimp only; (try rw [hTm]); first | exact hinv | exact RtInv.inv_congr hinv rfl (by janus64_simp) rfl
     · dsimp only; (try rw [hTm]); exact hMF
     · dsimp only; (try rw [hTm]); exact hLF)
  | ((try simp (disch := omega) only [cmova_max] at *)
     have hx0 : (T.regs 2).toNat ≤ 64 := by omega
     have hx1 : (T.regs 9).toNat ≤ 64 := by omega
     have hx2 : (T.regs 11).toNat ≤ 64 := by omega
     have hv0 := hU0 hx0
     have hv1 := hU1 hx1
     have hv2 := hU2 hx2
     refine hk _ (by janus64_simp) (by janus64_simp [hTm]) (by janus64_simp [hT4]) (by janus64_simp [hT14])
       (by janus64_simp [hT5]) (by janus64_simp [hTx]) (by janus64_simp [hTfs, hfs]) (by janus64_simp [hTdf, hdf])
       (by omega) (by omega) (by omega) (by first | omega | bv_omega) (by janus64_simp; omega) (by janus64_simp; omega)
       (by janus64_simp; omega) ?_ ?_ ?_ <;>
     (janus64_simp <;> (try simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]) <;> (try split) <;> omega))
end FvModexp.Amd64.Run
