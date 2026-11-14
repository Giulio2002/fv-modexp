import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.W2Seg
import FvModexp.Proofs.Amd64.Exp.W2ZmDefs

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `z = z[:n]`, `zz = zz.make(2 * numWords)[:n]` (nat.go:1426-1428; agent expmc s48)

From the join fn+0xb53 (AX = z, DX = cap z, BX = 2n) to `zj` (fn+0xbcf): the bounds check `n ≤ cap z`, the spills
`cap z → 0x88`, `z → 0x170`, then `zz.make(2n)`: reuse when `2n ≤ cap zz` (`[sp+0xa2]`, pointer `[sp+0x190]`), else
`makeslice(Word, 2n, 2n+4)` (return fn+0xbac; `2n+4` spilled to 0x80).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf)

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zm2 (impl : List Amd64.Segment) {R : RtInv}
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    {ret : W64} {Q : State → Prop}
    (b : Nat) (L : List (Nat × Nat)) (g fs sp n zp zc zzp zzc : Nat) (M : Memory) (r5 : W64)
    (he : Env R L g fs sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hzc : n ≤ zc) (hzc' : zc < 2 ^ 40) (hzp : zp < 2 ^ 64)
    (hzzc : zzc < 2 ^ 40)
    (hzz : 2 * n ≤ zzc → Buf R L g fs sp n M zzp zzc ∧ zzp % 8 = 0)
    (hd : Extracted.program.DataLoaded M)
    (r3b0 : M.readLE (sp + 0x298) 8 = n) (ra0 : M.readLE (sp + 0xa0) 8 = zzc) (r188 : M.readLE (sp + 0x190) 8 = zzp)
    (hok : zzc < 2 * n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4] ∧
      blockSize (8 * (2 * n + 4)) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M))
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6213459) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h2 : S.regs 2 = BitVec.ofNat 64 zc) (h3 : S.regs 3 = BitVec.ofNat 64 (2 * n))
    (K2 : ∀ (S' : State) (zzp' zzc' : Nat) (L' : List (Nat × Nat)) (b' : Nat),
      S'.rip = BitVec.ofNat 64 6213583 → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 2 = BitVec.ofNat 64 zc → S'.regs 1 = BitVec.ofNat 64 zzp' →
      S'.regs 12 = BitVec.ofNat 64 zzc' → S'.regs 11 = BitVec.ofNat 64 n →
      ZPost R L L' b b' g fs sp n M S'.mem (zw2 sp) zzp zzc zzp' zzc' →
      S'.mem.readLE (sp + 0x88) 8 = zc → S'.mem.readLE (sp + 0x170) 8 = zp →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  have hlt : (BitVec.ofNat 64 zzc).toInt < (BitVec.ofNat 64 (2 * n)).toInt ↔ zzc < 2 * n := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega), BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have hna : (BitVec.ofNat 64 zc < BitVec.ofNat 64 n) = False := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, eq_iff_iff, iff_false]; omega
  have hw : MemFrame M ((M.writeLE (sp + 136) 8 zc).writeLE (sp + 368) 8 zp) [(sp + 136, sp + 144), (sp + 368, sp + 376)] :=
    ((MemFrame.refl M _).writeLE_inRanges _ ⟨(sp + 136, sp + 144), by simp, by simp only; omega,
      by simp only; omega⟩).writeLE_inRanges _ ⟨(sp + 368, sp + 376), by simp, by simp only; omega, by simp only; omega⟩
  have hLw : LiveFrame M ((M.writeLE (sp + 136) 8 zc).writeLE (sp + 368) 8 zp) L [] :=
    ((LiveFrame.refl _ _ _).writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))).writeLE _
      (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))
  have hz1 : ((M.writeLE (sp + 136) 8 zc).writeLE (sp + 368) 8 zp).readLE (sp + 0x88) 8 = zc := by
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self]; omega
  have hz2 : ((M.writeLE (sp + 136) 8 zc).writeLE (sp + 368) 8 zp).readLE (sp + 0x170) 8 = zp := by
    simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self]; omega
  by_cases hr : 2 * n ≤ zzc
  · obtain ⟨hB, hz8⟩ := hzz hr
    have hlt' : ((BitVec.ofNat 64 zzc).toInt < (BitVec.ofNat 64 (2 * n)).toInt) = False := by
      simp only [hlt, eq_iff_iff, iff_false]; omega
    refine SegProg.lift W2Seg.codeIn (r := BitVec.ofNat 64 6213583) ?_
    janus64_run [r3b0, ra0, r188, hlt', hna] until [6213583]
    have hF : MemFrame M ((M.writeLE (sp + 136) 8 zc).writeLE (sp + 368) 8 zp) (R.rt ++ zw2 sp) :=
      hw.mono (fun a k ho => by simp only [zw2, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega)
    have hgo : Outside (g + 16) 8 (zw2 sp) := out_of_in hgw _ (zw2_in sp)
    have hfo : Outside (fs - 8) 8 (zw2 sp) := out_of_in hfw _ (zw2_in sp)
    refine K2 _ zzp zzc L b rfl ?_ ?_ ?_ hfs ?_ rfl ?_ ?_ ?_ ?_ ?_
      ⟨Env.frame he hF hgo hfo (LiveExt.refl R L), ⟨hB.1, hB.2.1, by rw [hF.accessible]; exact hB.2.2.1, hB.2.2.2⟩,
        hz8, LiveExt.refl R L, by omega, hF, hLw,
        FvModexp.Expmc.inv_writeLE (Or.inr (hwrt.of_sub (by omega) (by omega)))
          (FvModexp.Expmc.inv_writeLE (Or.inr (hwrt.of_sub (by omega) (by omega))) hinv),
        by rw [Arm64.Memory.regions_writeLE, Arm64.Memory.regions_writeLE], Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩ hz1 hz2
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | exact hsp | exact h5 | exact h14 | exact hx15 | exact h0 | exact h2 | rfl
  · have hr' : zzc < 2 * n := by omega
    obtain ⟨hok1, hbs⟩ := hok hr'
    have hlt' : ((BitVec.ofNat 64 zzc).toInt < (BitVec.ofNat 64 (2 * n)).toInt) = True := by
      simp only [hlt, eq_iff_iff, iff_true]; omega
    have hwt : Apart wT 16 (sp - 4296) (4296 + 0x2a8) := apart_of_data hd 1 (by decide) (by decide) hwacc
    janus_eval_nat h_t : wT
    rw [h_t] at hok1 hwt
    unfold Apart at hwt
    obtain ⟨hwa, hws, hwp⟩ := FvModexp.Amd64.wordT_data hd
    rw [show 2 * n + 4 = n + (n + 4) by omega] at hok1 hbs
    have hLs' : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
        ([(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 24)] ++ [(sp - 8, sp - 8 + 8)]) := by
      intro r hr
      have := hLs r hr
      simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
      omega
    refine SegProg.lift W2Seg.codeIn (r := BitVec.ofNat 64 6213543) ?_
    janus64_run [r3b0, ra0, r188, hlt', hna, hws, hwp, BitVec.msb_eq_decide] until [6213543]
    janus64_run [r3b0, ra0, r188, hlt', hna, hws, hwp, BitVec.msb_eq_decide] until [6213548] calls [hmk.pos]
    refine SegProg.lift W2Seg.codeIn (r := BitVec.ofNat 64 6213583) ?_
    janus64_run [r3b0, ra0, r188, hlt', hna, hws, hwp, BitVec.msb_eq_decide] until [6213583]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hsz _ hinv' _ _
    have hw' : MemFrame M ((((M.writeLE (sp + 136) 8 zc).writeLE (sp + 368) 8 zp).writeLE (sp + 128) 8
        (n + (n + 4))).writeLE (sp - 8) 8 6213548) [(sp + 136, sp + 144), (sp + 368, sp + 376), (sp + 128, sp + 136),
          (sp - 8, sp)] :=
      ((hw.mono (fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega)).writeLE_inRanges _
        ⟨(sp + 128, sp + 136), by simp, by simp only; omega, by simp only; omega⟩).writeLE_inRanges _
        ⟨(sp - 8, sp), by simp, by simp only; omega, by simp only; omega⟩
    have hLw' : LiveFrame M ((((M.writeLE (sp + 136) 8 zc).writeLE (sp + 368) 8 zp).writeLE (sp + 128) 8
        (n + (n + 4))).writeLE (sp - 8) 8 6213548) L [] :=
      (hLw.writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))
    have hP := fresh_post (zp := zzp) (zc := zzc) (zw := zw2 sp) (by simp) (zw2_in sp) he hn16 hw' hLw'
      (fun a k ho => by simp only [zw2, outside_cons, outside_nil, and_true] at ho ⊢; omega) hLF hrg1 hMF hAp hIn hle
      hacc (h8 (Or.inr (by omega))) (by omega) (by rw [show 2 * n + 4 = n + (n + 4) by omega]) hinv'
    rw [show 2 * n + 4 = n + (n + 4) by omega] at hP
    have rd : ∀ a, sp + 128 ≤ a → a + 8 ≤ sp + 0x2a8 → m.readLE a 8 = Arm64.Memory.readLE ((((M.writeLE (sp + 136) 8
        zc).writeLE (sp + 368) 8 zp).writeLE (sp + 128) 8 (n + (n + 4))).writeLE (sp - 8) 8 6213548) a 8 := fun a h1 h2 =>
      hMF.readLE _ _ (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨hwrt.of_sub (by omega) (by omega), by omega, by omega⟩)
    refine K2 _ ptr.toNat (n + (n + 4)) _ _ rfl ?_ ?_ ?_ hfs ?_ rfl ?_ ?_ ?_ ?_ ?_ hP ?_ ?_
    · simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte]; exact BitVec.sub_add_cancel _ _
    · simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]; exact h5
    · simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]; exact h14
    · simp
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    · rw [rd _ (by omega) (by omega)]
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self]; omega
    · rw [rd _ (by omega) (by omega)]
      simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self]; omega

end FvModexp.Amd64.W2Pro
