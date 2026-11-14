import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Amd64.Exp.W2Seg
import FvModexp.Proofs.Amd64.Exp.W2ZmDefs

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `z = z.make(2 * numWords)` (nat.go:1425, nat.go:58-69; agent expmc s48)

From the power-table loop exit (fn+0xb05) to the join fn+0xb53 (AX = z, DX = cap z). Reuse when `2n ≤ cap z`
(`[sp+0x2b8]`, the caller's `z.cap`), else `makeslice(Word, 2n, 2n+4)` (return fn+0xb46; `2n+4` spilled to 0x88).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf)

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem zm1 (impl : List Amd64.Segment) {R : RtInv}
    (hmk : MakesliceLiveContract64 (LibW.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    {ret : W64} {Q : State → Prop}
    (b : Nat) (L : List (Nat × Nat)) (g fs sp n zp zc : Nat) (M : Memory) (r5 : W64)
    (he : Env R L g fs sp M) (hn : 0 < n) (hn16 : n ≤ 2 ^ 16) (hzc : zc < 2 ^ 40)
    (hz : 2 * n ≤ zc → Buf R L g fs sp n M zp zc ∧ zp % 8 = 0)
    (hd : Extracted.program.DataLoaded M)
    (r3d0 : M.readLE (sp + 0x2b8) 8 = zc) (r3c0 : M.readLE (sp + 0x2a8) 8 = zp) (r3b0 : M.readLE (sp + 0x298) 8 = n)
    (r78 : M.readLE (sp + 0x78) 8 = 2 * n)
    (hok : zc < 2 * n → R.ok (Extracted.program.contractAddr "runtime.makeslice") [wT, 2 * n, 2 * n + 4] ∧
      blockSize (8 * (2 * n + 4)) true ≤ b)
    (hinv : R.inv b L g (view R.rt L M)) (hacc2 : M.accessible (sp + 0x2a8) 0x20 false = true)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6213381) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (K1 : ∀ (S' : State) (zp' zc' : Nat) (L' : List (Nat × Nat)) (b' : Nat),
      S'.rip = BitVec.ofNat 64 6213459 → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 0 = BitVec.ofNat 64 zp' → S'.regs 2 = BitVec.ofNat 64 zc' → S'.regs 3 = BitVec.ofNat 64 (2 * n) →
      ZPost R L L' b b' g fs sp n M S'.mem (zw1 sp) zp zc zp' zc' →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have he0 := he
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hfs1, hfacc, hfrd, hfw, hfrt, hadx⟩ := he0
  have hlt : (BitVec.ofNat 64 zc).toInt < (BitVec.ofNat 64 (2 * n)).toInt ↔ zc < 2 * n := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega), BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  by_cases hr : 2 * n ≤ zc
  · obtain ⟨hB, hz8⟩ := hz hr
    have hlt' : ((BitVec.ofNat 64 zc).toInt < (BitVec.ofNat 64 (2 * n)).toInt) = False := by
      simp only [hlt, eq_iff_iff, iff_false]; omega
    refine SegProg.lift W2Seg.codeIn (r := BitVec.ofNat 64 6213459) ?_
    janus64_run [r3d0, r3c0, r3b0, r78, hlt'] until [6213459]
    refine K1 _ zp zc L b rfl ?_ ?_ ?_ hfs ?_ rfl ?_ ?_ ?_ ⟨he, hB, hz8, LiveExt.refl R L, by omega, MemFrame.refl _ _,
      LiveFrame.refl _ _ _, hinv, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    all_goals first | exact hsp | exact h5 | exact h14 | exact hx15 | rfl
  · have hr' : zc < 2 * n := by omega
    obtain ⟨hok1, hbs⟩ := hok hr'
    have hlt' : ((BitVec.ofNat 64 zc).toInt < (BitVec.ofNat 64 (2 * n)).toInt) = True := by
      simp only [hlt, eq_iff_iff, iff_true]; omega
    have hwt : Apart wT 16 (sp - 4296) (4296 + 0x2a8) := apart_of_data hd 1 (by decide) (by decide) hwacc
    janus_eval_nat h_t : wT
    rw [h_t] at hok1 hwt
    unfold Apart at hwt
    obtain ⟨hwa, hws, hwp⟩ := FvModexp.Amd64.wordT_data hd
    rw [show 2 * n + 4 = n + (n + 4) by omega] at hok1 hbs
    have hbs' : blockSize (8 * (n + (n + 4))) (0 == 0) ≤ b := hbs
    have hLs' : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
        ([(sp - 8 - 4096, sp - 8), (sp - 8 + 8, sp - 8 + 8 + 24)] ++ [(sp - 8, sp - 8 + 8)]) := by
      intro r hr
      have := hLs r hr
      simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
      omega
    janus64_run [r3d0, r3c0, r3b0, r78, hlt', hws, hwp, BitVec.msb_eq_decide] until [6213459] calls [hmk.pos]
    rename_i ptr _ _ _ _ m _ _ hLF hMF hAp hIn hle hacc h8 _ _ hsz _ hinv' _ _
    have hw : MemFrame M ((M.writeLE (sp + 136) 8 (n + (n + 4))).writeLE (sp - 8) 8 6213446)
        [(sp + 136, sp + 144), (sp - 8, sp)] :=
      ((MemFrame.refl M _).writeLE_inRanges _ ⟨(sp + 136, sp + 144), by simp, by simp only; omega,
        by simp only; omega⟩).writeLE_inRanges _ ⟨(sp - 8, sp), by simp, by simp only; omega, by simp only; omega⟩
    have hLw : LiveFrame M ((M.writeLE (sp + 136) 8 (n + (n + 4))).writeLE (sp - 8) 8 6213446) L [] :=
      ((LiveFrame.refl _ _ _).writeLE _ (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))).writeLE _
        (FvModexp.Expmc.outside_of_liveSep hLs (by omega) (by omega))
    have hP := fresh_post (zp := zp) (zc := zc) (zw := zw1 sp) (by simp) (zw1_in sp) he hn16 hw hLw
      (fun a k ho => by simp only [zw1, outside_cons, outside_nil, and_true] at ho ⊢; omega) hLF hrg1 hMF hAp hIn hle
      hacc (h8 (Or.inr (by omega))) (by omega) (by rw [show 2 * n + 4 = n + (n + 4) by omega]) hinv'
    rw [show 2 * n + 4 = n + (n + 4) by omega] at hP
    refine K1 _ ptr.toNat (n + (n + 4)) _ _ rfl ?_ ?_ ?_ hfs ?_ rfl ?_ ?_ ?_ hP
    all_goals simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true,
      getD_cons_zero, or_self, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    all_goals first | exact hsp | exact h5 | exact h14 | exact BitVec.sub_add_cancel _ _ | rfl

end FvModexp.Amd64.W2Pro
