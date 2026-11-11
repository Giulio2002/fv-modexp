import FvModexp.Proofs.Amd64.Exp.MontExit
import FvModexp.Proofs.Common.MaskWord
import FvModexp.Proofs.Common.ExpmcWin
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# `nat.montgomery` (amd64): the main loop, nat.go:199-211 (see the arm64 twin)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts
open FvModexp.Amd64.MontHyp FvModexp.Exp

namespace FvModexp.Amd64.MontLoop

/-- What one iteration writes: `z`, the pushed return address and the call frame `[sp-8, sp+0x60)`, the spills
`[sp+0x78, sp+0xa0)`, `[sp+0xa8, sp+0xb0)`. -/
abbrev loopWs (zp n sp : Nat) : List (Nat × Nat) :=
  [(zp, zp + 16 * n), (sp - 8, sp + 0x60), (sp + 0x78, sp + 0xa0), (sp + 0xa8, sp + 0xb0)]

/-- What the loop (with the exit path) guarantees, relative to the memory `M0` at the first arrival at the head. -/
abbrev LoopPost (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (s : State) (sp zp cap n X Y Mv k : Nat) (M0 : Memory)
    (s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
  s'.regs 0 = BitVec.ofNat 64 zp ∧ s'.regs 3 = BitVec.ofNat 64 n ∧ s'.regs 1 = BitVec.ofNat 64 cap ∧
  s'.mem.readLE zp (8 * n) = montgomery n X Y Mv k ∧
  R.inv b L (s.regs 14).toNat (view R.rt L s'.mem) ∧
  MemFrame M0 s'.mem (R.rt ++ [(sp - 4104, sp + 288), (zp, zp + 16 * n)]) ∧
  LiveFrame M0 s'.mem L [(zp, zp + 16 * n)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem loop (impl : List Amd64.Segment) (R : RtInv)
    (hamv : Summary0 (LibMont.program.link impl) (segAddr LibMont.program amvFn) AmvPre AmvQ)
    (hsub : Summary0 (LibMont.program.link impl) (segAddr LibMont.program subFn) SubPre SubQ)
    (hmv : MemmoveLive64 (LibMont.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibMont.program.link impl) ret) (s : State) (L : List (Nat × Nat)) (b : Nat)
    (sp zp cap xp xc yp mp mc k n : Nat) (M0 : Memory)
    (hsps : (s.regs 4).toNat = sp + 0xb8) (hx15 : s.xmm 15 = 0#128)
    (hal : sp % 8 = 0) (hsp4 : 4104 ≤ sp) (hsp48 : sp + 288 ≤ 2 ^ 48)
    (hacc : M0.accessible (sp - 4104) (4104 + 288) true = true)
    (hn : 0 < n) (hn2 : 2 * n ≤ cap) (hcap : cap < 2 ^ 40) (hxc : xc < 2 ^ 64) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40)
    (hk : k < 2 ^ 64)
    (hzp : zp + 8 * cap ≤ 2 ^ 48) (hzacc : M0.accessible zp (8 * cap) true = true)
    (hxacc : M0.accessible xp (8 * n) false = true) (hxp : xp + 8 * n ≤ 2 ^ 48)
    (hyacc : M0.accessible yp (8 * n) false = true) (hyp : yp + 8 * n ≤ 2 ^ 48)
    (hmacc : M0.accessible mp (8 * n) false = true) (hmp : mp + 8 * n ≤ 2 ^ 48)
    (hadx : M0.accessible hasADX 1 false = true)
    (hzx : Apart zp (8 * cap) xp (8 * n)) (hzy : Apart zp (8 * cap) yp (8 * n)) (hzm : Apart zp (8 * cap) mp (8 * n))
    (hzs : Apart zp (8 * cap) (sp - 4104) (4104 + 288))
    (hxs : Apart xp (8 * n) (sp - 4104) (4104 + 288)) (hys : Apart yp (8 * n) (sp - 4104) (4104 + 288))
    (hms : Apart mp (8 * n) (sp - 4104) (4104 + 288))
    (r60 : M0.readLE (sp + 0x60) 8 = 2 * n) (r68 : M0.readLE (sp + 0x68) 8 = cap) (ra0 : M0.readLE (sp + 0xa0) 8 = zp)
    (rc0 : M0.readLE (sp + 0xc0) 8 = mp) (rc8 : M0.readLE (sp + 0xc8) 8 = n) (rd0 : M0.readLE (sp + 0xd0) 8 = mc)
    (rd8 : M0.readLE (sp + 0xd8) 8 = k) (re0 : M0.readLE (sp + 0xe0) 8 = n) (r100 : M0.readLE (sp + 0x100) 8 = xp)
    (r108 : M0.readLE (sp + 0x108) 8 = n) (r110 : M0.readLE (sp + 0x110) 8 = xc) (r118 : M0.readLE (sp + 0x118) 8 = yp)
    (hret0 : M0.readLE (sp + 0xb8) 8 = ret) (hbp : M0.readLE (sp + 0xb0) 8 = (s.regs 5).toNat)
    (htb : 8 ≤ s.fsBase.toNat ∧ s.fsBase.toNat ≤ 2 ^ 48) (htr : M0.accessible (s.fsBase.toNat - 8) 8 false = true)
    (htg : M0.readLE (s.fsBase.toNat - 8) 8 = (s.regs 14).toNat)
    (hts : Apart (s.fsBase.toNat - 8) 8 (sp - 4104) (4104 + 288)) (htz : Apart (s.fsBase.toNat - 8) 8 zp (8 * cap))
    (hg : (s.regs 14).toNat + 24 ≤ 2 ^ 48) (hgacc : M0.accessible ((s.regs 14).toNat + 16) 8 false = true)
    (hgs : Apart ((s.regs 14).toNat + 16) 8 (sp - 4104) (4104 + 288)) (hgz : Apart ((s.regs 14).toNat + 16) 8 zp (8 * cap))
    (hguard : M0.readLE ((s.regs 14).toNat + 16) 8 + 4104 < sp)
    (hgrt : Outside ((s.regs 14).toNat + 16) 8 R.rt)
    (hwin : Outside (sp - 4104) (4104 + 288) R.rt) (hzh : InRanges zp (8 * cap) L ∨ Outside zp (8 * cap) R.rt)
    (hLs : LiveSep L [(sp - 4104, sp + 288)])
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L M0))
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, zp + n * 8, n * 8]) :
    ∀ (r : Nat) (S : State) (i c : Nat) (M : Memory), i + r = n →
    S.rip = BitVec.ofNat 64 head → S.regs 4 = BitVec.ofNat 64 sp →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 cap → S.regs 2 = BitVec.ofNat 64 n →
    S.regs 3 = BitVec.ofNat 64 n → S.regs 6 = BitVec.ofNat 64 n → S.regs 7 = BitVec.ofNat 64 xp →
    S.regs 8 = BitVec.ofNat 64 xc → S.regs 9 = BitVec.ofNat 64 yp → S.regs 10 = BitVec.ofNat 64 (2 * n) →
    S.regs 11 = BitVec.ofNat 64 i → S.regs 12 = BitVec.ofNat 64 c →
    S.regs 14 = s.regs 14 → S.xmm 15 = s.xmm 15 → S.df = false → S.fsBase = s.fsBase → S.mem = M →
    MemFrame M0 M (loopWs zp n sp) →
    M.readLE zp (8 * (2 * n)) = (montIter n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k i).1 →
    c = (montIter n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k i).2 →
    Amd64.Tactic.Reaches ((LibMont.program.link impl).withExit ret) S (IsReturn fun s' =>
      LoopPost R L b s sp zp cap n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k M0 s') := by
  intro r
  induction r with
  | zero =>
    intro S i c M hir hpc hsp h0 h1 h2 h3 h6 h7 h8 h9 h10 h11 h12 h14 h15 hdf hfs hmem hF hval hcv
    have hin : i = n := by omega
    subst i
    have hc1 : c ≤ 1 := hcv ▸ FvModexp.Expmc.montIter_c_le _ _ _ _ _ _
    have hwo : ∀ a k, sp - 4104 ≤ a → a + k ≤ sp + 288 → (a + k ≤ sp - 8 ∨ sp + 0x60 ≤ a) →
        (a + k ≤ sp + 0x78 ∨ sp + 0xa0 ≤ a) → (a + k ≤ sp + 0xa8 ∨ sp + 0xb0 ≤ a) → Outside a k (loopWs zp n sp) := by
      intro a k h1 h2 h3 h4 h5
      have := hzs; unfold Apart at this
      simp only [loopWs, outside_cons, outside_nil, and_true]; omega
    have hfo : ∀ a k, Apart a k zp (8 * cap) → Apart a k (sp - 4104) (4104 + 288) → Outside a k (loopWs zp n sp) := by
      intro a k h1 h2
      unfold Apart at h1 h2
      simp only [loopWs, outside_cons, outside_nil, and_true]; omega
    have eA : ∀ a k w, M.accessible a k w = M0.accessible a k w := hF.accessible
    have hinvM : R.inv b L (s.regs 14).toNat (view R.rt L M) := by
      refine FvModexp.Expmc.inv_frame hF (fun r hr => ?_) hinv
      simp only [loopWs, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hzh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
      all_goals exact Or.inr (hwin.of_sub (by omega) (by omega))
    have rd : ∀ a v, sp - 4104 ≤ a → a + 8 ≤ sp + 288 → (a + 8 ≤ sp - 8 ∨ sp + 0x60 ≤ a) →
        (a + 8 ≤ sp + 0x78 ∨ sp + 0xa0 ≤ a) → (a + 8 ≤ sp + 0xa8 ∨ sp + 0xb0 ≤ a) → M0.readLE a 8 = v →
        M.readLE a 8 = v := fun a v h1 h2 h3 h4 h5 h => by rw [hF.readLE _ _ (hwo a 8 h1 h2 h3 h4 h5)]; exact h
    rw [← hfs] at htb htr htg hts htz
    refine Amd64.Tactic.Reaches.mono (MontExit.exit (impl := impl) (R := R) (hsub := hsub) (hmv := hmv) (ret := ret)
      (hret := hret) (s := s) (L := L) (b := b) (S := S) (sp := sp) (zp := zp) (cap := cap) (mp := mp) (mc := mc)
      (n := n) (c := c) (M := M) (hpc := hpc) (hsp := hsp) (hsps := hsps) (h0 := h0) (h1 := h1) (h2 := h2) (h3 := h3)
      (h10 := h10) (h11 := h11) (h12 := h12) (h14 := h14) (h15 := h15) (hmem := hmem) (hx15 := hx15) (hdf := hdf)
      (hal := hal) (hsp4 := hsp4) (hsp48 := hsp48) (hacc := by rw [eA]; exact hacc)
      (hret0 := rd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) hret0)
      (hbp := rd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) hbp)
      (hn := hn) (hn2 := hn2) (hcap := hcap) (hc := hc1) (hmc := hmc) (hmc' := hmc') (hzp := hzp)
      (hzacc := by rw [eA]; exact hzacc) (hmacc := by rw [eA]; exact hmacc) (hmp := hmp) (hzm := hzm) (hzs := hzs)
      (hms := hms)
      (r68 := rd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) r68)
      (ra0 := rd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) ra0)
      (rc0 := rd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) rc0)
      (rd0 := rd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) rd0)
      (re0 := rd _ _ (by omega) (by omega) (by omega) (by omega) (by omega) re0)
      (htb := htb) (htr := by rw [eA]; exact htr) (htg := by rw [hF.readLE _ _ (hfo _ _ htz hts)]; exact htg)
      (hts := hts) (htz := htz) (hg := hg) (hgacc := by rw [eA]; exact hgacc) (hgs := hgs) (hgz := hgz)
      (hguard := by rw [hF.readLE _ _ (hfo _ _ hgz hgs)]; exact hguard) (hgrt := hgrt) (hwin := hwin) (hzh := hzh)
      (hLs := hLs) (hinv := hinvM) (hok := hok)) ?_
    intro o ho
    cases o with
    | stub _ _ _ => exact ho.elim
    | returned s' =>
      simp only [isReturn_returned] at ho ⊢
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, ev, ei, ef, el⟩ := ho
      refine ⟨e1, e2, e3, e4, e5, e6, e7, ?_, ei, ?_, ?_⟩
      · rw [ev, hcv, hF.readLE _ _ (hfo _ _ (hzm.symm) hms),
          FvModexp.Expmc.readLE_win M zp n n (2 * n) (by omega), hval]
        unfold montgomery
        rw [FvModexp.Expmc.B_pow]
      · refine hF.trans ef (fun a k hk => ?_)
        simp only [loopWs, outside_append, outside_cons, outside_nil, and_true] at hk ⊢
        obtain ⟨hrt, hw, hz⟩ := hk
        exact ⟨⟨by omega, by omega, by omega, by omega⟩, hrt, by omega, by omega⟩
      · refine (FvModexp.Expmc.liveFrame_of_frame hF ?_).trans
          (FvModexp.Expmc.liveFrame_widen el ?_) (fun _ _ h => h)
        · intro a k hin hout
          obtain ⟨r, hr, h1, h2⟩ := hin
          have := hLs r hr
          simp only [loopWs, outside_cons, outside_nil, and_true] at this hout ⊢
          omega
        · intro a k h
          simp only [outside_cons, outside_nil, and_true] at h ⊢
          omega
  | succ r ih =>
    intro S i c M hir hpc hsp h0 h1 h2 h3 h6 h7 h8 h9 h10 h11 h12 h14 h15 hdf hfs hmem hF hval hcv
    have hi : i < n := by omega
    have hc1 : c ≤ 1 := hcv ▸ FvModexp.Expmc.montIter_c_le _ _ _ _ _ _
    have htb' := htb
    have htr' := htr
    have htg' := htg
    have hts' := hts
    have htz' := htz
    rw [← hfs] at htb' htr' htg' hts' htz'
    janus64_run [r60, r68, ra0, rc0, rc8, rd0, rd8, re0, r100, r108, r110, r118, htg',
      FvModexp.mask_neg_sub_lt (i * 8) i cap (by omega) (by omega) (by omega), amvVal]
      until [segAddr LibMont.program fn + 0x34e] calls [hamv]
    rename_i m1 _ _ V1 C2 F1 _ _ _ _ _ m2 _ _ V2 C3 F2
    have hzs' := hzs
    unfold Apart at hzs'
    have hl1 : m1.readLE zp (8 * i) = M.readLE zp (8 * i) := by
      rw [F1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hr1 : m1.readLE (zp + 8 * (i + n)) (8 * (2 * n - (i + n))) = M.readLE (zp + 8 * (i + n)) (8 * (2 * n - (i + n))) := by
      rw [F1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hl2 : m2.readLE zp (8 * i) = m1.readLE zp (8 * i) := by
      rw [F2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hr2 : m2.readLE (zp + 8 * (i + n)) (8 * (2 * n - (i + n))) = m1.readLE (zp + 8 * (i + n)) (8 * (2 * n - (i + n))) := by
      rw [F2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have ei : zp + i * 8 = zp + 8 * i := by omega
    rw [ei] at V1 V2 C2 C3
    rw [show sp - 8 + 96 = sp + 88 by omega] at C2 C3
    have hZ1 := FvModexp.Expmc.readLE_setWin zp i n (2 * n) _ (by omega) hl1 hr1 rfl
    have hZ2 := FvModexp.Expmc.readLE_setWin zp i n (2 * n) _ (by omega) hl2 hr2 rfl
    have e0 := (FvModexp.Expmc.readLE_win M zp i n (2 * n) (by omega)).symm
    have e4 : win (m1.readLE zp (8 * (2 * n))) i n = m1.readLE (zp + 8 * i) (8 * n) :=
      (FvModexp.Expmc.readLE_win m1 zp i n (2 * n) (by omega)).symm
    have e5 : wd (m1.readLE zp (8 * (2 * n))) i = m1.readLE (zp + 8 * i) 8 :=
      (FvModexp.Expmc.readLE_wd m1 zp i (2 * n) (by omega)).symm
    have hz1lt := Janus.Arm64.Memory.readLE_lt m1 (zp + 8 * i) 8
    rw [FvModexp.Expmc.bv_mul_toNat _ _ (by simpa using hz1lt) hk, ← V1] at V2 C3
    have hstep := FvModexp.Expmc.montStep_eq n (M0.readLE xp (8 * n)) (M0.readLE mp (8 * n)) k
      (M0.readLE (yp + i * 8) 8) i (M.readLE zp (8 * (2 * n))) c _ _ (m1.readLE (sp + 88) 8) _ _
      (m2.readLE (sp + 88) 8) _ _ e0
      (by rw [V1, FvModexp.Expmc.B_pow]) (by rw [C2, FvModexp.Expmc.B_pow]) hZ1 e4 e5
      (by rw [V2, FvModexp.Expmc.B_pow]) (by rw [C3, FvModexp.Expmc.B_pow]) hZ2
    have hpair : montIter n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k i =
        (M.readLE zp (8 * (2 * n)), c) := Prod.ext hval.symm hcv.symm
    have hd : wd (M0.readLE yp (8 * n)) i = M0.readLE (yp + i * 8) 8 := by
      rw [← FvModexp.Expmc.readLE_wd M0 yp i n hi, Nat.mul_comm i 8]
    have hsucc : montIter n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k (i + 1) =
        montStep n (M0.readLE xp (8 * n)) (M0.readLE mp (8 * n)) k (M0.readLE (yp + i * 8) 8) i
          (M.readLE zp (8 * (2 * n)), c) := by
      simp only [montIter]; rw [hpair, hd]
    rw [hstep] at hsucc
    clear hstep hpair hd e0 e4 e5 V1 V2 C2 C3
    have hc2lt : m1.readLE (sp + 88) 8 < 2 ^ 64 := by simpa using Janus.Arm64.Memory.readLE_lt m1 (sp + 88) 8
    have hc3lt : m2.readLE (sp + 88) 8 < 2 ^ 64 := by simpa using Janus.Arm64.Memory.readLE_lt m2 (sp + 88) 8
    janus64_run [r60, r68, ra0, rc0, rc8, rd0, rd8, re0, r100, r108, r110, r118, htg'] until [head]
    all_goals first
      | (apply ih _ (i + 1) 1 _ (by omega) <;> first | rfl | (janus64_simp [hx15]; done) | (dsimp only; exact hfs) | (dsimp only; simp only [loopWs]; janus_frame) | (dsimp only; rw [hsucc]; exact FvModexp.Expmc.final_val_gen m2 zp n i _ _ hi (by simp only [B_eq]; omega)) | (rw [hsucc]; simp only [B_eq]; split <;> omega))
      | (apply ih _ (i + 1) 0 _ (by omega) <;> first | rfl | (janus64_simp [hx15]; done) | (dsimp only; exact hfs) | (dsimp only; simp only [loopWs]; janus_frame) | (dsimp only; rw [hsucc]; exact FvModexp.Expmc.final_val_gen m2 zp n i _ _ hi (by simp only [B_eq]; omega)) | (rw [hsucc]; simp only [B_eq]; split <;> omega))

end FvModexp.Amd64.MontLoop
