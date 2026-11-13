import FvModexp.Proofs.Arm64.Exp.MontLDefs

/-!
# `nat.montgomery` (arm64): one iteration of the main loop (the `succ` step of `MontLoop.loop`), nat.go:199-211
(split out of `MontLoop`, agent expmc s61)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.MontHyp

namespace FvModexp.Arm64.MontLoop

open FvModexp.Exp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem step (impl : List Segment) (R : RtInv)
    (hamv : Summary0 (LibMont.program.link impl) (segAddr LibMont.program amvFn) AmvPre AmvQ)
    (hsub : Summary0 (LibMont.program.link impl) (segAddr LibMont.program subFn) SubPre SubQ)
    (hmv : MemmoveLive (LibMont.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (ret : Nat) (hret : RetAddr (LibMont.program.link impl) ret) (s : State) (L : List (Nat × Nat)) (b : Nat)
    (sp zp cap xp xc yp mp mc k n : Nat) (M0 : Memory)
    (hsps : s.sp.toNat = sp + 192)
    (hal : sp % 16 = 0) (hsp4 : 4096 ≤ sp) (hsp48 : sp + 312 ≤ 2 ^ 48)
    (hacc : M0.accessible (sp - 4096) (4096 + 312) true = true)
    (hn : 0 < n) (hn2 : 2 * n ≤ cap) (hcap : cap < 2 ^ 40) (hxc : xc < 2 ^ 64) (hmc : n ≤ mc) (hmc' : mc < 2 ^ 40)
    (hk : k < 2 ^ 64)
    (hzp : zp + 8 * cap ≤ 2 ^ 48) (hzacc : M0.accessible zp (8 * cap) true = true)
    (hxacc : M0.accessible xp (8 * n) false = true) (hxp : xp + 8 * n ≤ 2 ^ 48)
    (hyacc : M0.accessible yp (8 * n) false = true) (hyp : yp + 8 * n ≤ 2 ^ 48)
    (hmacc : M0.accessible mp (8 * n) false = true) (hmp : mp + 8 * n ≤ 2 ^ 48)
    (hzx : Apart zp (8 * cap) xp (8 * n)) (hzy : Apart zp (8 * cap) yp (8 * n)) (hzm : Apart zp (8 * cap) mp (8 * n))
    (hzs : Apart zp (8 * cap) (sp - 4096) (4096 + 312))
    (hxs : Apart xp (8 * n) (sp - 4096) (4096 + 312)) (hys : Apart yp (8 * n) (sp - 4096) (4096 + 312))
    (hms : Apart mp (8 * n) (sp - 4096) (4096 + 312))
    (r104 : M0.readLE (sp + 104) 8 = 2 * n) (r112 : M0.readLE (sp + 112) 8 = cap) (r168 : M0.readLE (sp + 168) 8 = zp)
    (r224 : M0.readLE (sp + 224) 8 = xp) (r232 : M0.readLE (sp + 232) 8 = n) (r240 : M0.readLE (sp + 240) 8 = xc)
    (r248 : M0.readLE (sp + 248) 8 = yp) (r272 : M0.readLE (sp + 272) 8 = mp) (r280 : M0.readLE (sp + 280) 8 = n)
    (r288 : M0.readLE (sp + 288) 8 = mc) (r296 : M0.readLE (sp + 296) 8 = k) (r304 : M0.readLE (sp + 304) 8 = n)
    (hret0 : M0.readLE sp 8 = ret) (hfp : M0.readLE (sp - 8) 8 = (s.regs 29).toNat)
    (hg : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hgacc : M0.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hgs : Apart ((s.regs 28).toNat + 16) 8 (sp - 4096) (4096 + 312)) (hgz : Apart ((s.regs 28).toNat + 16) 8 zp (8 * cap))
    (hguard : M0.readLE ((s.regs 28).toNat + 16) 8 + 4096 < sp)
    (hgrt : Outside ((s.regs 28).toNat + 16) 8 R.rt)
    (hwin : Outside (sp - 4096) (4096 + 312) R.rt) (hzh : InRanges zp (8 * cap) L ∨ Outside zp (8 * cap) R.rt)
    (hLs : LiveSep L [(sp - 4096, sp + 312)])
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L M0))
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, zp + n * 8, 8 * n])
    (r : Nat) (ih : Inv impl R ret s L b sp zp cap xp xc yp mp mc k n M0 r) :
    Inv impl R ret s L b sp zp cap xp xc yp mp mc k n M0 (r + 1) := by
  unfold Inv at ih ⊢
  intro S i c M hir hpc hsp h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h18 h28 hmem hF hval hcv
  have hi : i < n := by omega
  have hc1 : c ≤ 1 := hcv ▸ FvModexp.Expmc.montIter_c_le _ _ _ _ _ _
  janus_run [r104, r112, r168, r224, r232, r240, r248, r272, r280, r288, r296, r304,
    FvModexp.mask_sub_lt i cap (by omega) (by omega), amvVal] until [segAddr LibMont.program fn + 0x248] calls [hamv]
  rename_i m1 V1 C2 F1 _ _ _ _ m2 V2 C3 F2
  have hzs' := hzs
  unfold Apart at hzs'
  have hl1 : m1.readLE zp (8 * i) = M.readLE zp (8 * i) := by
    rw [F1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
  have hr1 : m1.readLE (zp + 8 * (i + n)) (8 * (2 * n - (i + n))) = M.readLE (zp + 8 * (i + n)) (8 * (2 * n - (i + n))) := by
    rw [F1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
  have hl2 : m2.readLE zp (8 * i) = m1.readLE zp (8 * i) := by
    rw [F2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
  have hr2 : m2.readLE (zp + 8 * (i + n)) (8 * (2 * n - (i + n))) = m1.readLE (zp + 8 * (i + n)) (8 * (2 * n - (i + n))) := by
    rw [F2.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
  have hZ1 := FvModexp.Expmc.readLE_setWin zp i n (2 * n) _ (by omega) hl1 hr1 rfl
  have hZ2 := FvModexp.Expmc.readLE_setWin zp i n (2 * n) _ (by omega) hl2 hr2 rfl
  have e0 := (FvModexp.Expmc.readLE_win M zp i n (2 * n) (by omega)).symm
  have e4 : win (m1.readLE zp (8 * (2 * n))) i n = m1.readLE (zp + 8 * i) (8 * n) :=
    (FvModexp.Expmc.readLE_win m1 zp i n (2 * n) (by omega)).symm
  have e5 : wd (m1.readLE zp (8 * (2 * n))) i = m1.readLE (zp + i * 8) 8 := by
    rw [← FvModexp.Expmc.readLE_wd m1 zp i (2 * n) (by omega), Nat.mul_comm i 8]
  have hstep := FvModexp.Expmc.montStep_eq n (M0.readLE xp (8 * n)) (M0.readLE mp (8 * n)) k
    (M0.readLE (yp + i * 8) 8) i (M.readLE zp (8 * (2 * n))) c _ _ (m1.readLE (sp + 96) 8) _ _ (m2.readLE (sp + 96) 8) _ _ e0
    (by rw [V1, FvModexp.Expmc.B_pow]) (by rw [C2, FvModexp.Expmc.B_pow]) hZ1 e4 e5
    (by rw [V2, FvModexp.Expmc.B_pow, B_eq]) (by rw [C3, FvModexp.Expmc.B_pow, B_eq]) hZ2
  have hpair : montIter n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k i =
      (M.readLE zp (8 * (2 * n)), c) := Prod.ext hval.symm hcv.symm
  have hd : wd (M0.readLE yp (8 * n)) i = M0.readLE (yp + i * 8) 8 := by
    rw [← FvModexp.Expmc.readLE_wd M0 yp i n hi, Nat.mul_comm i 8]
  have hsucc : montIter n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k (i + 1) =
      montStep n (M0.readLE xp (8 * n)) (M0.readLE mp (8 * n)) k (M0.readLE (yp + i * 8) 8) i
        (M.readLE zp (8 * (2 * n)), c) := by
    simp only [montIter]; rw [hpair, hd]
  rw [hstep] at hsucc
  clear hstep hpair hd e0 e4 e5 V1 V2
  janus_run [r104, r112, r168, r224, r232, r240, r248, r272, r280, r288, r296, r304] until [head]
  all_goals first
    | (apply ih _ (i + 1) 1 _ (by omega) <;> first | rfl | (janus_simp; done) | exact FvModexp.Expmc.succ_reg i | (simp only [loopWs]; janus_frame) | (rw [hsucc]; exact FvModexp.Expmc.final_val m2 zp n i c _ _ hi) | (rw [hsucc]; simp only [B_eq]; split <;> omega))
    | (apply ih _ (i + 1) 0 _ (by omega) <;> first | rfl | (janus_simp; done) | exact FvModexp.Expmc.succ_reg i | (simp only [loopWs]; janus_frame) | (rw [hsucc]; exact FvModexp.Expmc.final_val m2 zp n i c _ _ hi) | (rw [hsucc]; simp only [B_eq]; split <;> omega))


end FvModexp.Arm64.MontLoop
