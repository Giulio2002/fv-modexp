import FvModexp.Proofs.Arm64.Exp.MontExit
import FvModexp.Proofs.Arm64.Exp.MontBody
import FvModexp.Proofs.Common.MaskWord
import FvModexp.Proofs.Common.ExpmcWin
import FvModexp.Proofs.Common.ExpmcFrame

/-!
# `nat.montgomery` (arm64): one iteration of the main loop, nat.go:199-211

```go
for i := 0; i < n; i++ {
	d := y[i]
	c2 := addMulVVWW(z[i:n+i], z[i:n+i], x, d, 0)
	t := z[i] * k
	c3 := addMulVVWW(z[i:n+i], z[i:n+i], m, t, 0)
	cx := c + c2
	cy := cx + c3
	z[n+i] = cy
	if cx < c2 || cy < c3 { c = 1 } else { c = 0 }
}
```
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.MontHyp

namespace FvModexp.Arm64.MontLoop

open FvModexp.Exp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem loop (impl : List Segment) (R : RtInv)
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
    (hok : R.ok (Extracted.program.contractAddr "runtime.memmove") [zp, zp + n * 8, 8 * n]) :
    ∀ (r : Nat) (S : State) (i c : Nat) (M : Memory), i + r = n →
    S.pc = BitVec.ofNat 64 head → S.sp = BitVec.ofNat 64 sp →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 (2 * n) → S.regs 2 = BitVec.ofNat 64 cap →
    S.regs 3 = BitVec.ofNat 64 xp → S.regs 4 = BitVec.ofNat 64 n → S.regs 5 = BitVec.ofNat 64 xc →
    S.regs 6 = BitVec.ofNat 64 yp → S.regs 7 = BitVec.ofNat 64 i → S.regs 8 = BitVec.ofNat 64 c →
    S.regs 9 = BitVec.ofNat 64 mp → S.regs 10 = BitVec.ofNat 64 n → S.regs 11 = BitVec.ofNat 64 mc →
    S.regs 12 = BitVec.ofNat 64 k → S.regs 13 = BitVec.ofNat 64 n →
    S.regs 18 = s.regs 18 → S.regs 28 = s.regs 28 → S.mem = M →
    MemFrame M0 M (loopWs zp n sp) →
    M.readLE zp (8 * (2 * n)) = (montIter n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k i).1 →
    c = (montIter n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k i).2 →
    Reaches ((LibMont.program.link impl).withExit ret) S (IsReturn fun s' =>
      LoopPost R L b s sp zp cap n (M0.readLE xp (8 * n)) (M0.readLE yp (8 * n)) (M0.readLE mp (8 * n)) k M0 s') := by
  intro r
  induction r with
  | zero =>
    intro S i c M hir hpc hsp h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h18 h28 hmem hF hval hcv
    have hin : i = n := by omega
    subst i
    have hc1 : c ≤ 1 := hcv ▸ FvModexp.Expmc.montIter_c_le _ _ _ _ _ _
    -- reads through the loop frame
    have hwo : ∀ a k, sp - 4096 ≤ a → a + k ≤ sp + 312 → (a + k ≤ sp + 8 ∨ sp + 104 ≤ a) →
        (a + k ≤ sp + 128 ∨ sp + 168 ≤ a) → (a + k ≤ sp + 176 ∨ sp + 184 ≤ a) → Outside a k (loopWs zp n sp) := by
      intro a k h1 h2 h3 h4 h5
      have := hzs; unfold Apart at this
      simp only [loopWs, outside_cons, outside_nil, and_true]; omega
    have hfo : ∀ a k, Apart a k zp (8 * cap) → Apart a k (sp - 4096) (4096 + 312) → Outside a k (loopWs zp n sp) := by
      intro a k h1 h2
      unfold Apart at h1 h2
      simp only [loopWs, outside_cons, outside_nil, and_true]; omega
    have eA : ∀ a k w, M.accessible a k w = M0.accessible a k w := hF.accessible
    have hinvM : R.inv b L (s.regs 28).toNat (view R.rt L M) := by
      refine FvModexp.Expmc.inv_frame hF (fun r hr => ?_) hinv
      simp only [loopWs, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hzh.imp (fun h => h.sub (Nat.le_refl _) (by omega)) (fun h => h.of_sub (Nat.le_refl _) (by omega))
      all_goals exact Or.inr (hwin.of_sub (by omega) (by omega))
    refine Reaches.mono (MontExit.exit impl R hsub hmv ret hret s L b S sp zp cap xp xc mp mc k n c M hpc hsp hsps
      h0 h1 h2 h7 h8 h9 h10 h11 h13 h18 h28 hmem hal hsp4 hsp48 (by rw [eA]; exact hacc)
      (by rw [hF.readLE _ _ (hwo (sp) 8 (by omega) (by omega) (by omega) (by omega) (by omega))]; exact hret0)
      (by rw [hF.readLE _ _ (hwo (sp - 8) 8 (by omega) (by omega) (by omega) (by omega) (by omega))]; exact hfp)
      hn hn2 hcap hc1 hmc hmc' hzp (by rw [eA]; exact hzacc) (by rw [eA]; exact hmacc) hmp hzm hzs hms
      (by rw [hF.readLE _ _ (hwo (sp + 112) 8 (by omega) (by omega) (by omega) (by omega) (by omega))]; exact r112)
      (by rw [hF.readLE _ _ (hwo (sp + 168) 8 (by omega) (by omega) (by omega) (by omega) (by omega))]; exact r168)
      (by rw [hF.readLE _ _ (hwo (sp + 304) 8 (by omega) (by omega) (by omega) (by omega) (by omega))]; exact r304)
      hg (by rw [eA]; exact hgacc) hgs hgz
      (by rw [hF.readLE _ _ (hfo _ _ hgz hgs)]; exact hguard) hgrt hwin hzh hLs hinvM hok) ?_
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
        obtain ⟨hrt, hw, hw2, hz⟩ := hk
        exact ⟨⟨by omega, by omega, by omega, by omega⟩, hrt, by omega, by omega, by omega⟩
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
  | succ r ih => exact step impl R hamv hsub hmv ret hret s L b sp zp cap xp xc yp mp mc k n M0 hsps hal hsp4 hsp48 hacc hn hn2 hcap hxc hmc hmc' hk hzp hzacc hxacc hxp hyacc hyp hmacc hmp hzx hzy hzm hzs hxs hys hms r104 r112 r168 r224 r232 r240 r248 r272 r280 r288 r296 r304 hret0 hfp hg hgacc hgs hgz hguard hgrt hwin hzh hLs hinv hok r ih

end FvModexp.Arm64.MontLoop
