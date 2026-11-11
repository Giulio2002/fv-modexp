import FvModexp.Proofs.Arm64.Nat.BasicSqrDefs
import FvModexp.Proofs.Arm64.Nat.DivmcCall
import FvModexp.Proofs.Common.BitLemmas

/-!
# `basicSqr` (arm64), the small path: `n < basicSqrThreshold` → `basicMul(z, x, x)`; return

Entry → the `CALL basicMul` at `+0x100` (the prologue spills `X1`, `X4` and clears the defer slot / bit, then loads
`basicSqrThreshold`), `basicMul`'s summary (`BasicMul.ens`, its `CallEnv` at `SP' = SP - 208` from ours), the epilogue.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel
open FvModexp.Arm64.RunIface (Serves)

namespace FvModexp.Arm64.BasicSqr

abbrev callBM : Nat := segAddr Extracted.program fn + 0x100

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.janusRenameI false in
theorem small2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hsm : xl.toNat < 12)
    (S : State) (hpcS : S.pc = BitVec.ofNat 64 callBM) (hsp : S.sp = s.sp - 208#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 216#64) (h18 : S.regs 18 = s.regs 18)
    (r0 : S.regs 0 = zp) (r1 : S.regs 1 = zl) (r2 : S.regs 2 = zc) (r3 : S.regs 3 = xp) (r4 : S.regs 4 = xl)
    (r5 : S.regs 5 = xc) (r6 : S.regs 6 = xp) (r7 : S.regs 7 = xl) (r8 : S.regs 8 = xc)
    (hF : MemFrame s.mem S.mem (winA s 4432 64)) (hreg : S.mem.regions = s.mem.regions)
    (hlr : S.mem.readLE (s.sp.toNat - 208) 8 = (s.regs 30).toNat)
    (hfp : S.mem.readLE (s.sp.toNat - 216) 8 = (s.regs 29).toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hc : CodeIn ((Extracted.program.onlySegments BasicMul.names).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hBM := Ensures.toSummaryRegs9 (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 =>
    BasicMul.ens impl hap R hmc b L a0 a1 a2 a3 a4 a5 a6 a7 a8) (noExit_restrict hap BasicMul.names) hc
  clear hc
  simp only [BasicMul.Pre, CallEnv] at hBM
  have hce := hpre.ce; have hsv := hpre.sv; have hx0 := hpre.x0; have hzl := hpre.zl2; have hzc := hpre.zlc
  have hzc40 := hpre.zcb; have hzl' := hpre.zlive; have hzw := hpre.zw; have hzg := hpre.zg
  have hxacc := hpre.xacc; have hx48 := hpre.x48; have hxh := hpre.xh; have hxw := hpre.xw; have hzx := hpre.zx
  have hsp0 : 4432 ≤ s.sp.toNat := hce.2.1.2.1
  have hsp' : S.sp.toNat = s.sp.toNat - 208 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hFw : MemFrame s.mem S.mem (win s 4432 64) := hF.mono fun a n h => by
    simp only [win, winA, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hce1 := CallEnv.callee (stk1 := 4224) (above1 := 72) hce hsp' h28 (by decide) (by decide) (by decide) hFw hreg
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := hce1
  simp only [LiveSep, win, outside_cons, outside_nil, and_true] at hLs
  rw [h28] at hg1 hg2 hg3 hga hgr
  rw [hsp'] at hg3 hga
  unfold Apart at hga
  have hinv : R.inv b L (s.regs 28).toNat (view R.rt L S.mem) :=
    inv_frame_winA hF hce.2.2.2.1 hsp0 (by decide) hpre.inv
  unfold RoOut at hro
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl' (by omega)
  have e2 : 8 * zl.toNat = 8 * (xl.toNat + xl.toNat) := by omega
  simp only [win, outside_cons, outside_nil, and_true] at hzw hxw
  rw [e2] at hzh hzacc hz48 hzw hzx hzg
  have hzaccS : S.mem.accessible zp.toNat (8 * (xl.toNat + xl.toNat)) true = true := by rw [hF.accessible]; exact hzacc
  have hxaccS : S.mem.accessible xp.toNat (8 * xl.toNat) false = true := by rw [hF.accessible]; exact hxacc
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [zp.toNat, 8 * (xl.toNat + xl.toNat)] :=
    hsv.2.2.1 _ _ (by omega)
  clear hFw hzacc hxacc hzl'
  janus_run until [callBM + 4] calls [hBM]
  rename_i _ hsp2 _ _ _ L' b' hext hbb hval hinv2 hF2 hLF2
  have hl4 := hl4; have hl48 := hl48
  have e208 : (s.sp - 208#64).toNat = s.sp.toNat - 208 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  simp only [winA, e208] at hF2
  have hout0 := hce.2.2.2.1
  have hstok := hpre.stok; have hstw := hpre.stw; have hstz := hpre.stz
  have hrd : ∀ a, s.sp.toNat - 216 ≤ a → a + 8 ≤ s.sp.toNat - 200 → s'.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2
    refine hF2.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hout0.of_sub (by omega) (by omega), by omega, by omega⟩, by omega⟩
  have hr1 := (hrd _ (by omega) (by omega)).trans hfp
  have hr2 := (hrd _ (by omega) (by omega)).trans hlr
  janus_run [hr1, hr2]
  -- the caller-visible objects held in `L` outside the window and `z` keep their bytes
  have hkeep : ∀ a n, Held R L a n → Outside a n (win s 4432 64) → Apart a n zp.toNat (8 * (xl.toNat + xl.toNat)) →
      s'.mem.readLE a n = s.mem.readLE a n := by
    intro a n hh hw hz
    simp only [win, outside_cons, outside_nil, and_true] at hw
    unfold Apart at hz
    rw [Held.readLE2 hh hF2 hLF2 (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hF.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  obtain ⟨hst8, hsth, hstacc, hst48, hstnl, hstlc, hstc40⟩ := hstok
  have hstz' : Apart st.toNat 24 zp.toNat (8 * (xl.toNat + xl.toNat)) := by rw [← e2]; exact hstz
  have rW : s'.mem.readLE st.toNat 8 = s.mem.readLE st.toNat 8 :=
    hkeep _ _ (hsth.sub (Nat.le_refl _) (by omega)) (hstw.of_sub (Nat.le_refl _) (by omega))
      (by unfold Apart at hstz' ⊢; omega)
  have rL : s'.mem.readLE (st.toNat + 8) 8 = s.mem.readLE (st.toNat + 8) 8 :=
    hkeep _ _ (hsth.sub (by omega) (by omega)) (hstw.of_sub (by omega) (by omega))
      (by unfold Apart at hstz' ⊢; omega)
  have rC : s'.mem.readLE (st.toNat + 16) 8 = s.mem.readLE (st.toNat + 16) 8 :=
    hkeep _ _ (hsth.sub (by omega) (by omega)) (hstw.of_sub (by omega) (by omega))
      (by unfold Apart at hstz' ⊢; omega)
  have hacc2 : ∀ a n w, s'.mem.accessible a n w = s.mem.accessible a n w := fun a n w => by
    rw [hF2.accessible, hF.accessible]
  have hFall : MemFrame s.mem s'.mem (R.rt ++ winA s 4432 64 ++ ws s.mem st.toNat zp.toNat zl.toNat) :=
    MemFrame.trans hF hF2 fun a n h => by
      simp only [ws, stkWs, winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      refine ⟨⟨h.1.2.1, h.1.2.2⟩, ⟨h.1.1, by omega, by omega⟩, by omega⟩
  have hLFall : LiveFrame s.mem s'.mem L (ws s.mem st.toNat zp.toNat zl.toNat) := by
    have hLs0 := hce.2.2.2.2.2.2.1
    refine LiveFrame.trans (liveFrame_of_frame (rs := winA s 4432 64) (lo := s.sp.toNat - 4432) (hi := s.sp.toNat + 64)
      (hF.mono fun a n h => by simp only [outside_append] at h; exact h.1) ?_ ?_)
      (LiveFrame.mono_ws hLF2 fun a n h => by
        simp only [ws, stkWs, outside_cons, outside_nil, and_true] at h ⊢; omega) (fun _ _ h => h)
    · intro r hr; have := hLs0 r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · intro r hr; simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
  refine ⟨?_, L', b', hext, by omega, hinv2, ⟨⟨hst8, hext.held hsth, ?_, hst48, ?_, ?_, ?_⟩, ?_, ?_⟩,
    hFall, hLFall⟩
  · show natVal s'.mem _ _ = _
    rw [show zl.toNat = xl.toNat + xl.toNat by omega]; exact hval
  · show s'.mem.accessible _ _ _ = _; rw [hacc2]; exact hstacc
  · show NatLive s'.mem R L' (s'.mem.readLE st.toNat 8) (s'.mem.readLE (st.toNat + 16) 8)
    rw [rW, rC]; intro hc; obtain ⟨q1, q2, q3, q4⟩ := hstnl hc
    exact ⟨q1, hext.held q2, by rw [hacc2]; exact q3, q4⟩
  · show s'.mem.readLE (st.toNat + 8) 8 ≤ s'.mem.readLE (st.toNat + 16) 8
    rw [rL, rC]; exact hstlc
  · show s'.mem.readLE (st.toNat + 16) 8 < _
    rw [rC]; exact hstc40
  · exact rL
  · exact Or.inl ⟨rW, rC⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem small (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = st) (h1 : s.regs 1 = zp)
    (h2 : s.regs 2 = zl) (h3 : s.regs 3 = zc) (h4 : s.regs 4 = xp) (h5 : s.regs 5 = xl) (h6 : s.regs 6 = xc)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hsm : xl.toNat < 12) :
    ReachesRet (LibBasicSqr.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hc : CodeIn ((Extracted.program.onlySegments BasicMul.names).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  have hBM := fun b L => Ensures.toSummaryRegs9 (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 =>
    BasicMul.ens impl hap R hmc b L a0 a1 a2 a3 a4 a5 a6 a7 a8) (noExit_restrict hap BasicMul.names) hc
  clear hc
  have hce := hpre.ce; have hthA := hpre.thA; have hthV := hpre.thV; have hthO := hpre.thO
  have hx0 := hpre.x0; have hzl := hpre.zl2; have hzc40 := hpre.zcb; have hzc := hpre.zlc
  have hce' := hce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hce'
  have eA : thrA = 7147152 := rfl
  rw [eA] at hthA hthV hthO
  simp only [win, outside_cons, outside_nil, and_true] at hthO
  janus_run [hthV, toInt_small xl (by omega), toInt_small (BitVec.ofNat 64 12) (by decide)] until [callBM]
  refine small2 impl hap R hmc b L st zp zl zc xp xl xc s hpre hsm _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by simp only [winA]; janus_frame) rfl ?_ ?_ hl4 hl48
  all_goals janus_simp

end FvModexp.Arm64.BasicSqr
