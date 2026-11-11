import FvModexp.Proofs.Amd64.Nat.BasicSqrDefs
import FvModexp.Proofs.Amd64.Nat.DivmcCall
import FvModexp.Proofs.Common.BitLemmas

/-!
# `basicSqr` (amd64), the small path: `n < basicSqrThreshold` → `basicMul(z, x, x)`; return

Entry → the `CALL basicMul` at `+0x163` (the prologue spills `RBX`, `RSI`, clears the defer slot / bit, compares with
`basicSqrThreshold`), `basicMul`'s summary (`BasicMul.ens`, its `CallEnv` at `RSP - 200` from ours), the epilogue.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel
open FvModexp.Amd64.RunIface (Serves)

namespace FvModexp.Amd64.BasicSqr

/-- a held range outside a caller's own stores (`rs1`) and a callee's writes keeps its bytes -/
theorem Held.readLE3 {R : RtInv} {L rs1 ws1 ws2 : List (Nat × Nat)} {m0 m1 m2 : Janus.Arm64.Memory} {a n : Nat}
    (h : Held R L a n) (h01 : MemFrame m0 m1 rs1) (h12 : MemFrame m1 m2 (R.rt ++ ws1 ++ ws2))
    (hl : LiveFrame m1 m2 L ws2) (o1 : Outside a n rs1) (o2 : Outside a n ws1) (o3 : Outside a n ws2) :
    m2.readLE a n = m0.readLE a n := by
  rw [Held.readLE2 h h12 hl o2 o3]; exact h01.readLE a n o1

abbrev callBM : Nat := segAddr Extracted.program fn + 0x163

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
theorem small (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (st zp zl zc xp xl xc : BitVec 64) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (h0 : s.regs 0 = st) (h3 : s.regs 3 = zp) (h1 : s.regs 1 = zl) (h7 : s.regs 7 = zc) (h6 : s.regs 6 = xp)
    (h8 : s.regs 8 = xl) (h9 : s.regs 9 = xc)
    (hpre : Pre R b L st.toNat zp.toNat zl.toNat zc.toNat xp.toNat xl.toNat s) (hsm : xl.toNat < 12) :
    ReachesRet (LibBasicSqr.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ Post R b L st.toNat zp.toNat zl.toNat xp.toNat xl.toNat s s' := by
  have hc : CodeIn64 ((Extracted.program.onlySegments BasicMul.names).link impl) (LibBasicSqr.program.link impl) := by
    rw [LibBasicSqr.eq_only]; exact A64.codeIn_restrict_mono64 hap (sub_of_all (by decide))
  have hBM := Ensures.toSummaryRegs9 (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 =>
    BasicMul.ens impl hap R hmc b L a0 a1 a2 a3 a4 a5 a6 a7 a8) (A64.noExit_restrict64 hap BasicMul.names) hc
  clear hc
  simp only [BasicMul.Pre, CallEnv, TlsOK] at hBM
  have hce := hpre.ce; have hsv := hpre.sv; have hx0 := hpre.x0; have hzl := hpre.zl2; have hzc := hpre.zlc
  have hzc40 := hpre.zcb; have hzl' := hpre.zlive; have hzw := hpre.zw; have hzg := hpre.zg; have hzt := hpre.zt
  have hxacc := hpre.xacc; have hx48 := hpre.x48; have hxh := hpre.xh; have hxw := hpre.xw; have hzx := hpre.zx
  have hthA := hpre.thA; have hthV := hpre.thV; have hthO := hpre.thO; have hadx := hpre.adx
  have hinv := hpre.inv
  have hce' := hce
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := hce'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw htg
  have hfs : (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 := by omega
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 64 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [win, Outside, and_true] at this; exact this
  have hwin : ∀ r ∈ [((s.regs 4).toNat - 4424, (s.regs 4).toNat + 64)],
      (s.regs 4).toNat - 4424 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat + 64 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro r rfl; simp only; omega
  unfold RoOut at hro
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl' (by omega)
  have e2 : 8 * zl.toNat = 8 * (xl.toNat + xl.toNat) := by omega
  simp only [win, Outside, and_true] at hzw hxw hthO
  rw [e2] at hzh hzacc hz48 hzw hzx hzg hzt
  have hok : R.ok (cA "runtime.memclrNoHeapPointers") [zp.toNat, 8 * (xl.toNat + xl.toNat)] :=
    hsv.2.2.1 _ _ (by omega)
  have eA : thrA = 11841176 := rfl
  rw [eA] at hthA hthV hthO
  clear hzl'
  janus64_run [hfs, hthV, BitVec.msb_eq_decide] until [callBM + 5] calls [hBM]
  rename_i _ _ _ _ hfs2 hdf2 L' b' hext hbb hval hinv2 hF2 hLF2
  have e200 : (s.regs 4 - 200#64).toNat = (s.regs 4).toNat - 200 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  simp only [win, Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e200] at hF2
  have hFa : MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4424, (s.regs 4).toNat - 128),
      ((s.regs 4).toNat - 89, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 16, (s.regs 4).toNat),
      ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24), ((s.regs 4).toNat + 40, (s.regs 4).toNat + 48)] ++
      [(zp.toNat, zp.toNat + 8 * (xl.toNat + xl.toNat))]) :=
    MemFrame.trans (rs := [((s.regs 4).toNat - 200, (s.regs 4).toNat - 192), ((s.regs 4).toNat - 89, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 16, (s.regs 4).toNat), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24), ((s.regs 4).toNat + 40, (s.regs 4).toNat + 48)]) (by janus_frame) hF2 fun a n h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨hr, c1, c2, c3, c4, c5⟩, cz⟩ := h
      exact ⟨⟨by omega, c2, c3, c4, c5⟩, ⟨hr, by omega⟩, cz⟩
  have hr1 : s'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 :=
    hFa.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]
                       exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega, by omega, by omega, by omega⟩, by omega⟩)
  have hr2 : s'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hF2.readLE _ _ (by simp only [outside_append, outside_cons, outside_nil, and_true]
                           exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega⟩)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 5).isLt
  janus64_run [hr1, hr2]
  -- the caller-visible objects held in `L` outside the window and `z` keep their bytes
  have hkeep : ∀ a n, Held R L a n → Outside a n (win s 4424 64) → Apart a n zp.toNat (8 * (xl.toNat + xl.toNat)) →
      s'.mem.readLE a n = s.mem.readLE a n := by
    intro a n hh hw hz
    simp only [win, outside_cons, outside_nil, and_true] at hw
    unfold Apart at hz
    exact Held.readLE3 hh (rs1 := [((s.regs 4).toNat - 200, (s.regs 4).toNat - 192), ((s.regs 4).toNat - 89, (s.regs 4).toNat - 88), ((s.regs 4).toNat - 16, (s.regs 4).toNat), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24), ((s.regs 4).toNat + 40, (s.regs 4).toNat + 48)]) (by janus_frame) hF2 hLF2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hstw := hpre.stw; have hstz := hpre.stz
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  obtain ⟨hst8, hsth, hstacc, hst48, hstnl, hstlc, hstc40⟩ := hpre.stok
  have hstz' : Apart st.toNat 24 zp.toNat (8 * (xl.toNat + xl.toNat)) := by rw [← e2]; exact hstz
  unfold Apart at hstz'
  have rW : s'.mem.readLE st.toNat 8 = s.mem.readLE st.toNat 8 :=
    hkeep _ _ (hsth.sub (Nat.le_refl _) (by omega)) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart; omega)
  have rL : s'.mem.readLE (st.toNat + 8) 8 = s.mem.readLE (st.toNat + 8) 8 :=
    hkeep _ _ (hsth.sub (by omega) (by omega)) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart; omega)
  have rC : s'.mem.readLE (st.toNat + 16) 8 = s.mem.readLE (st.toNat + 16) 8 :=
    hkeep _ _ (hsth.sub (by omega) (by omega)) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart; omega)
  have hacc2 : ∀ a n w, s'.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hFa.accessible a n w
  have hFall : MemFrame s.mem s'.mem (R.rt ++ win s 4424 64 ++ ws s.mem st.toNat zp.toNat zl.toNat) :=
    hFa.mono fun a n h => by
      simp only [ws, stkWs, win, outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨hr, hw'⟩, hz', -⟩ := h
      exact ⟨⟨hr, by omega, by omega, by omega, by omega, by omega⟩, by omega⟩
  have hLFall : LiveFrame s.mem s'.mem L (ws s.mem st.toNat zp.toNat zl.toNat) := by
    refine ⟨fun a n hin hws => ?_⟩
    have hw' : a + n ≤ (s.regs 4).toNat - 4424 ∨ (s.regs 4).toNat + 64 ≤ a := by
      obtain ⟨r, hr, i1, i2⟩ := hin; have := hLs' r hr; omega
    simp only [ws, stkWs, outside_cons, outside_nil, and_true] at hws
    exact hkeep a n (Or.inl hin) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
      (by unfold Apart; omega)
  refine ⟨⟨?r4, ?r5, ?r14, ?x15⟩, ?fs, ?df, ?val, L', b', hext, by omega, ?inv,
    ⟨⟨hst8, hext.held hsth, ?sacc, hst48, ?snl, ?slc, ?sc40⟩, ?slen, ?sarr⟩, hFall, hLFall⟩
  case inv => janus_assumption
  case fs => show s'.fsBase = s.fsBase; rw [hfs2]
  case df => exact hdf.symm
  case val =>
    show natVal s'.mem _ _ = _
    rw [show zl.toNat = xl.toNat + xl.toNat by omega]; exact hval
  case sacc => show s'.mem.accessible _ _ _ = _; rw [hacc2]; exact hstacc
  case snl =>
    show NatLive s'.mem R L' (s'.mem.readLE st.toNat 8) (s'.mem.readLE (st.toNat + 16) 8)
    rw [rW, rC]; intro hc; obtain ⟨q1, q2, q3, q4⟩ := hstnl hc
    exact ⟨q1, hext.held q2, by rw [hacc2]; exact q3, q4⟩
  case slc =>
    show s'.mem.readLE (st.toNat + 8) 8 ≤ s'.mem.readLE (st.toNat + 16) 8
    rw [rL, rC]; exact hstlc
  case sc40 => show s'.mem.readLE (st.toNat + 16) 8 < _; rw [rC]; exact hstc40
  case slen => exact rL
  case sarr => exact Or.inl ⟨rW, rC⟩
  all_goals janus64_simp

end FvModexp.Amd64.BasicSqr
