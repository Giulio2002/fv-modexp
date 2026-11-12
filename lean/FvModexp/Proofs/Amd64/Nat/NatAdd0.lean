import FvModexp.Proofs.Amd64.Nat.NatAdd
import FvModexp.Proofs.Amd64.Nat.NatAdd0Set
import FvModexp.Proofs.Amd64.Nat.NatAdd0Swap

set_option autoImplicit false

/-! # `nat.add` (amd64) with empty-tolerant operands: the derived summary `ensR0` / `ens0` from `Pre0`
(twin of `FvModexp.Arm64.NatAdd.ensR0`; coordinator decision on "[infra s30] FINDING") -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.NatAdd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath0 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc yp yl yc) (hyx : yl.toNat ≤ xl.toNat) (hx0 : xl.toNat = 0)
    (hpre : PreS0 4288 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatAdd.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS0_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, -⟩, -, -, -, -, -, hx40, hy40,
    hz40, hzl, hzo, -, -, -, -, -, -, -, -, -, -, -, hinv, -, -⟩ := hpre'
  have hxz : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx0)
  have hyz : yl = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  subst hxz hyz
  janus64_run [BitVec.msb_eq_decide]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨rfl, ?df, zp.toNat, 0, zc.toNat, ?_, ?_, ?_, by simp, Or.inl rfl, by omega, by omega, L, b,
    LiveExt.refl R L, Nat.sub_le _ _, inv_win ?hF hout hb' hinv, fun hc => ?nl, Or.inl ⟨rfl, rfl⟩,
    MemFrame.mono ?hF fun a n h => by simp only [outside_append] at h; exact h.1.2,
    liveFrame_of_frame (rs := win s 4288 80) (MemFrame.mono ?hF fun a n h => by
        simp only [outside_append] at h; exact h.1)
      (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega)⟩, fun _ => ⟨?_, ?_⟩, fun _ => ?_⟩
  case hF => simp only [win]; janus_frame
  case df => exact hdf.symm
  case nl =>
    obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hc
    exact ⟨hzal, hzh, by janus64_simp; exact hzacc, hz48⟩
  all_goals janus64_simp
  all_goals first | exact hz40 | exact hdf | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem body0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Summary (LibNatAdd.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧ s.regs 6 = xl ∧ s.regs 8 = xc ∧
        s.regs 9 = yp ∧ s.regs 10 = yl ∧ s.regs 11 = yc ∧ yl.toNat ≤ xl.toNat ∧
        PreS0 4288 R b L zp zc xp xl xc yp yl yc s)
      (fun s s' => RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11, hyx, hpre⟩
  have he : Entry s zp zl zc xp xl xc yp yl yc := ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩
  have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibNatAdd.program.link impl) := by
    rw [LibNatAdd.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibNatAdd.names
  have hmk' := MakesliceLiveContract64.of_codeIn hc3 hmk
  have hmv' := MemmoveLive64.of_codeIn hc3 hmv
  by_cases hx0 : xl.toNat = 0
  · exact zeroPath0 impl R b L zp zl zc xp xl xc yp yl yc s he hyx hx0 hpre
  by_cases hy0 : yl.toNat = 0
  · exact setPath0 impl R hmk' hmv' b L zp zl zc xp xl xc yp yl yc s he hy0 (by omega) hpre
  have hpS := hpre.toS (by omega) (by omega)
  by_cases hz : xl.toNat + 1 ≤ zc.toNat
  · exact ReachesRet.mono (reuse impl hap R hmv b L zp zl zc xp xl xc yp yl yc s he hyx (by omega) hz hpS) (fun _ h => ⟨h.1, h.2.1⟩)
  · exact ReachesRet.mono (alloc impl hap R hmk' hmv b L zp zl zc xp xl xc yp yl yc s he hyx (by omega) (by omega) hpS) (fun _ h => ⟨h.1, h.2.1⟩)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Summary (LibNatAdd.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧ s.regs 6 = xl ∧ s.regs 8 = xc ∧
        s.regs 9 = yp ∧ s.regs 10 = yl ∧ s.regs 11 = yc ∧ PreS0 4440 R b L zp zc xp xl xc yp yl yc s)
      (fun s s' => RegsOK s s' ∧ PostR 4440 R b L zp zc xp xl yp yl s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11, hpre⟩
  have hsp0 : 4440 ≤ (s.regs 4).toNat := by have := hpre.1.2.1.1; simpa only [regSP] using this
  by_cases hyx : yl.toNat ≤ xl.toNat
  · obtain ⟨k, s', hst, hr, hq1, hq2⟩ := body0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc s hpc
      ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11, hyx, preS0_mono (by omega) hpre⟩
    exact ⟨k, s', hst, hr, hq1, postR_mono (by omega) hsp0 hq2⟩
  · obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ : (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧
        s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
        s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4440 < (s.regs 4).toNat ∧ 4440 ≤ (s.regs 4).toNat ∧
        (s.regs 4).toNat + 80 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 4).toNat - 4440) (4440 + 80) true = true ∧
        (s.regs 4).toNat % 8 = 0 ∧ TlsG s := by
      obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩ := hpre
      simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
      exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩
    have hpre' := hpre
    obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, -, -, -, -, -, hx40, hy40, -⟩ := hpre'
    unfold Apart at hga
    janus64_run [BitVec.msb_eq_decide] until [segAddr Extracted.program fn + 0x2c7]
    janus64_step
    have hF1 : MemFrame s.mem (((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 8) 8
        zp.toNat).writeLE ((s.regs 4).toNat + 32) 8 xp.toNat).writeLE ((s.regs 4).toNat + 56) 8 yp.toNat).writeLE ((s.regs 4).toNat - 152) 8 6182956)
        (win s 4440 80) := by simp only [win]; janus_frame
    refine ReachesRet.call (body0 impl hap R hmk hmv b L zp zl zc yp yl yc xp xl xc) rfl
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, preS0_swap hpre rfl ?_ ?_ hF1 (by simp)⟩ ?_
    rotate_left
    all_goals try janus64_simp
    intro s2 hpc2 ⟨⟨hs2, h5', h14', hx15'⟩, hq⟩
    have hq' := hq
    obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmf, _⟩, _⟩ := hq'
    have e152 : (s.regs 4 - 152#64).toNat = (s.regs 4).toNat - 152 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hzo : Outside zp.toNat (8 * zc.toNat) (win s 4440 80) := hpre.2.2.2.2.2.2.2.2.2.2.1
    simp only [win, outside_cons, outside_nil, and_true] at hzo
    have hrd : ∀ a, (s.regs 4).toNat - 8 ≤ a → a + 8 ≤ (s.regs 4).toNat + 8 → s2.mem.readLE a 8 =
        (((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 8) 8
        zp.toNat).writeLE ((s.regs 4).toNat + 32) 8 xp.toNat).writeLE ((s.regs 4).toNat + 56) 8 yp.toNat).writeLE ((s.regs 4).toNat - 152) 8 6182956).readLE a 8 := by
      intro a ha1 ha2
      refine hmf.readLE _ _ ?_
      simp only [win, Janus.Amd64.Tactic.setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, e152, outside_append,
        outside_cons, outside_nil, and_true]
      and_intros <;> first | exact hout.of_sub (by omega) (by omega) | omega
    have hr1 : s2.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
      rw [hrd _ (by omega) (by omega)]; janus64_simp
    have hr2 : s2.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
      rw [hrd _ (by omega) (by omega)]; janus64_simp
    janus64_run [hr1, hr2]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, postR_congr (postR_swap0 hpre (by janus64_simp) (by janus64_simp) (by janus64_simp) (by janus64_simp) hF1 hq) ?_ ?_ ?_ rfl rfl ?dfc⟩
    case dfc =>
      have hd2 := hq.1.2.1
      rw [hd2]
    all_goals try janus64_simp
    all_goals try rw [h14']
    all_goals try rw [hx15']
    all_goals try janus64_simp

/-- **`nat.add`** (amd64, empty-tolerant `Pre0`): as `FvModexp.Arm64.NatAdd.ens`. -/
theorem ensR0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre0 R b L zp zc xp xl xc yp yl yc)
      (fun s s' => Post R b L zp zc xp xl yp yl s s' ∧
        (need xl yl ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 1).toNat = zc.toNat) ∧
        (mx xl yl < 2 ^ 39 → (s'.regs 1).toNat < 2 ^ 40)) := by
  rw [show names = LibNatAdd.names from rfl, ← LibNatAdd.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6,
      h_a7, h_a8, hpre.toS0⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

/-- **`nat.add`** (amd64, empty-tolerant `Pre0`): as `FvModexp.Arm64.NatAdd.ens` (`ensR` without the extra conjuncts). -/
theorem ens0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre0 R b L zp zc xp xl xc yp yl yc) (Post R b L zp zc xp xl yp yl) :=
  Ensures.mono (ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (fun _ h => h) (fun _ _ _ h => h.1)

end FvModexp.Amd64.NatAdd
