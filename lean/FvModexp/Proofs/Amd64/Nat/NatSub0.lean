import FvModexp.Proofs.Amd64.Nat.NatSub
import FvModexp.Proofs.Amd64.Nat.NatSub0Set
import FvModexp.Proofs.Amd64.Nat.NatSub0Alloc

set_option autoImplicit false

/-! # `nat.sub` (amd64) with empty-tolerant operands: the derived summary `ensR0` / `ens0` from `Pre0`
(twin of `FvModexp.Arm64.NatSub.ensR0`; coordinator decision on "[infra s30] FINDING") -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.NatSub

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath0 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc yp yl yc) (hyx : yl.toNat ≤ xl.toNat) (hx0 : xl.toNat = 0)
    (hpre : PreS0 4288 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatSub.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS0_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, -⟩, -, -, -, -, -, -, -, hx40, hy40,
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
theorem full0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Summary (LibNatSub.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧ s.regs 6 = xl ∧ s.regs 8 = xc ∧
        s.regs 9 = yp ∧ s.regs 10 = yl ∧ s.regs 11 = yc ∧
        PreS0 4288 R b L zp zc xp xl xc yp yl yc s)
      (fun s s' => RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11, hpre⟩
  have hyx : yl.toNat ≤ xl.toNat := hpre.2.2.1
  have he : Entry s zp zl zc xp xl xc yp yl yc := ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩
  have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibNatSub.program.link impl) := by
    rw [LibNatSub.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibNatSub.names
  have hmk' := MakesliceLiveContract64.of_codeIn hc3 hmk
  have hmv' := MemmoveLive64.of_codeIn hc3 hmv
  by_cases hx0 : xl.toNat = 0
  · exact zeroPath0 impl R b L zp zl zc xp xl xc yp yl yc s he hyx hx0 hpre
  by_cases hy0 : yl.toNat = 0
  · exact setPath0 impl R hmk' hmv' b L zp zl zc xp xl xc yp yl yc s he hy0 (by omega) hpre
  by_cases hc0 : zc.toNat = 0
  · exact alloc0 impl hap R hmk' hmv b L zp zl zc xp xl xc yp yl yc s he hyx (by omega) (by omega) hpre
  have hpS := hpre.toS (by omega) (by omega) (by omega)
  by_cases hz : xl.toNat ≤ zc.toNat
  · exact ReachesRet.mono (reuse impl hap R hmv b L zp zl zc xp xl xc yp yl yc s he hyx (by omega) hz hpS) (fun _ h => ⟨h.1, h.2.1⟩)
  · exact ReachesRet.mono (alloc impl hap R hmk' hmv b L zp zl zc xp xl xc yp yl yc s he hyx (by omega) (by omega) hpS) (fun _ h => ⟨h.1, h.2.1⟩)

/-- **`nat.sub`** (amd64, empty-tolerant `Pre0`): as `FvModexp.Arm64.NatSub.ensR0`. -/
theorem ensR0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre0 R b L zp zc xp xl xc yp yl yc)
      (fun s s' => Post R b L zp zc xp xl yp yl s s' ∧
        (xl.toNat ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 1).toNat = zc.toNat) ∧
        (xl.toNat < 2 ^ 39 → (s'.regs 1).toNat < 2 ^ 40)) := by
  rw [show names = LibNatSub.names from rfl, ← LibNatSub.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6,
      h_a7, h_a8, hpre.toS0⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

/-- **`nat.sub`** (amd64, empty-tolerant `Pre0`): as `FvModexp.Arm64.NatSub.ensR0` (`ensR` without the extra conjuncts). -/
theorem ens0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre0 R b L zp zc xp xl xc yp yl yc) (Post R b L zp zc xp xl yp yl) :=
  Ensures.mono (ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (fun _ h => h) (fun _ _ _ h => h.1)

end FvModexp.Amd64.NatSub
