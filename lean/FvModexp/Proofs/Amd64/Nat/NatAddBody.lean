import FvModexp.Proofs.Amd64.Nat.NatAddAlloc
import FvModexp.Proofs.Amd64.Nat.NatAddSetE

/-! # `nat.add` (amd64): the body for `len y ≤ len x`, as a `Summary` at the entry (see the arm64 twin) -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.NatAdd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc yp yl yc) (hyx : yl.toNat ≤ xl.toNat) (hx0 : xl.toNat = 0)
    (hpre : PreS 4288 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatAdd.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := preS_env hpre
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
theorem body (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Summary (LibNatAdd.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧ s.regs 6 = xl ∧ s.regs 8 = xc ∧
        s.regs 9 = yp ∧ s.regs 10 = yl ∧ s.regs 11 = yc ∧ yl.toNat ≤ xl.toNat ∧
        PreS 4288 R b L zp zc xp xl xc yp yl yc s)
      (fun s s' => RegsOK s s' ∧ PostR 4288 R b L zp zc xp xl yp yl s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11, hyx, hpre⟩
  have he : Entry s zp zl zc xp xl xc yp yl yc := ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, h11⟩
  have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibNatAdd.program.link impl) := by
    rw [LibNatAdd.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibNatAdd.names
  have hmk' := MakesliceLiveContract64.of_codeIn hc3 hmk
  have hmv' := MemmoveLive64.of_codeIn hc3 hmv
  by_cases hx0 : xl.toNat = 0
  · exact zeroPath impl R b L zp zl zc xp xl xc yp yl yc s he hyx hx0 hpre
  by_cases hy0 : yl.toNat = 0
  · exact setPath impl R hmk' hmv' b L zp zl zc xp xl xc yp yl yc s he hy0 (by omega) hpre
  by_cases hz : xl.toNat + 1 ≤ zc.toNat
  · exact reuse impl hap R hmv b L zp zl zc xp xl xc yp yl yc s he hyx (by omega) hz hpre
  · exact alloc impl hap R hmk' hmv b L zp zl zc xp xl xc yp yl yc s he hyx (by omega) (by omega) hpre

end FvModexp.Amd64.NatAdd
