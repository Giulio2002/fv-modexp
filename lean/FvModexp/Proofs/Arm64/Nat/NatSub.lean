import FvModexp.Proofs.Arm64.Nat.NatSubReuse
import FvModexp.Proofs.Arm64.Nat.NatSubAlloc
import FvModexp.Proofs.Arm64.Nat.NatSubSetE

/-!
# `nat.sub` (arm64): the summary

`full`: the `Summary` at the entry (paths: `m = 0`, `n = 0` (`setPath`), `zc ≥ m` (`reuse`), else (`alloc`)); `ens`, `sum`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatSub

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `m = 0` (so `n = 0`): `return z[:0]`. -/
theorem zeroPath (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = yp)
    (h7 : s.regs 7 = yl) (h8 : s.regs 8 = yc) (hyx : yl.toNat ≤ xl.toNat) (hx0 : xl.toNat = 0)
    (hpre : PreS 4304 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatSub.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostS 4304 R b L zp zc xp xl yp yl s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, -, -, -, -, -, -, hx40, hy40,
    hz40, hzl, -, -, -, -, -, -, -, -, -, -, -, -, hinv, -, -⟩ := hpre'
  have hxz : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx0)
  have hyz : yl = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  subst hxz hyz
  janus_run
  refine ⟨zp.toNat, 0, zc.toNat, ?_, ?_, ?_, by simp, Or.inl rfl, by omega, by omega, L, b, LiveExt.refl R L,
    Nat.sub_le _ _, inv_frame_winA ?hF hout hb' (by omega) hinv, fun hc => ?nl, Or.inl ⟨rfl, rfl⟩,
    MemFrame.mono ?hF fun a n h => by simp only [outside_append] at h; exact h.1.2,
    liveFrame_of_frame (rs := winA s 4304 80) (MemFrame.mono ?hF fun a n h => by
        simp only [outside_append] at h; exact h.1)
      (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)⟩
  case hF => simp only [winA]; janus_frame
  case nl =>
    obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hc
    exact ⟨hzal, hzh, by janus_simp; exact hzacc, hz48⟩
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Summary (LibNatSub.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = xp ∧ s.regs 4 = xl ∧ s.regs 5 = xc ∧ s.regs 6 = yp ∧ s.regs 7 = yl ∧
        s.regs 8 = yc ∧ PreS 4304 R b L zp zc xp xl xc yp yl yc s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostS 4304 R b L zp zc xp xl yp yl s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, hpre⟩
  have hyx : yl.toNat ≤ xl.toNat := hpre.2.2.1
  have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibNatSub.program.link impl) := by
    rw [LibNatSub.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibNatSub.names
  have hmk' := MakesliceLiveContract.of_codeIn hc3 hmk
  have hmv' := MemmoveLive.of_codeIn hc3 hmv
  by_cases hx0 : xl.toNat = 0
  · exact zeroPath impl R b L zp zl zc xp xl xc yp yl yc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 hyx hx0 hpre
  by_cases hy0 : yl.toNat = 0
  · exact setPath impl R hmk' hmv' b L zp zl zc xp xl xc yp yl yc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 hy0
      (by omega) hpre
  by_cases hz : xl.toNat ≤ zc.toNat
  · exact reuse impl hap R hmv b L zp zl zc xp xl xc yp yl yc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 hyx
      (by omega) hz hpre
  · exact alloc impl hap R hmk' hmv b L zp zl zc xp xl xc yp yl yc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 hyx
      (by omega) (by omega) hpre

def names : List String := LibNatSub.names

/-- **`nat.sub`** (arm64): `z.sub(x, y)` (`len y ≤ len x`, `Y ≤ X`) returns a normalised nat holding `X - Y`, in `z`'s array (`zc ≥ need`) or a
fresh one; writes only `z`'s array and the window; no panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre R b L zp zc xp xl xc yp yl yc) (Post R b L zp zc xp xl yp yl) := by
  rw [show names = LibNatSub.names from rfl, ← LibNatSub.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (noExit_restrict hap names)
    (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.NatSub
