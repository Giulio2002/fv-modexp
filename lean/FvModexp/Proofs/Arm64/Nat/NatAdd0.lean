import FvModexp.Proofs.Arm64.Nat.NatAdd
import FvModexp.Proofs.Arm64.Nat.NatAdd0Set
import FvModexp.Proofs.Arm64.Nat.NatAdd0Swap

set_option autoImplicit false

/-!
# `nat.add` (arm64) with empty-tolerant operands: the derived summary (coordinator decision on "[infra s30] FINDING")

`ensR0` / `ensX0` / `ens0`: `nat.add` from `Pre0` (no location facts for an empty `x` / `y`, no window fact for an
empty `z`), same postconditions as `ensR` / `ensX` / `ens` (`Pre.to0` maps the old precondition). `body0`: the
`len y ≤ len x` dispatch under `PreS0`; `full0`: both orders (self-call `z.add(y, x)` via `preS0_swap`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.NatAdd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `m = 0` (so `n = 0`): `return z[:0]`. -/
theorem zeroPath0 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc yp yl yc : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = yp)
    (h7 : s.regs 7 = yl) (h8 : s.regs 8 = yc) (hyx : yl.toNat ≤ xl.toNat) (hx0 : xl.toNat = 0)
    (hpre : PreS0 4304 R b L zp zc xp xl xc yp yl yc s) :
    ReachesRet (LibNatAdd.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostX 4304 R b L zp zc xp xl yp yl s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, -, -, -, -, hx40, hy40,
    hz40, hzl, -, -, -, -, -, -, -, -, -, -, -, -, hinv, -, -⟩ := hpre'
  have hxz : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx0)
  have hyz : yl = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
  subst hxz hyz
  janus_run
  refine ⟨⟨⟨zp.toNat, 0, zc.toNat, ?_, ?_, ?_, by simp, Or.inl rfl, by omega, by omega, L, b, LiveExt.refl R L,
    Nat.sub_le _ _, inv_frame_winA ?hF hout hb' (by omega) hinv, fun hc => ?nl, Or.inl ⟨rfl, rfl⟩,
    MemFrame.mono ?hF fun a n h => by simp only [outside_append] at h; exact h.1.2,
    liveFrame_of_frame (rs := winA s 4304 80) (MemFrame.mono ?hF fun a n h => by
        simp only [outside_append] at h; exact h.1)
      (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)⟩, fun _ => ⟨?_, ?_⟩, fun _ => ?_⟩,
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
  all_goals first | exact hz40 | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem body0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Summary (LibNatAdd.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = xp ∧ s.regs 4 = xl ∧ s.regs 5 = xc ∧ s.regs 6 = yp ∧ s.regs 7 = yl ∧
        s.regs 8 = yc ∧ yl.toNat ≤ xl.toNat ∧ PreS0 4304 R b L zp zc xp xl xc yp yl yc s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostX 4304 R b L zp zc xp xl yp yl s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, hyx, hpre⟩
  have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibNatAdd.program.link impl) := by
    rw [LibNatAdd.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibNatAdd.names
  have hmk' := MakesliceLiveContract.of_codeIn hc3 hmk
  have hmv' := MemmoveLive.of_codeIn hc3 hmv
  by_cases hx0 : xl.toNat = 0
  · exact zeroPath0 impl R b L zp zl zc xp xl xc yp yl yc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 hyx hx0 hpre
  by_cases hy0 : yl.toNat = 0
  · exact setPath0 impl R hmk' hmv' b L zp zl zc xp xl xc yp yl yc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 hy0
      (by omega) hpre
  have hpS := hpre.toS (by omega) (by omega)
  by_cases hz : xl.toNat + 1 ≤ zc.toNat
  · exact reuse impl hap R hmv b L zp zl zc xp xl xc yp yl yc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 hyx
      (by omega) hz hpS
  · exact alloc impl hap R hmk' hmv b L zp zl zc xp xl xc yp yl yc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 h8 hyx
      (by omega) (by omega) hpS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Summary (LibNatAdd.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = xp ∧ s.regs 4 = xl ∧ s.regs 5 = xc ∧ s.regs 6 = yp ∧ s.regs 7 = yl ∧
        s.regs 8 = yc ∧ PreS0 4464 R b L zp zc xp xl xc yp yl yc s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostX 4464 R b L zp zc xp xl yp yl s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, hpre⟩
  have hsp0 : 4464 ≤ s.sp.toNat := hpre.1.2.1.2.1
  by_cases hyx : yl.toNat ≤ xl.toNat
  · obtain ⟨k, s', hst, hr, hq1, hq2⟩ := body0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc s hpc
      ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, h8, hyx, preS0_mono (by omega) hpre⟩
    exact ⟨k, s', hst, hr, hq1, postX_mono (by omega) hsp0 hq2⟩
  · have hpre' := hpre
    obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, -, -, -, -, hx40, hy40, -⟩ := hpre'
    unfold Apart at hga
    janus_run until [segAddr Extracted.program fn + 0x214]
    janus_step
    have hF1 : MemFrame s.mem (((((s.mem.writeLE (s.sp.toNat - 160) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 168) 8
        (s.regs 29).toNat).writeLE (s.sp.toNat + 8) 8 zp.toNat).writeLE (s.sp.toNat + 32) 8 xp.toNat).writeLE
        (s.sp.toNat + 56) 8 yp.toNat) (winA s 4464 80) := by simp only [winA]; janus_frame
    refine ReachesRet.call (body0 impl hap R hmk hmv b L zp zl zc yp yl yc xp xl xc) rfl
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, preS0_swap hpre rfl ?_ hF1 (by simp)⟩ ?_
    rotate_left
    all_goals try janus_simp
    intro s2 hpc2 ⟨⟨hs2, h28', h29', h18'⟩, hq⟩
    have hq' := hq
    obtain ⟨_, hmf, _⟩ := hq'
    have e160 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hzo : Outside zp.toNat (8 * zc.toNat) (win s 4464 80) := hpre.2.2.2.2.2.2.2.2.2.2.1
    simp only [win, outside_cons, outside_nil, and_true] at hzo
    have hrd : ∀ a, s.sp.toNat - 168 ≤ a → a + 8 ≤ s.sp.toNat - 152 → s2.mem.readLE a 8 =
        (((((s.mem.writeLE (s.sp.toNat - 160) 8 (s.regs 30).toNat).writeLE (s.sp.toNat - 168) 8
        (s.regs 29).toNat).writeLE (s.sp.toNat + 8) 8 zp.toNat).writeLE (s.sp.toNat + 32) 8 xp.toNat).writeLE
        (s.sp.toNat + 56) 8 yp.toNat).readLE a 8 := by
      intro a ha1 ha2
      refine hmf.readLE _ _ ?_
      simp only [winA, outside_append, outside_cons, outside_nil, and_true, e160]
      and_intros <;> first | exact hout.of_sub (by omega) (by omega) | omega
    have hr1 : s2.mem.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat := by
      rw [hrd _ (by omega) (by omega)]; janus_simp
    have hr2 : s2.mem.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat := by
      rw [hrd _ (by omega) (by omega)]; janus_simp
    janus_run [hr1, hr2]
    exact postX_congr (postX_swap0 hpre rfl (by janus_simp) hF1 hq) (by janus_simp) (by janus_simp) (by janus_simp) rfl

/-- **`nat.add`** (arm64, empty-tolerant operands `Pre0`, exact write set `PostX`): `z.add(x, y)` returns a normalised nat holding `X + Y`, in `z`'s array (`zc ≥ need`) or a
fresh one; writes only `z`'s array and the window; no panic, no fault. -/
theorem ensX0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre0 R b L zp zc xp xl xc yp yl yc)
      (PostX 4464 R b L zp zc xp xl yp yl) := by
  rw [show names = LibNatAdd.names from rfl, ← LibNatAdd.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, h_x8, hpre.toS0⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

/-- **`nat.add`** (arm64, empty-tolerant operands `Pre0`): `z.add(x, y)` returns a normalised nat holding `X + Y`, in `z`'s array (`zc ≥ need`) or a
fresh one; writes only `z`'s array and the window; no panic, no fault. -/
theorem ensR0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre0 R b L zp zc xp xl xc yp yl yc)
      (fun s s' => Post R b L zp zc xp xl yp yl s s' ∧
        (need xl yl ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 2).toNat = zc.toNat) ∧
        (mx xl yl < 2 ^ 39 → (s'.regs 2).toNat < 2 ^ 40)) :=
  Ensures.mono (ensX0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (fun _ h => h) (fun _ _ _ h => h.1)

/-- (`ensR` without the extra conjuncts.) -/
theorem ens0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Pre0 R b L zp zc xp xl xc yp yl yc) (Post R b L zp zc xp xl yp yl) :=
  Ensures.mono (ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc) (fun _ h => h) (fun _ _ _ h => h.1)

end FvModexp.Arm64.NatAdd
