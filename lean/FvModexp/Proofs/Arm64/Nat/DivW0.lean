import FvModexp.Proofs.Arm64.Nat.DivWZ

set_option autoImplicit false

/-!
# `nat.divW` (arm64) for a possibly-nil empty dividend (`Pre0`)

`Pre2` with the dividend's location facts (readable, `xp + 8 len ≤ 2^48`, held, outside the window) asked only for `len x > 0`: an empty
`x` (`len = 0`, e.g. a `nil` or `cap = 0` nat with an arbitrary pointer, possibly inside the window) is never dereferenced (`m = 0`: `q = z[:0]`,
or `z.set(x)` = `memmove(zp, xp, 0)` unless `zp = xp`). `full0`/`ens0`; `Pre2.toPre0` (old statements unchanged).
Used by `nat.div`'s `stk == nil, z2 = u` form (`(*Int).Mod`, whose dividend may be empty with any pointer).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivW

/-- `Pre2` with the dividend's location facts only for `len x > 0` -/
def Pre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4240 64 ∧ Outside wordT 16 R.rt ∧ y.toNat ≠ 0 ∧ xl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4240 64)) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (0 < xl.toNat → zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat))) ∧
    (0 < xl.toNat → s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
      Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4240 64)) ∧
    NatNorm s.mem xp.toNat xl.toNat ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

theorem Pre2.toPre0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (h : Pre2 R b L zp zc xp xl y s) : Pre0 R b L zp zc xp xl y s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, fun h => ⟨(a8 h).1, fun _ => (a8 h).2⟩, fun _ => ⟨a9, a10, a11, a13⟩, a12, a14,
    a15, a16⟩

theorem Pre0.toPre2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (h : Pre0 R b L zp zc xp xl y s) (hx : 0 < xl.toNat) : Pre2 R b L zp zc xp xl y s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a12, a14, a15, a16⟩ := h
  obtain ⟨a9, a10, a11, a13⟩ := a9 hx
  exact ⟨a1, a2, a3, a4, a5, a6, a7, fun h => ⟨(a8 h).1, (a8 h).2 hx⟩, a9, a10, a11, a12, a13, a14, a15, a16⟩

/-- the postcondition for `m = 0` (`q = z[:0]`, `r = 0`) from `Pre0` -/
theorem post_zero0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hpre : Pre0 R b L zp zc xp xl y s) (hx : xl.toNat = 0) (s' : State)
    (hF : MemFrame s.mem s'.mem (R.rt ++ winA s 4240 64 ++ zr zp zc))
    (hLF : LiveFrame s.mem s'.mem L (zr zp zc))
    (hinv : R.inv b L (s.regs 28).toNat (view R.rt L s'.mem))
    (h0 : s'.regs 0 = zp) (h1 : s'.regs 1 = 0#64) (h2 : s'.regs 2 = zc) (h3 : s'.regs 3 = 0#64) :
    Post R b L zp zc xp xl y s s' := by
  obtain ⟨-, -, -, -, -, hzl, -⟩ := hpre
  refine ⟨zp.toNat, 0, zc.toNat, by rw [h0], by rw [h1]; rfl, by rw [h2], ?_, ?_, Or.inl rfl, Nat.zero_le _,
    by omega, L, b, LiveExt.refl R L, Nat.sub_le _ _, hinv, fun hc => ?_, Or.inl ⟨rfl, rfl⟩, hF, hLF⟩
  · rw [h3, hx, natVal_zero]; rfl
  · rw [hx, natVal_zero, natVal_zero]; simp
  · obtain ⟨a, b, c, d⟩ := hzl hc
    exact ⟨a, b, by rw [hF.accessible]; exact c, d⟩

/-- from a window-only frame -/
theorem post_zero_win0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hpre : Pre0 R b L zp zc xp xl y s) (hx : xl.toNat = 0) (s' : State)
    (hW : MemFrame s.mem s'.mem (winA s 4240 64))
    (h0 : s'.regs 0 = zp) (h1 : s'.regs 1 = 0#64) (h2 : s'.regs 2 = zc) (h3 : s'.regs 3 = 0#64) :
    Post R b L zp zc xp xl y s s' := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨-, hb', ha, -⟩, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, hinv, -, -⟩ := hpre'
  refine post_zero0 hpre hx s' (hW.mono fun a n h => by simp only [outside_append] at h; exact h.1.2) ?_
    (inv_frame_winA hW hout hb' (by omega) hinv) h0 h1 h2 h3
  exact liveFrame_of_frame (rs := winA s 4240 64) (hW.mono fun a n h => by
      simp only [outside_append] at h; exact h.1) (fun r hr => by
      have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
    (fun r hr => by
      simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath0 (impl : List Segment) (b : Nat) (R : RtInv) (L : List (Nat × Nat)) (zp zl zc xp xc y : BitVec 64)
    (s : State) (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = 0#64) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = y)
    (hy0 : y.toNat ≠ 0) (hy1 : y.toNat ≠ 1) (hpre : Pre0 R b L zp zc xp 0#64 y s) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp 0#64 y s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, -, -⟩, -⟩ := hpre'
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  have hy1' : (y = 1#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy1; rw [e]; rfl
  janus_run [hy0', hy1']
  refine post_zero_win0 hpre rfl _ ?_ ?_ ?_ ?_ ?_
  · simp only [winA]; janus_frame
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `y = 1`, `len x = 0`: `z.set(x)` = `memmove(zp, xp, 0)` unless `zp = xp` (zero-length contract) -/
theorem setZero0 (impl : List Segment) (R : RtInv)
    (hmz : MemmoveZeroLive (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xc : BitVec 64)
    (s : State) (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = 0#64) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = 1#64)
    (hpre : Pre0 R b L zp zc xp 0#64 1#64 s) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp 0#64 1#64 s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, -, -, hz40, hzl, hzw', -, -, -,
    hinv, -, hmv'⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hzw'
  have hmv0 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 0] := fun d src => hmv' d src 0 (Nat.zero_le _)
  simp only [LiveSep, win] at hLs
  unfold Apart at hga
  by_cases hzx : zp = xp
  · subst hzx
    janus_run
    refine post_zero_win0 hpre rfl _ ?_ ?_ ?_ ?_ ?_
    · simp only [winA]; janus_frame
    all_goals janus_simp
  have hzx' : (zp = xp) = False := by simp only [eq_iff_iff, iff_false]; exact hzx
  set_option janus.callRegions true in
  janus_run [hzx'] calls [hmz]
  rename_i m _ _ hLF2 _ hF2 hinv2 _
  have hW := fun (M1 : Memory) (h : MemFrame s.mem M1 (winA s 4240 64)) => h
  refine post_zero0 hpre rfl _ ((hW _ ?hW).trans hF2 ?hc) ⟨fun a n hin hz => ?hl⟩ hinv2 ?_ ?_ ?_ ?_
  case hW => simp only [winA]; janus_frame
  case hc =>
    intro a n ho
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hr, h1', h2'⟩, h3'⟩ := ho
    exact ⟨⟨h1', h2'⟩, ⟨hr, by omega, by omega⟩⟩
  case hl =>
    obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this hz
    refine (hLF2.readLE a n ⟨q, hq, hq1, hq2⟩ (by simp only [outside_nil])).trans ?_
    refine (MemFrame.readLE (rs := winA s 4240 64) ?_ a n ?_)
    · simp only [winA]; janus_frame
    · simp only [winA, outside_cons, outside_nil, and_true]; omega
  all_goals janus_simp

set_option maxRecDepth 20000 in
theorem full0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Summary (LibDivW.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = xp ∧ s.regs 4 = xl ∧ s.regs 5 = xc ∧ s.regs 6 = y ∧
        Pre0 R b L zp zc xp xl y s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre⟩
  rcases Nat.eq_zero_or_pos xl.toNat with hx | hx
  · have hx' : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx)
    subst hx'
    by_cases hy : y.toNat = 1
    · have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibDivW.program.link impl) := by
        rw [LibDivW.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibDivW.names
      have hy' : y = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hy)
      subst hy'
      exact setZero0 impl R (MemmoveZeroLive.of_codeIn hc3 hmz) b L zp zl zc xp xc s hpc hl4 hl48 h0 h1 h2 h3 h4 h5
        h6 hpre
    · exact zeroPath0 impl b R L zp zl zc xp xc y s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 hpre.2.2.1 hy hpre
  · exact full2 impl hap R hmk hmv hmz b L zp zl zc xp xl xc y s hpc
      ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre.toPre2 hx⟩

/-- **`nat.divW`** (arm64), `Pre0` form (an empty dividend may have any pointer) -/
theorem ens0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y]
      (Pre0 R b L zp zc xp xl y) (Post R b L zp zc xp xl y) := by
  rw [show names = LibDivW.names from rfl, ← LibDivW.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full0 impl hap R hmk hmv hmz b L zp zl zc xp xl xc y) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

end FvModexp.Arm64.DivW
