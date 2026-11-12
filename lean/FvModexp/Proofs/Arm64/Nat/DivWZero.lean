import FvModexp.Proofs.Arm64.Nat.DivWSet

/-!
# `nat.divW` (arm64): the `m = 0` paths

`y ≠ 1`: `q = z[:0]` (`+0xf4`); `y = 1`: `z.set(x)` with `m = 0`: `z.make(0)` reuses `z` (`0 ≤ zc`), `copy(z[:0], x)`
calls `memmove(zp, xp, 0)` unless `zp = xp`. Both return `(zp, 0, zc)` and `r = 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivW

/-- `Pre` without its last conjunct (the `memmove(z, x, 0)` side condition) -/
def Pre2 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4240 64 ∧ Outside wordT 16 R.rt ∧ y.toNat ≠ 0 ∧ xl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4240 64)) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ NatNorm s.mem xp.toNat xl.toNat ∧
    Outside xp.toNat (8 * xl.toNat) (win s 4240 64) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

theorem Pre.toPre2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (h : Pre R b L zp zc xp xl y s) : Pre2 R b L zp zc xp xl y s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, -⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩

theorem Pre2.toPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (h : Pre2 R b L zp zc xp xl y s)
    (hz : xl.toNat = 0 → y.toNat = 1 → zp = xp ∨
      (s.mem.accessible zp.toNat 0 true = true ∧ zp.toNat ≤ 2 ^ 48 ∧ Held R L zp.toNat 0 ∧
        Outside zp.toNat 0 (win s 4240 64))) :
    Pre R b L zp zc xp xl y s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, hz⟩

/-- `post_zero` from `Pre2` -/
theorem post_zero2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hpre : Pre2 R b L zp zc xp xl y s) (hx : xl.toNat = 0) (s' : State)
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

/-- The postcondition for `m = 0` (`q = z[:0]`, `r = 0`). -/
theorem post_zero {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hpre : Pre R b L zp zc xp xl y s) (hx : xl.toNat = 0) (s' : State)
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

/-- From a window-only frame. -/
theorem post_zero_win {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hpre : Pre R b L zp zc xp xl y s) (hx : xl.toNat = 0) (s' : State)
    (hW : MemFrame s.mem s'.mem (winA s 4240 64))
    (h0 : s'.regs 0 = zp) (h1 : s'.regs 1 = 0#64) (h2 : s'.regs 2 = zc) (h3 : s'.regs 3 = 0#64) :
    Post R b L zp zc xp xl y s s' := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨-, hb', ha, -⟩, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, hinv, -, -⟩ := hpre'
  refine post_zero hpre hx s' (hW.mono fun a n h => by simp only [outside_append] at h; exact h.1.2) ?_
    (inv_frame_winA hW hout hb' (by omega) hinv) h0 h1 h2 h3
  exact liveFrame_of_frame (rs := winA s 4240 64) (hW.mono fun a n h => by
      simp only [outside_append] at h; exact h.1) (fun r hr => by
      have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
    (fun r hr => by
      simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath (impl : List Segment) (b : Nat) (R : RtInv) (L : List (Nat × Nat)) (zp zl zc xp xc y : BitVec 64)
    (s : State) (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = 0#64) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = y)
    (hy0 : y.toNat ≠ 0) (hy1 : y.toNat ≠ 1) (hpre : Pre R b L zp zc xp 0#64 y s) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp 0#64 y s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, -, -⟩, -⟩ := hpre'
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  have hy1' : (y = 1#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy1; rw [e]; rfl
  janus_run [hy0', hy1']
  refine post_zero_win hpre rfl _ ?_ ?_ ?_ ?_ ?_
  · simp only [winA]; janus_frame
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `y = 1`, `len x = 0`: `z.set(x)` = `memmove(zp, xp, 0)` unless `zp = xp` (zero-length contract) -/
theorem setZero (impl : List Segment) (R : RtInv)
    (hmz : MemmoveZeroLive (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xc : BitVec 64)
    (s : State) (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = 0#64) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = 1#64)
    (hpre : Pre2 R b L zp zc xp 0#64 1#64 s) :
    ReachesRet (LibDivW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp 0#64 1#64 s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, -, -, hz40, hzl, hzw', -, -, -, -, -,
    hxw, hinv, -, hmv'⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw
  have hmv0 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 0] := fun d src => hmv' d src 0 (Nat.zero_le _)
  simp only [LiveSep, win] at hLs
  unfold Apart at hga
  by_cases hzx : zp = xp
  · subst hzx
    janus_run
    refine post_zero_win (hpre.toPre fun _ _ => Or.inl rfl) rfl _ ?_ ?_ ?_ ?_ ?_
    · simp only [winA]; janus_frame
    all_goals janus_simp
  have hzx' : (zp = xp) = False := by simp only [eq_iff_iff, iff_false]; exact hzx
  set_option janus.callRegions true in
  janus_run [hzx'] calls [hmz]
  rename_i m _ _ hLF2 _ hF2 hinv2 _
  have hW := fun (M1 : Memory) (h : MemFrame s.mem M1 (winA s 4240 64)) => h
  refine post_zero2 hpre rfl _ ((hW _ ?hW).trans hF2 ?hc) ⟨fun a n hin hz => ?hl⟩ hinv2 ?_ ?_ ?_ ?_
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

end FvModexp.Arm64.DivW
