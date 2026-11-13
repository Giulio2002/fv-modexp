import FvModexp.Proofs.Amd64.Nat.DivWSet

/-!
# `nat.divW` (amd64): the `m = 0` paths (`q = z[:0]`; `y = 1`: `z.set(x)` with `memmove(zp, xp, 0)` unless `zp = xp`)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivW

theorem post_zero {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hpre : Pre R b L zp zc xp xl y s) (hx : xl.toNat = 0) (s' : State)
    (hF : MemFrame s.mem s'.mem (R.rt ++ win s 4232 64 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]))
    (hLF : LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)])
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s'.mem)) (hfs : s'.fsBase = s.fsBase)
    (h0 : s'.regs 0 = zp) (h1 : s'.regs 3 = 0#64) (h2 : s'.regs 1 = zc) (h3 : s'.regs 7 = 0#64) :
    PostI R b L zp zc xp xl y s s' := by
  obtain ⟨-, -, -, -, -, hzl, -⟩ := hpre
  refine ⟨hfs, zp.toNat, 0, zc.toNat, by rw [h0], by rw [h1]; rfl, by rw [h2], ?_, ?_, Or.inl rfl, Nat.zero_le _,
    by omega, L, b, LiveExt.refl R L, Nat.sub_le _ _, hinv, fun hc => ?_, Or.inl ⟨rfl, rfl⟩, hF, hLF⟩
  · rw [h3, hx, natVal_zero]; rfl
  · rw [hx, natVal_zero, natVal_zero]; simp
  · obtain ⟨a, b, c, d⟩ := hzl hc
    exact ⟨a, b, by rw [hF.accessible]; exact c, d⟩

theorem post_zero_win {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hpre : Pre R b L zp zc xp xl y s) (hx : xl.toNat = 0) (s' : State)
    (hW : MemFrame s.mem s'.mem (win s 4232 64)) (hfs : s'.fsBase = s.fsBase)
    (h0 : s'.regs 0 = zp) (h1 : s'.regs 3 = 0#64) (h2 : s'.regs 1 = zc) (h3 : s'.regs 7 = 0#64) :
    PostI R b L zp zc xp xl y s s' := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, -, -, hLs, -, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, hinv, -, -⟩ := hpre'
  refine post_zero hpre hx s' (hW.mono fun a n h => by simp only [outside_append] at h; exact h.1.2) ?_
    (inv_win hW hout hb' hinv) hfs h0 h1 h2 h3
  exact liveFrame_of_frame (rs := win s 4232 64) (hW.mono fun a n h => by
      simp only [outside_append] at h; exact h.1) (fun r hr => by
      have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
    (fun r hr => by
      simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath (impl : List Amd64.Segment) (b : Nat) (R : RtInv) (L : List (Nat × Nat))
    (zp zl zc xp xc y : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp 0#64 xc y) (hy0 : y.toNat ≠ 0) (hy1 : y.toNat ≠ 1)
    (hpre : Pre R b L zp zc xp 0#64 y s) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp 0#64 y s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  have hy1' : (y = 1#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy1; rw [e]; rfl
  janus64_run [hy0', hy1', BitVec.msb_eq_decide]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post_zero_win hpre rfl _ ?hW ?_ ?_ ?_ ?_ ?_⟩
  case hW => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | omega | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setZero (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp 0#64 xc 1#64) (hpre : Pre R b L zp zc xp 0#64 1#64 s) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp 0#64 1#64 s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, hga, hgr, hLs, -, ⟨-, htr, htw⟩⟩, -, -, -, hz40, hzl, hzw', -, -, -, -, -, hxw, hinv, -,
    hmv', hz0⟩ := hpre'
  simp only [win, outside_cons, outside_nil, and_true] at hxw
  have hmv0 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 0] := fun d src => hmv' d src 0 (Nat.zero_le _)
  simp only [LiveSep, win] at hLs
  unfold Apart at hga htw
  by_cases hzx : zp = xp
  · subst hzx
    janus64_run [BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post_zero_win hpre rfl _ ?hW ?_ ?_ ?_ ?_ ?_⟩
    case hW => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | omega | skip
  obtain ⟨hza, hz48, hzh, hzo⟩ := (hz0 rfl rfl).resolve_left hzx
  replace hzw' : Outside zp.toNat (8 * zc.toNat) (win s 4232 64) := by
    by_cases hc : zc.toNat = 0
    · rw [hc, Nat.mul_zero]; exact hzo
    · exact hzw' (by omega)
  clear hzo
  simp only [win, outside_cons, outside_nil, and_true] at hzw'
  have hzh' : InRanges zp.toNat 0 L ∨ Outside zp.toNat 0 R.rt := hzh
  have hzx' : (zp = xp) = False := by simp only [eq_iff_iff, iff_false]; exact hzx
  have hgok : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 136 := by omega
  janus64_run [hzx', BitVec.msb_eq_decide] calls [hmv]
  · rename_i heq
    exfalso; apply hzx; apply BitVec.eq_of_toNat_eq
    have := zp.isLt; have := xp.isLt; omega
  rename_i m _ _ hF2 hLF2 hinv2 _
  have hW := fun (M1 : Janus.Arm64.Memory) (h : MemFrame s.mem M1 (win s 4232 64)) => h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post_zero hpre rfl _ ((hW _ ?hW).trans hF2 ?hc) ⟨fun a n hin hz => ?hl⟩ hinv2 ?_ ?_ ?_
    ?_ ?_⟩
  case hW => simp only [win]; janus_frame
  case hc =>
    intro a n ho
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hr, h1'⟩, h3'⟩ := ho
    exact ⟨h1', ⟨hr, by omega, by omega⟩, by omega⟩
  case hl =>
    obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this hz
    refine (hLF2.readLE a n ⟨q, hq, hq1, hq2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega)).trans ?_
    refine (MemFrame.readLE (rs := win s 4232 64) ?_ a n ?_)
    · simp only [win]; janus_frame
    · simp only [win, outside_cons, outside_nil, and_true]; omega
  all_goals try janus64_simp
  all_goals first | omega | skip

end FvModexp.Amd64.DivW
