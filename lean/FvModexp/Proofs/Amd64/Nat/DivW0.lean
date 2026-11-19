import FvModexp.Proofs.Amd64.Nat.DivWZ

set_option autoImplicit false

/-!
# `nat.divW` (amd64) for a possibly-nil empty dividend (`Pre0`) — the twin of `Arm64/Nat/DivW0.lean`

`Pre2` with the dividend's location facts (readable, `xp + 8 len ≤ 2^48`, held, outside the window, and `zp = xp ∨ Apart`)
asked only for `len x > 0`: an empty `x` (`len = 0`, e.g. a `nil` or `cap = 0` nat with an arbitrary pointer, possibly
inside the window) is never dereferenced (`m = 0`: `q = z[:0]`, or `z.set(x)` = `memmove(zp, xp, 0)` unless `zp = xp`).
`full0`/`ens0`; `Pre2.toPre0` (old statements unchanged). Used by `nat.div`'s empty-dividend paths.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivW

/-- `Pre2` with the dividend's location facts only for `len x > 0` -/
def Pre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4232 64 ∧ Outside wordT 16 R.rt ∧ y.toNat ≠ 0 ∧ xl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4232 64)) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 14).toNat + 16) 8 ∧
      Apart zp.toNat (8 * zc.toNat) (s.fsBase.toNat - 8) 8 ∧
      (0 < xl.toNat → zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat))) ∧
    (0 < xl.toNat → s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
      Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4232 64)) ∧
    NatNorm s.mem xp.toNat xl.toNat ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

theorem Pre2.toPre0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (h : Pre2 R b L zp zc xp xl y s) : Pre0 R b L zp zc xp xl y s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, fun h => ⟨(a8 h).1, (a8 h).2.1, fun _ => (a8 h).2.2⟩,
    fun _ => ⟨a9, a10, a11, a13⟩, a12, a14, a15, a16⟩

theorem Pre0.toPre2 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (h : Pre0 R b L zp zc xp xl y s) (hx : 0 < xl.toNat) : Pre2 R b L zp zc xp xl y s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a12, a14, a15, a16⟩ := h
  obtain ⟨a9, a10, a11, a13⟩ := a9 hx
  exact ⟨a1, a2, a3, a4, a5, a6, a7, fun h => ⟨(a8 h).1, (a8 h).2.1, (a8 h).2.2 hx⟩, a9, a10, a11, a12, a13, a14,
    a15, a16⟩

theorem pre_env0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hpre : Pre0 R b L zp zc xp xl y s) :
    (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4232 < (s.regs 4).toNat ∧ 4232 ≤ (s.regs 4).toNat ∧
    (s.regs 4).toNat + 64 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 4232) (4232 + 64) true = true ∧ (s.regs 4).toNat % 8 = 0 ∧ TlsG s := by
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩

theorem post_zero_win0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hpre : Pre0 R b L zp zc xp xl y s) (hx : xl.toNat = 0) (s' : State)
    (hW : MemFrame s.mem s'.mem (win s 4232 64)) (hfs : s'.fsBase = s.fsBase)
    (h0 : s'.regs 0 = zp) (h1 : s'.regs 3 = 0#64) (h2 : s'.regs 1 = zc) (h3 : s'.regs 7 = 0#64) :
    PostI R b L zp zc xp xl y s s' := by
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env0 hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, -, -, hLs, -, -⟩, -, -, -, -, hzl, -, -, -, -, hinv, -, -⟩ := hpre'
  refine post_zeroN hzl hx s' (hW.mono fun a n h => by simp only [outside_append] at h; exact h.1.2) ?_
    (inv_win hW hout hb' hinv) hfs h0 h1 h2 h3
  exact liveFrame_of_frame (rs := win s 4232 64) (hW.mono fun a n h => by
      simp only [outside_append] at h; exact h.1) (fun r hr => by
      have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
    (fun r hr => by
      simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem zeroPath0 (impl : List Amd64.Segment) (b : Nat) (R : RtInv) (L : List (Nat × Nat))
    (zp zl zc xp xc y : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp 0#64 xc y) (hy0 : y.toNat ≠ 0) (hy1 : y.toNat ≠ 1)
    (hpre : Pre0 R b L zp zc xp 0#64 y s) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp 0#64 y s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env0 hpre
  have hy0' : (y = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy0; rw [e]; rfl
  have hy1' : (y = 1#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hy1; rw [e]; rfl
  janus64_run [hy0', hy1', BitVec.msb_eq_decide]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post_zero_win0 hpre rfl _ ?hW ?_ ?_ ?_ ?_ ?_⟩
  case hW => simp only [win]; janus_frame
  all_goals try janus64_simp
  all_goals first | omega | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `y = 1`, `len x = 0`: `z.set(x)` = `memmove(zp, xp, 0)` unless `zp = xp` (zero-length contract) -/
theorem setZero0 (impl : List Amd64.Segment) (R : RtInv)
    (hmz : MemmoveZeroLive64 (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp 0#64 xc 1#64) (hpre : Pre0 R b L zp zc xp 0#64 1#64 s) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp 0#64 1#64 s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  by_cases hzx : zp = xp
  · subst hzx
    obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env0 hpre
    have hz40 : zc.toNat < 2 ^ 40 := hpre.2.2.2.2.1
    janus64_run [BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post_zero_win0 hpre rfl _ ?hW ?_ ?_ ?_ ?_ ?_⟩
    case hW => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | omega | skip
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, ⟨htg, htr, htw⟩⟩, -, -, -, hz40, hzl, -, -, -,
    -, hinv, -, hmv'⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hmv0 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 0] := fun d src => hmv' d src 0 (Nat.zero_le _)
  simp only [LiveSep, win] at hLs
  unfold Apart at hga htw
  have hzx' : (zp = xp) = False := by simp only [eq_iff_iff, iff_false]; exact hzx
  have hgok : s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4096 < (s.regs 4).toNat - 136 := by omega
  janus64_run [hzx', BitVec.msb_eq_decide] calls [hmz]
  · rename_i heq
    exfalso; apply hzx; apply BitVec.eq_of_toNat_eq
    have := zp.isLt; have := xp.isLt; omega
  rename_i m _ _ hLF2 _ hF2 hinv2
  have hW := fun (M1 : Janus.Arm64.Memory) (h : MemFrame s.mem M1 (win s 4232 64)) => h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, post_zeroN hzl rfl _ ((hW _ ?hW).trans hF2 ?hc) ⟨fun a n hin hz => ?hl⟩ hinv2 ?_ ?_
    ?_ ?_ ?_⟩
  case hW => simp only [win]; janus_frame
  case hc =>
    intro a n ho
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hr, h1'⟩, h3'⟩ := ho
    exact ⟨h1', hr, by omega, by omega⟩
  case hl =>
    obtain ⟨q, hq, hq1, hq2⟩ := hin
    have := hLs q hq
    simp only [outside_cons, outside_nil, and_true] at this hz
    refine (hLF2.readLE a n ⟨q, hq, hq1, hq2⟩ (by simp only [outside_nil])).trans ?_
    refine (MemFrame.readLE (rs := win s 4232 64) ?_ a n ?_)
    · simp only [win]; janus_frame
    · simp only [win, outside_cons, outside_nil, and_true]; omega
  all_goals try janus64_simp
  all_goals first | omega | skip

set_option maxRecDepth 20000 in
theorem full0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Summary (LibDivW.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧ s.regs 6 = xl ∧ s.regs 8 = xc ∧
        s.regs 9 = y ∧ Pre0 R b L zp zc xp xl y s)
      (fun s s' => RegsOK s s' ∧ PostI R b L zp zc xp xl y s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre⟩
  rcases Nat.eq_zero_or_pos xl.toNat with hx | hx
  · have hx' : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx)
    subst hx'
    by_cases hy : y.toNat = 1
    · have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibDivW.program.link impl) := by
        rw [LibDivW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibDivW.names
      have hy' : y = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hy)
      subst hy'
      exact setZero0 impl R (MemmoveZeroLive64.of_codeIn hc3 hmz) b L zp zl zc xp xc s
        ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ hpre
    · exact zeroPath0 impl b R L zp zl zc xp xc y s ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ hpre.2.2.1 hy
        hpre
  · exact full2 impl hap R hmk hmv hmz b L zp zl zc xp xl xc y s hpc
      ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre.toPre2 hx⟩

/-- **`nat.divW`** (amd64), `Pre0` form (an empty dividend may have any pointer) -/
theorem ens0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y]
      (Pre0 R b L zp zc xp xl y) (Post R b L zp zc xp xl y) := by
  refine Ensures.of_old ?_ ?_
  · by_cases hx : xl.toNat = 0
    · have hx0 : xl = 0 := BitVec.eq_of_toNat_eq (by simpa using hx)
      subst hx0
      janus64_pre_setRet [FvModexp.Amd64.DivW.Pre0, FvModexp.Amd64.CallEnv, FvModexp.Amd64.DivW.wordT, FvModexp.NatLive, FvModexp.Amd64.win, FvModexp.NatNorm, FvModexp.Amd64.TlsOK]
    · have hxp : 0 < xl.toNat := Nat.pos_of_ne_zero hx
      janus64_pre_setRet [FvModexp.Amd64.DivW.Pre0, FvModexp.Amd64.CallEnv, FvModexp.Amd64.DivW.wordT, FvModexp.NatLive, FvModexp.Amd64.win, FvModexp.NatNorm, FvModexp.Amd64.TlsOK]
  rw [show names = LibDivW.names from rfl, ← LibDivW.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full0 impl hap R hmk hmv hmz b L zp zl zc xp xl xc y) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6,
      hpre⟩ fun s' ⟨⟨a, b, c, d, e⟩, hfs, hq⟩ => ⟨⟨a, b, c, d⟩, hfs, e.trans h_df.symm, hq⟩

end FvModexp.Amd64.DivW
