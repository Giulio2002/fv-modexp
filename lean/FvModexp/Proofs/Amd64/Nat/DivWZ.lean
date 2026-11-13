import FvModexp.Proofs.Amd64.Nat.DivW

set_option autoImplicit false

/-!
# `nat.divW` (amd64) without the `memmove(z, x, 0)` side condition (twin of `Arm64/Nat/DivWZ.lean`)

`DivW.Pre`'s last conjunct (`len x = 0 → y = 1 → zp = xp ∨ z's empty range held and outside the window`) is only there
for `z.set(x)` with `len x = 0`, where Go's `copy` calls `memmove(zp, xp, 0)`. With Janus's zero-length contract
`MemmoveZeroLive64` as an extra premise the conjunct is dropped: `Pre2` = `Pre` without it; `full2`/`ens2`/`sum2`.
`nat.div` (whose `z` may be an arbitrary empty slice) uses this form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh inv_win)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivW

/-- `Pre` without its last conjunct -/
def Pre2 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4232 64 ∧ Outside wordT 16 R.rt ∧ y.toNat ≠ 0 ∧ xl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4232 64)) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 14).toNat + 16) 8 ∧
      Apart zp.toNat (8 * zc.toNat) (s.fsBase.toNat - 8) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ NatNorm s.mem xp.toNat xl.toNat ∧
    Outside xp.toNat (8 * xl.toNat) (win s 4232 64) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

theorem Pre2.toPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (h : Pre2 R b L zp zc xp xl y s)
    (hz : xl.toNat = 0 → y.toNat = 1 → zp = xp ∨
      (s.mem.accessible zp.toNat 0 true = true ∧ zp.toNat ≤ 2 ^ 48 ∧ Held R L zp.toNat 0 ∧
        Outside zp.toNat 0 (win s 4232 64))) :
    Pre R b L zp zc xp xl y s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, hz⟩

/-- `post_zero` from `NatLive` only -/
theorem post_zeroN {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    (hzl : NatLive s.mem R L zp.toNat zc.toNat) (hx : xl.toNat = 0) (s' : State)
    (hF : MemFrame s.mem s'.mem (R.rt ++ win s 4232 64 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]))
    (hLF : LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)])
    (hinv : R.inv b L (s.regs 14).toNat (view R.rt L s'.mem)) (hfs : s'.fsBase = s.fsBase)
    (h0 : s'.regs 0 = zp) (h1 : s'.regs 3 = 0#64) (h2 : s'.regs 1 = zc) (h3 : s'.regs 7 = 0#64) :
    PostI R b L zp zc xp xl y s s' := by
  refine ⟨hfs, zp.toNat, 0, zc.toNat, by rw [h0], by rw [h1]; rfl, by rw [h2], ?_, ?_, Or.inl rfl, Nat.zero_le _,
    by omega, L, b, LiveExt.refl R L, Nat.sub_le _ _, hinv, fun hc => ?_, Or.inl ⟨rfl, rfl⟩, hF, hLF⟩
  · rw [h3, hx, natVal_zero]; rfl
  · rw [hx, natVal_zero, natVal_zero]; simp
  · obtain ⟨a, b, c, d⟩ := hzl hc
    exact ⟨a, b, by rw [hF.accessible]; exact c, d⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `y = 1`, `len x = 0`: `z.set(x)` = `memmove(zp, xp, 0)` unless `zp = xp` (zero-length contract) -/
theorem setZero2 (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (LibDivW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xc : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp 0#64 xc 1#64) (hpre : Pre2 R b L zp zc xp 0#64 1#64 s) :
    ReachesRet (LibDivW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp 0#64 1#64 s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  by_cases hzx : zp = xp
  · subst hzx
    exact setZero impl R hmv b L zp zl zc zp xc s
      ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ (hpre.toPre fun _ _ => Or.inl rfl)
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, hgr, hLs, -, ⟨htg, htr, htw⟩⟩, -, -, -, hz40, hzl, -, -,
    -, -, -, -, hxw, hinv, -, hmv'⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  simp only [win, outside_cons, outside_nil, and_true] at hxw
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
set_option maxHeartbeats 64000000 in
theorem full2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Summary (LibDivW.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧ s.regs 6 = xl ∧ s.regs 8 = xc ∧
        s.regs 9 = y ∧ Pre2 R b L zp zc xp xl y s)
      (fun s s' => RegsOK s s' ∧ PostI R b L zp zc xp xl y s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre⟩
  by_cases hz : xl.toNat = 0 ∧ y.toNat = 1
  · have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibDivW.program.link impl) := by
      rw [LibDivW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibDivW.names
    have hx : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hz.1)
    have hy : y = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hz.2)
    subst hx hy
    exact setZero2 impl R (MemmoveLive64.of_codeIn hc3 hmv) (MemmoveZeroLive64.of_codeIn hc3 hmz) b L zp zl zc xp xc
      s ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ hpre
  · exact full impl hap R hmk hmv b L zp zl zc xp xl xc y s hpc
      ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, hpre.toPre fun a b => absurd ⟨a, b⟩ hz⟩

/-- **`nat.divW`** (amd64), `Pre2` form (premise: the zero-length `memmove` contract) -/
theorem ens2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y]
      (Pre2 R b L zp zc xp xl y) (Post R b L zp zc xp xl y) := by
  rw [show names = LibDivW.names from rfl, ← LibDivW.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full2 impl hap R hmk hmv hmz b L zp zl zc xp xl xc y) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6,
      hpre⟩ fun s' ⟨⟨a, b, c, d, e⟩, hfs, hq⟩ => ⟨⟨a, b, c, d⟩, hfs, e.trans h_df.symm, hq⟩

end FvModexp.Amd64.DivW
