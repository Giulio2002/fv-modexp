import FvModexp.Proofs.Amd64.Nat.MulAddWWReuse
import FvModexp.Proofs.Amd64.Nat.MulAddWWAlloc
import FvModexp.Proofs.Amd64.Nat.MulAddWWSet

/-!
# `nat.mulAddWW` (go-bigmodexpfix natmul.go:136), amd64: the summary

`toSet`: the entry → `+0x122` (`m = 0` or `y = 0`) and the `setWord` dispatch; `full`: the `Summary` at the entry over
all paths (`setWord`; `zc ≥ m + 1`: `reuse`; else `alloc`); `ens`: the `Ensures` of CONVENTIONS §3 on
`(Extracted.program.onlySegments names).link impl`; `sum`: `ens` as a callee summary.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.MulAddWW

/-- From `SetRel` at `+0x122`: the three `setWord` paths. -/
theorem setPath (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibMulAddWW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64)
    (s : State) (M : Janus.Arm64.Memory) (h : SetRel R b L zp zc xp xl y r s M) (hxy0 : xl.toNat = 0 ∨ y.toNat = 0)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 hSet) (h0 : S.regs 0 = zp) (h1 : S.regs 1 = zc) (h10 : S.regs 10 = r)
    (hsp : S.regs 4 = s.regs 4 - 104#64) (h14 : S.regs 14 = s.regs 14) (h5 : S.regs 5 = s.regs 4 - 8#64)
    (hx15 : S.xmm 15 = s.xmm 15) (hfs : S.fsBase = s.fsBase) (hdf : S.df = false) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) S fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' := by
  by_cases hr : r.toNat = 0
  · exact setZero impl R b L zp zc xp xl y r s M h hr S hpc h0 h1 h10 hsp h14 h5 hx15 hfs hdf hm
  by_cases hzc : zc.toNat = 0
  · exact setAlloc impl R hmk b L zp zc xp xl y r s M h hxy0 hr hzc S hpc h0 h1 h10 hsp h14 h5 hx15 hfs hdf hm
  · exact setReuse impl R b L zp zc xp xl y r s M h hr hzc S hpc h0 h1 h10 hsp h14 h5 hx15 hfs hdf hm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toSet (impl : List Amd64.Segment) (R : RtInv)
    (hmk : MakesliceLiveContract64 (LibMulAddWW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (he : Entry s zp zl zc xp xl xc y r) (hxy0 : xl.toNat = 0 ∨ y.toNat = 0) (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (retAddrOf s) s fun s' =>
      RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hw, hal, htg⟩ := pre_env hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, hd, hout, hga, -, -, hro, -⟩, -, hx40, hz40, -⟩ := hpre'
  have hxy : natVal s.mem xp.toNat xl.toNat * y.toNat = 0 := by
    rcases hxy0 with e | e
    · rw [e]; simp
    · rw [e]; simp
  have hrel : ∀ M : Janus.Arm64.Memory, MemFrame s.mem M (win s 4208 72) →
      M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 →
      M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat →
      M.readLE ((s.regs 4).toNat + 64) 8 = r.toNat → M.regions = s.mem.regions → SetRel R b L zp zc xp xl y r s M :=
    fun M hF r1 r2 r3 hrg => ⟨hpre, hxy, hra, hx15, hdf, hF, r1, r2, r3,
      FvModexp.dataLoaded_frame64 hd hrg hro (hF.widen R.rt) (fun q hq _ => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        exact Janus.Arm64.Memory.accessible_mono _ hw (Nat.le_refl _) (by simp only; omega))⟩
  by_cases hx0 : xl.toNat = 0
  · have hx0' : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx0)
    subst hx0'
    janus64_run [BitVec.msb_eq_decide] until [hSet]
    refine setPath impl R hmk b L zp zc xp 0#64 y r s _ (hrel _ ?hF ?_ ?_ ?_ (by simp)) hxy0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals janus64_simp
  · have hy0 : y = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hy0
    have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
    janus64_run [hx0', BitVec.msb_eq_decide] until [hSet]
    refine setPath impl R hmk b L zp zc xp xl 0#64 r s _ (hrel _ ?hF ?_ ?_ ?_ (by simp)) hxy0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ rfl
    case hF => simp only [win]; janus_frame
    all_goals janus64_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) :
    Summary (LibMulAddWW.program.link impl) (segAddr Extracted.program fn)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = zp ∧ s.regs 3 = zl ∧ s.regs 1 = zc ∧ s.regs 7 = xp ∧ s.regs 6 = xl ∧ s.regs 8 = xc ∧
        s.regs 9 = y ∧ s.regs 10 = r ∧ Pre R b L zp zc xp xl y r s)
      (fun s s' => RegsOK s s' ∧ PostI R b L zp zc xp xl y r s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10, hpre⟩
  have he : Entry s zp zl zc xp xl xc y r := ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9, h10⟩
  have hc3 : CodeIn64 (Extracted.program.ofImpl impl) (LibMulAddWW.program.link impl) := by
    rw [LibMulAddWW.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibMulAddWW.names
  have hmk' := MakesliceLiveContract64.of_codeIn hc3 hmk
  by_cases hxy0 : xl.toNat = 0 ∨ y.toNat = 0
  · exact toSet impl R hmk' b L zp zl zc xp xl xc y r s he hxy0 hpre
  have hx0 : xl.toNat ≠ 0 := fun e => hxy0 (Or.inl e)
  have hy0 : y.toNat ≠ 0 := fun e => hxy0 (Or.inr e)
  by_cases hz : xl.toNat + 1 ≤ zc.toNat
  · exact reuse impl hap R b L zp zl zc xp xl xc y r s he hx0 hy0 hz hpre
  · exact alloc impl hap R hmk' b L zp zl zc xp xl xc y r s he hx0 hy0 (by omega) hpre

/-- **`nat.mulAddWW`** (amd64): `z.mulAddWW(x, y, r)` returns a normalised nat holding `X·y + r`, in `z`'s array
(`zc ≥ need`) or a fresh one; writes only `z`'s array and the window; no panic, no fault. -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y, r]
      (Pre R b L zp zc xp xl y r) (Post R b L zp zc xp xl y r) := by
  rw [show names = LibMulAddWW.names from rfl, ← LibMulAddWW.eq_only]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full impl hap R hmk b L zp zl zc xp xl xc y r) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, h_a6,
      h_a7, hpre⟩ fun s' ⟨⟨a, b, c, d, e⟩, hfs, hq⟩ => ⟨⟨a, b, c, d⟩, hfs, e.trans h_df.symm, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk b L zp zl zc xp xl xc y r) (A64.noExit_restrict64 hap names)
    (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.MulAddWW
