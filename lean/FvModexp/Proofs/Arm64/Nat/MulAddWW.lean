import FvModexp.Proofs.Arm64.Nat.MulAddWWReuse
import FvModexp.Proofs.Arm64.Nat.MulAddWWAlloc
import FvModexp.Proofs.Arm64.Nat.MulAddWWSet

/-!
# `nat.mulAddWW` (go-bigmodexpfix natmul.go:136), arm64: the summary

`toSet`: the entry → `+0xc0` (`m = 0` or `y = 0`) and the `setWord` dispatch; `full`: the `Summary` at the entry over
all paths (`setWord`; `zc ≥ m + 1`: `reuse`; else `alloc`); `ens`: the `Ensures` of CONVENTIONS §3 on
`(Extracted.program.onlySegments names).link impl`; `sum`: `ens` as a callee summary.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.MulAddWW

/-- From `SetRel` at `+0xc0`: the three `setWord` paths. -/
theorem setPath (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibMulAddWW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64)
    (s : State) (M : Memory) (h : SetRel R b L zp zc xp xl y r s M) (hxy0 : xl.toNat = 0 ∨ y.toNat = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hSet) (h0 : S.regs 0 = zp) (h2 : S.regs 2 = zc) (h7 : S.regs 7 = r)
    (hsp : S.sp = s.sp - 112#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 120#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' := by
  by_cases hr : r.toNat = 0
  · exact setZero impl R b L zp zc xp xl y r s M h hr S hpc h0 h2 h7 hsp h28 h29 h18 hm
  by_cases hzc : zc.toNat = 0
  · exact setAlloc impl R hmk b L zp zc xp xl y r s M h hxy0 hr hzc S hpc h0 h2 h7 hsp h28 h29 h18 hm
  · exact setReuse impl R b L zp zc xp xl y r s M h hr hzc S hpc h0 h2 h7 hsp h28 h29 h18 hm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem toSet (impl : List Segment) (R : RtInv)
    (hmk : MakesliceLiveContract (LibMulAddWW.program.link impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = zp) (h1 : s.regs 1 = zl)
    (h2 : s.regs 2 = zc) (h3 : s.regs 3 = xp) (h4 : s.regs 4 = xl) (h5 : s.regs 5 = xc) (h6 : s.regs 6 = y)
    (h7 : s.regs 7 = r) (hxy0 : xl.toNat = 0 ∨ y.toNat = 0) (hpre : Pre R b L zp zc xp xl y r s) :
    ReachesRet (LibMulAddWW.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, -, -, hro⟩, -, hx40, hz40, -, -, -, -, -, -, -, -,
    -⟩ := hpre'
  have hxy : natVal s.mem xp.toNat xl.toNat * y.toNat = 0 := by
    rcases hxy0 with e | e
    · rw [e]; simp
    · rw [e]; simp
  have hrel : ∀ M : Memory, MemFrame s.mem M (winA s 4208 72) →
      M.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat → M.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat →
      M.readLE (s.sp.toNat + 64) 8 = r.toNat → M.regions = s.mem.regions → SetRel R b L zp zc xp xl y r s M :=
    fun M hF r1 r2 r3 hrg => ⟨hpre, hxy, hl4, hl48, hF, r1, r2, r3,
      dataLoaded_win (lo := s.sp.toNat - 4208) (n := 4208 + 72) hd hrg hro (hF.widen R.rt) hw (fun q hq => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> simp only <;> omega)⟩
  by_cases hx0 : xl.toNat = 0
  · have hx0' : xl = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hx0)
    subst hx0'
    janus_run until [hSet]
    refine setPath impl R hmk b L zp zc xp 0#64 y r s _ (hrel _ ?hF ?_ ?_ ?_ (by simp)) hxy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
      rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
  · have hy0 : y = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hy0
    have hx0' : (xl = 0#64) = False := by simp only [eq_iff_iff, iff_false]; intro e; apply hx0; rw [e]; rfl
    janus_run [hx0'] until [hSet]
    refine setPath impl R hmk b L zp zc xp xl 0#64 r s _ (hrel _ ?hF ?_ ?_ ?_ (by simp)) hxy0 _ rfl ?_ ?_ ?_ ?_ ?_ ?_
      ?_ rfl
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) :
    Summary (LibMulAddWW.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = zp ∧ s.regs 1 = zl ∧
        s.regs 2 = zc ∧ s.regs 3 = xp ∧ s.regs 4 = xl ∧ s.regs 5 = xc ∧ s.regs 6 = y ∧ s.regs 7 = r ∧
        Pre R b L zp zc xp xl y r s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc xp xl y r s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, h7, hpre⟩
  have hc3 : CodeIn (Extracted.program.ofImpl impl) (LibMulAddWW.program.link impl) := by
    rw [LibMulAddWW.eq_only]; exact codeIn_ofImpl_restrict_of_apart hap LibMulAddWW.names
  have hmk' := MakesliceLiveContract.of_codeIn hc3 hmk
  by_cases hxy0 : xl.toNat = 0 ∨ y.toNat = 0
  · exact toSet impl R hmk' b L zp zl zc xp xl xc y r s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 hxy0 hpre
  have hx0 : xl.toNat ≠ 0 := fun e => hxy0 (Or.inl e)
  have hy0 : y.toNat ≠ 0 := fun e => hxy0 (Or.inr e)
  by_cases hz : xl.toNat + 1 ≤ zc.toNat
  · exact reuse impl hap R b L zp zl zc xp xl xc y r s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 hx0 hy0 hz hpre
  · exact alloc impl hap R hmk' b L zp zl zc xp xl xc y r s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 h7 hx0 hy0 (by omega)
      hpre

/-- **`nat.mulAddWW`** (arm64): `z.mulAddWW(x, y, r)` returns a normalised nat holding `X·y + r`, in `z`'s array
(`zc ≥ need`) or a fresh one; writes only `z`'s array and the window; no panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y, r]
      (Pre R b L zp zc xp xl y r) (Post R b L zp zc xp xl y r) := by
  rw [show names = LibMulAddWW.names from rfl, ← LibMulAddWW.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full impl hap R hmk b L zp zl zc xp xl xc y r) hret h_pc h_lr
    ⟨?_, ?_, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y r : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk b L zp zl zc xp xl xc y r) (noExit_restrict hap names)
    (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.MulAddWW
