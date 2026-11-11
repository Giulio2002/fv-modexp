import FvModexp.Proofs.Arm64.Nat.LibDivWVW
import FvModexp.Proofs.Arm64.Nat.AddVW
import FvModexp.Proofs.Arm64.RecipWordSum
import FvModexp.Proofs.Arm64.DivWWSum
import FvModexp.Proofs.Common.AsmDivVW

/-!
# `math/big.divWVW(z []Word, xn Word, x []Word, y Word) (r Word)` (go-bigmodexpfix natdiv.go:579, Go ABIInternal, arm64)

```go
func divWVW(z []Word, xn Word, x []Word, y Word) (r Word) {
	r = xn
	if len(x) == 1 { qq, rr := bits.Div(uint(r), uint(x[0]), uint(y)); z[0] = Word(qq); return Word(rr) }
	rec := reciprocalWord(y)
	for i := len(z) - 1; i >= 0; i-- { z[i], r = divWW(r, x[i], y, rec) }
	return r
}
```
Arguments `X0..X2 = z`, `X3 = xn`, `X4..X6 = x`, `X7 = y`; 64-byte frame, spills into the caller's frame up to
`SP + 72`; callees `reciprocalWord` (88 bytes below its `SP`), `math/bits.Div64` (40), `divWW` (frameless): the window
is `[SP - 152, SP + 72)`. Callee summaries (agent asm): `RecipWordSum.recip_summary`, `Div64Sum.div64_summary`,
`DivWWSum.divWW_summary`, moved into the restricted program by `codeIn_lib`.
Proof split (one `janus_run` per declaration): `fin` (loop exit), `body` (one iteration, head to head), `loop`
(induction), `gen` (entry to the loop head, `len x ≠ 1`), `one` (`len x = 1`), `ens_lib`, `ens`, `sum`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivWVW

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.divWVW"
def names : List String := LibDivWVW.names

abbrev entry : Nat := segAddr Extracted.program fn

/-! ## The callees, moved into the restricted program -/

theorem fetchIn_cons_cases {A : Segment} {rest : List Segment} {pc w : Nat}
    (h : Program.fetchIn (A :: rest) pc = some w) :
    Program.fetchIn [A] pc = some w ∨ Program.fetchIn rest pc = some w := by
  rw [Program.fetchIn_cons] at h
  rw [Program.fetchIn_cons]
  split at h
  · rename_i hc
    rw [if_pos hc]
    split at h
    · left; exact h
    · right; exact h
  · right; exact h

theorem fetchIn_some_mem : ∀ {segs : List Segment} {pc w : Nat}, Program.fetchIn segs pc = some w →
    ∃ seg ∈ segs, Program.fetchIn [seg] pc = some w
  | [], _, _, h => by simp [Program.fetchIn] at h
  | A :: rest, _, _, h => by
    rcases fetchIn_cons_cases h with h1 | h1
    · exact ⟨A, List.mem_cons_self .., h1⟩
    · obtain ⟨seg, hm, hs⟩ := fetchIn_some_mem h1
      exact ⟨seg, List.mem_cons_of_mem _ hm, hs⟩

/-- a library program whose segments are segments of the Run extraction kept by `names` is code of the
restricted program -/
theorem codeIn_lib (impl : List Segment) (hap : ImplApart Extracted.program impl) {lp : Program}
    (hm : ∀ seg ∈ lp.segments, seg ∈ Extracted.program.segments ∧ names.contains seg.name = true) :
    CodeIn lp (LibDivWVW.program.link impl) := by
  rw [LibDivWVW.eq_only]
  intro pc w hf
  obtain ⟨seg, hseg, hf'⟩ := fetchIn_some_mem (segs := lp.segments) hf
  obtain ⟨hm1, hm2⟩ := hm seg hseg
  exact codeIn_single (lp := { lp with segments := [seg] }) hap rfl hm1 hm2 pc w hf'

set_option maxRecDepth 100000 in
theorem codeIn_divww (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn FvModexp.Lib.DivWWA64.program (LibDivWVW.program.link impl) := by
  refine codeIn_lib impl hap ?_
  have e : FvModexp.Lib.DivWWA64.program.segments = [Extracted.seg63] := rfl
  rw [e]; intro seg hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
  exact ⟨List.getElem_mem (l := Extracted.program.segments) (n := 63) (by decide), by decide⟩

set_option maxRecDepth 100000 in
theorem codeIn_div (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn FvModexp.Lib.DivA64.program (LibDivWVW.program.link impl) := by
  refine codeIn_lib impl hap ?_
  have e : FvModexp.Lib.DivA64.program.segments = [Extracted.seg62] := rfl
  rw [e]; intro seg hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
  exact ⟨List.getElem_mem (l := Extracted.program.segments) (n := 62) (by decide), by decide⟩

set_option maxRecDepth 100000 in
theorem codeIn_recip (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn FvModexp.Lib.RecipA64.program (LibDivWVW.program.link impl) := by
  refine codeIn_lib impl hap ?_
  have e : FvModexp.Lib.RecipA64.program.segments = [Extracted.seg61, Extracted.seg62] := rfl
  rw [e]; intro seg hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨List.getElem_mem (l := Extracted.program.segments) (n := 61) (by decide), by decide⟩
  · exact ⟨List.getElem_mem (l := Extracted.program.segments) (n := 62) (by decide), by decide⟩

theorem divww (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibDivWVW.program.link impl) FvModexp.Lib.DivWWA64.entry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ (s.regs 2).toNat ≠ 0 ∧
        (s.regs 0).toNat < (s.regs 2).toNat ∧ (s.regs 3).toNat = FvModexp.AsmDiv.recipWord (s.regs 2).toNat)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧
        s'.regs 0 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) / (s.regs 2).toNat) ∧
        s'.regs 1 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) % (s.regs 2).toNat) ∧
        s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ MemFrame s.mem s'.mem []) := by
  refine Summary.mono (Summary.of_codeIn (codeIn_divww impl hap) FvModexp.Arm64.DivWWSum.divWW_summary)
    (fun _ h => h) ?_
  intro s s' _ ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, h3, h4, h5 18 (by decide), h5 28 (by decide), h5 29 (by decide), h6⟩

theorem div64 (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibDivWVW.program.link impl) FvModexp.Lib.DivA64.entry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 0 ∧ StackOK s 40 0 ∧
        (s.regs 2).toNat ≠ 0 ∧ (s.regs 0).toNat < (s.regs 2).toNat)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 18 = s.regs 18 ∧
        (s'.regs 0).toNat = ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) / (s.regs 2).toNat ∧
        (s'.regs 1).toNat = ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) % (s.regs 2).toNat ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 40, s.sp.toNat - 24)]) := by
  refine Summary.mono (Summary.of_codeIn (codeIn_div impl hap) FvModexp.Arm64.Div64Sum.div64_summary)
    (fun _ h => h) ?_
  intro s s' _ ⟨h1, h2, h3, h4, _, h6, h7, h8, _, h10⟩
  exact ⟨h1, h2, h3, h4, h6, h7, h8, h10⟩

theorem recip (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibDivWVW.program.link impl) FvModexp.Lib.RecipA64.entry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 48 ∧ StackOK s 88 0 ∧
        (s.regs 0).toNat ≠ 0 ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 88)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧
        s'.regs 0 = BitVec.ofNat 64 (FvModexp.AsmDiv.recipWord (s.regs 0).toNat) ∧
        s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat - 40)]) := by
  refine Summary.mono (Summary.of_codeIn (codeIn_recip impl hap) FvModexp.Arm64.RecipWordSum.recip_summary)
    (fun _ h => h) ?_
  intro s s' _ ⟨h1, h2, h3, h4, h5, h6, _, _, h9⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h9⟩

/-! ## Statement -/

/-- the precondition (`xl = zl` separately: Go's `len(z) = len(x)` contract of `divWVW`) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl xn xp y : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 152 72 ∧ y.toNat ≠ 0 ∧ xn.toNat < y.toNat ∧
    NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 152 72) ∧
    s.mem.accessible xp.toNat (8 * zl.toNat) false = true ∧ xp.toNat + 8 * zl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * zl.toNat) ∧ Outside xp.toNat (8 * zl.toNat) (win s 152 72) ∧
    (zp = xp ∨ Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * zl.toNat)) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- the dividend `xn·B^n + x` -/
@[reducible] def Dvd (m : Memory) (zl xn xp : BitVec 64) : Nat :=
  xn.toNat * 2 ^ (64 * zl.toNat) + natVal m xp.toNat zl.toNat

/-- the postcondition: `X0 = (xn·B^n + x) mod y`, `z = (xn·B^n + x) / y` (it fits: `xn < y`) -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl xn xp y : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat = Dvd s.mem zl xn xp % y.toNat ∧
    natVal s'.mem zp.toNat zl.toNat = Dvd s.mem zl xn xp / y.toNat ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 152 72 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)]

/-- a state `S` inside the frame against the call state `s`: limbs `z[k:n]` written, the spill slots -/
structure Rel (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret zp xp zl y rec k : Nat) (s S : State) : Prop where
  sp : S.sp = s.sp - 64#64
  g : S.regs 28 = s.regs 28
  fp : S.regs 29 = s.sp - 72#64
  r18 : S.regs 18 = s.regs 18
  lr : S.mem.readLE (s.sp.toNat - 64) 8 = ret
  sfp : S.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat
  rz : S.mem.readLE (s.sp.toNat + 8) 8 = zp
  rx : S.mem.readLE (s.sp.toNat + 40) 8 = xp
  rxl : S.mem.readLE (s.sp.toNat + 48) 8 = zl
  ry : S.mem.readLE (s.sp.toNat + 64) 8 = y
  rrec : S.mem.readLE (s.sp.toNat - 24) 8 = rec
  mf : MemFrame s.mem S.mem (R.rt ++ winA s 152 72 ++ [(zp + 8 * k, zp + 8 * zl)])
  lf : LiveFrame s.mem S.mem L [(zp + 8 * k, zp + 8 * zl)]
  inv : R.inv b L (s.regs 28).toNat (view R.rt L S.mem)

/-- the loop head (`TBNZ $63, X1` at `+0xc4`), `k` limbs left (`i = k - 1`), remainder `r` -/
def AtHead (rec k r : Nat) (S : State) : Prop :=
  S.pc = BitVec.ofNat 64 (entry + 0xc4) ∧ S.regs 0 = BitVec.ofNat 64 rec ∧ S.regs 1 = BitVec.ofNat 64 k - 1#64 ∧
    S.regs 2 = BitVec.ofNat 64 r

/-- the loop's value invariant: `r = H k % y`, `z[k:n] = H k / y` -/
def Val (s : State) (zp zl xn xp y : BitVec 64) (k r : Nat) (S : State) : Prop :=
  r = FvModexp.AsmDivVW.H s.mem xn.toNat xp.toNat zl.toNat k % y.toNat ∧
    S.mem.readLE (zp.toNat + 8 * k) (8 * (zl.toNat - k)) = FvModexp.AsmDivVW.H s.mem xn.toNat xp.toNat zl.toNat k / y.toNat

set_option maxRecDepth 20000 in
/-- the loop exit (`k = 0`): return `r` -/
theorem fin (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (rec r : Nat) (S : State) (hh : AtHead rec 0 r S)
    (hrel : Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat rec 0 s S) (hv : Val s zp zl xn xp y 0 r S) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩, hy, hxn, -⟩ := hpre
  obtain ⟨hpc, h0, h1, h2⟩ := hh
  obtain ⟨hsp, h28, h29, h18, h_rd_lr, h_rd_fp, -, -, -, -, -, hmf, hlf, hinv⟩ := hrel
  obtain ⟨hr, hq⟩ := hv
  have hspn : S.sp.toNat = s.sp.toNat - 64 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hacc : S.mem.accessible (s.sp.toNat - 152) (152 + 72) true = true := by rw [hmf.accessible]; exact hw
  have hr64 : r < 2 ^ 64 := by have := Nat.mod_lt (FvModexp.AsmDivVW.H s.mem xn.toNat xp.toNat zl.toNat 0) (show 0 < y.toNat by omega); have := y.isLt; omega
  janus_run
  refine ⟨?_, ?_, L, b, LiveExt.refl R L, Nat.le_refl _, hinv, ?_, ?_⟩
  · show (BitVec.ofNat 64 r).toNat = (xn.toNat * 2 ^ (64 * zl.toNat) + s.mem.readLE xp.toNat (8 * zl.toNat)) % y.toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr64, hr, FvModexp.AsmDivVW.H_zero]
  · show S.mem.readLE zp.toNat (8 * zl.toNat) = (xn.toNat * 2 ^ (64 * zl.toNat) + s.mem.readLE xp.toNat (8 * zl.toNat)) / y.toNat
    rw [← FvModexp.AsmDivVW.H_zero]; simpa using hq
  · simpa using hmf
  · simpa using hlf

theorem recipWord_lt (y : Nat) (hy : y ≠ 0) (h : y < 2 ^ 64) : FvModexp.AsmDiv.recipWord y < 2 ^ 64 := by
  have hn := FvModexp.AsmDiv.clz_norm64 y hy h
  unfold FvModexp.AsmDiv.recipWord
  exact FvModexp.Arm64.RecipWordSum.recip_lt _ hn.2.1

theorem b63 (j : Nat) (h : j < 2 ^ 63) : (BitVec.ofNat 64 j).getLsbD 63 = false := by
  simp only [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow h, Bool.and_false]

/-- bytes `[o, o + n)` of `x` at a state with `z[k:n]` written: unchanged since the call -/
theorem rel_x (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (rec k : Nat) (S : State)
    (hrel : Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat rec k s S) (o n : Nat) (hi : o + n ≤ 8 * zl.toNat)
    (hk : zp = xp → o + n ≤ 8 * k) :
    S.mem.readLE (xp.toNat + o) n = s.mem.readLE (xp.toNat + o) n := by
  obtain ⟨-, -, -, -, -, -, -, hxh, hxw, hzx, -⟩ := hpre
  have hmf' : MemFrame s.mem S.mem (R.rt ++ (winA s 152 72 ++ [(zp.toNat + 8 * k, zp.toNat + 8 * zl.toNat)])) := by
    rw [← List.append_assoc]; exact hrel.mf
  have hlf' : LiveFrame s.mem S.mem L (winA s 152 72 ++ [(zp.toNat + 8 * k, zp.toNat + 8 * zl.toNat)]) :=
    FvModexp.Arm64.AddVW.liveFrame_mono hrel.lf (fun a n h => by rw [outside_append] at h; exact h.2)
  simp only [Outside, and_true] at hxw
  refine Held.readLE (hxh.sub (by omega) (by omega)) hmf' hlf' ?_
  simp only [outside_append, winA, outside_cons, outside_nil, and_true]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rcases hzx with h | h
  · have := hk h; subst h; omega
  · unfold Apart at h; omega

set_option maxRecDepth 20000 in
/-- `Rel` after an iteration: the `i` spill, `divWW` (no memory change), the store of `z[k-1]` -/
theorem rel_next (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (rec k : Nat) (hk : 1 ≤ k) (hkz : k ≤ zl.toNat) (S T S' : State)
    (hrel : Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat rec k s S)
    (hmT : MemFrame (S.mem.writeLE (s.sp.toNat - 16) 8 (k - 1)) T.mem []) (v : Nat)
    (hsp' : S'.sp = s.sp - 64#64) (h28' : S'.regs 28 = s.regs 28) (h29' : S'.regs 29 = s.sp - 72#64)
    (h18' : S'.regs 18 = s.regs 18) (hm' : S'.mem = T.mem.writeLE (zp.toNat + (k - 1) * 8) 8 v) :
    Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat rec (k - 1) s S' := by
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩, -, -, hzl, hzw, -, -, -, -, -, -⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw
  obtain ⟨-, -, -, -, h_lr, h_fp, h_z, h_x, h_xl, h_y, h_rec, hmf, hlf, hinv⟩ := hrel
  -- reads of the new memory outside `z[k-1]` and the `i` slot are reads of `S.mem`
  have hrd : ∀ a n, (a + n ≤ zp.toNat + (k - 1) * 8 ∨ zp.toNat + (k - 1) * 8 + 8 ≤ a) →
      (a + n ≤ s.sp.toNat - 16 ∨ s.sp.toNat - 8 ≤ a) → S'.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2
    rw [hm', Memory.readLE_writeLE_of_disjoint (m := T.mem) _ (by omega), hmT.readLE a n (by simp [Outside]),
      Memory.readLE_writeLE_of_disjoint (m := S.mem) _ (by omega)]
  have hacc : ∀ a n w, S'.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w
    have := hmT.accessible a n w
    rw [Memory.accessible_writeLE] at this
    rw [hm', Memory.accessible_writeLE, this, hmf.accessible]
  refine ⟨hsp', h28', h29', h18', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrd _ _ (by omega) (by omega)]; exact h_lr
  · rw [hrd _ _ (by omega) (by omega)]; exact h_fp
  · rw [hrd _ _ (by omega) (by omega)]; exact h_z
  · rw [hrd _ _ (by omega) (by omega)]; exact h_x
  · rw [hrd _ _ (by omega) (by omega)]; exact h_xl
  · rw [hrd _ _ (by omega) (by omega)]; exact h_y
  · rw [hrd _ _ (by omega) (by omega)]; exact h_rec
  · refine ⟨fun a n h => ?_, fun a n w => hacc a n w⟩
    have h' := h
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h'
    rw [hrd _ _ (by omega) (by omega)]
    refine hmf.readLE a n ?_
    simp only [outside_append, winA, outside_cons, outside_nil, and_true]
    exact ⟨⟨h'.1.1, h'.1.2.1, h'.1.2.2⟩, by omega⟩
  · refine ⟨fun a n hin h => ?_⟩
    obtain ⟨r, hr, hr1, hr2⟩ := hin
    have hs := hLs r hr
    simp only [Outside, win, outside_cons, outside_nil, and_true] at hs h
    rw [hrd _ _ (by omega) (by omega)]
    exact hlf.readLE a n ⟨r, hr, hr1, hr2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega)
  · have hst : Outside (s.sp.toNat - 16) 8 R.rt := Outside.of_sub hout (by omega) (by omega)
    have h1 := inv_store_out hinv hst (v := k - 1)
    have h2 := RtInv.inv_frame' hmT (fun r hr => by simp at hr) h1
    rw [hm']
    exact inv_store_held h2 (hzh.sub (by omega) (by omega))

/-- the value invariant after an iteration -/
theorem val_next (s : State) (zp zl xn xp y : BitVec 64) (hy : y.toNat ≠ 0) (k r : Nat) (hk : 1 ≤ k)
    (hkz : k ≤ zl.toNat) (S T S' : State) (hv : Val s zp zl xn xp y k r S) (xk : Nat)
    (hxk : xk = s.mem.readLE (xp.toNat + (k - 1) * 8) 8)
    (hTz : T.mem.readLE (zp.toNat + 8 * k) (8 * (zl.toNat - k)) = S.mem.readLE (zp.toNat + 8 * k) (8 * (zl.toNat - k)))
    (hm' : S'.mem = T.mem.writeLE (zp.toNat + (k - 1) * 8) 8 ((r * 2 ^ 64 + xk) / y.toNat)) :
    Val s zp zl xn xp y (k - 1) ((r * 2 ^ 64 + xk) % y.toNat) S' := by
  have hH := FvModexp.AsmDivVW.H_step s.mem xn.toNat xp.toNat zl.toNat k hk hkz
  obtain ⟨hr, hq⟩ := hv
  have hrl : r < y.toNat := by rw [hr]; exact Nat.mod_lt _ (by omega)
  have hxl : xk < 2 ^ 64 := by rw [hxk]; have := Memory.readLE_lt s.mem (xp.toNat + (k - 1) * 8) 8; simpa using this
  obtain ⟨e1, e2⟩ := FvModexp.AsmDivVW.inv_step _ _ r xk y.toNat (by omega) hr hq
  rw [show xp.toNat + (k - 1) * 8 = xp.toNat + 8 * (k - 1) by omega] at hxk
  refine ⟨?_, ?_⟩
  · rw [hH, ← hxk, e2]
  · rw [hm', show zp.toNat + (k - 1) * 8 = zp.toNat + 8 * (k - 1) by omega, FvModexp.AsmDivVW.q_store _ _ _ _ _ hk hkz,
      hTz, Nat.mod_eq_of_lt (FvModexp.AsmDivVW.digit_lt _ _ _ hrl hxl), e1, hH, hxk]

set_option maxRecDepth 20000 in
/-- the second half of an iteration: after `divWW` returned (`+0xa8`), store the digit, back to the head -/
theorem tail (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (r k : Nat) (hk : 1 ≤ k) (hkz : k ≤ zl.toNat) (S : State)
    (hrel : Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat (FvModexp.AsmDiv.recipWord y.toNat) k s S)
    (hv : Val s zp zl xn xp y k r S) (T : State)
    (hpcT : T.pc = BitVec.ofNat 64 (entry + 0xa8)) (hspT : T.sp = s.sp - 64#64)
    (h0T : T.regs 0 = BitVec.ofNat 64 ((r * 2 ^ 64 + s.mem.readLE (xp.toNat + (k - 1) * 8) 8) / y.toNat))
    (h1T : T.regs 1 = BitVec.ofNat 64 ((r * 2 ^ 64 + s.mem.readLE (xp.toNat + (k - 1) * 8) 8) % y.toNat))
    (h18T : T.regs 18 = s.regs 18) (h28T : T.regs 28 = s.regs 28) (h29T : T.regs 29 = s.sp - 72#64)
    (hmT : MemFrame (S.mem.writeLE (s.sp.toNat - 16) 8 (k - 1)) T.mem [])
    (IH : ∀ r' S', AtHead (FvModexp.AsmDiv.recipWord y.toNat) (k - 1) r' S' →
      Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat (FvModexp.AsmDiv.recipWord y.toNat) (k - 1) s S' →
      Val s zp zl xn xp y (k - 1) r' S' →
      Reaches ((LibDivWVW.program.link impl).withExit ret) S'
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s')) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) T
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩, hy, hxn, hzl, hzw, hxacc, hx48, hxh,
    hxw, hzx, -⟩ := hpre'
  have hrel' := hrel
  obtain ⟨hsp, h28, h29, h18, h_rd_lr', h_rd_fp', h_rd_z', h_rd_x', h_rd_xl', h_rd_y', h_rd_rec', hmf, hlf, hinv⟩ := hrel'
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw hxw
  have hT : ∀ a n, T.mem.readLE a n = (S.mem.writeLE (s.sp.toNat - 16) 8 (k - 1)).readLE a n :=
    fun a n => hmT.readLE a n (by simp [Outside])
  have hTa : ∀ a n w, T.mem.accessible a n w = S.mem.accessible a n w := by
    intro a n w; have := hmT.accessible a n w; rw [Memory.accessible_writeLE] at this
    first | exact this.symm | exact this
  have h_rd_i : T.mem.readLE (s.sp.toNat - 16) 8 = k - 1 := by
    rw [hT, Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  have h_rd_z : T.mem.readLE (s.sp.toNat + 8) 8 = zp.toNat := by
    rw [hT, Memory.readLE_writeLE_of_disjoint (m := S.mem) _ (by omega)]; exact h_rd_z'
  have h_rd_rec : T.mem.readLE (s.sp.toNat - 24) 8 = FvModexp.AsmDiv.recipWord y.toNat := by
    rw [hT, Memory.readLE_writeLE_of_disjoint (m := S.mem) _ (by omega)]; exact h_rd_rec'
  have hspn : T.sp.toNat = s.sp.toNat - 64 := by rw [hspT, BitVec.toNat_sub]; simp; omega
  have hacc : T.mem.accessible (s.sp.toNat - 152) (152 + 72) true = true := by rw [hTa, hmf.accessible]; exact hw
  have hzacc' : T.mem.accessible zp.toNat (8 * zl.toNat) true = true := by rw [hTa, hmf.accessible]; exact hzacc
  clear hLs hout
  have hTz : T.mem.readLE (zp.toNat + 8 * k) (8 * (zl.toNat - k)) =
      S.mem.readLE (zp.toNat + 8 * k) (8 * (zl.toNat - k)) := by
    rw [hT, Memory.readLE_writeLE_of_disjoint (m := S.mem) _ (by omega)]
  janus_run until [entry + 0xc4]
  refine IH _ _ ⟨rfl, ?_, ?_, ?_⟩
    (rel_next R b L ret s zp zl xn xp y hpre _ k hk hkz S T _ hrel hmT
      ((r * 2 ^ 64 + s.mem.readLE (xp.toNat + (k - 1) * 8) 8) / y.toNat) ?_ ?_ ?_ ?_ ?_)
    (val_next s zp zl xn xp y hy k r hk hkz S T _ hv _ rfl hTz ?_)
  all_goals first | with_reducible rfl | janus_simp

set_option maxRecDepth 20000 in
/-- one iteration (`k ≥ 1` limbs left): head to the return from `divWW`, then `tail` -/
theorem body (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (r k : Nat) (hk : 1 ≤ k) (hkz : k ≤ zl.toNat) (S : State)
    (hh : AtHead (FvModexp.AsmDiv.recipWord y.toNat) k r S)
    (hrel : Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat (FvModexp.AsmDiv.recipWord y.toNat) k s S)
    (hv : Val s zp zl xn xp y k r S)
    (IH : ∀ r' S', AtHead (FvModexp.AsmDiv.recipWord y.toNat) (k - 1) r' S' →
      Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat (FvModexp.AsmDiv.recipWord y.toNat) (k - 1) s S' →
      Val s zp zl xn xp y (k - 1) r' S' →
      Reaches ((LibDivWVW.program.link impl).withExit ret) S'
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s')) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  have h_rd_xk := rel_x R b L ret s zp zl xn xp y hpre _ k S hrel ((k - 1) * 8) 8 (by omega) (fun _ => by omega)
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩, hy, hxn, hzl, hzw, hxacc, hx48, hxh,
    hxw, hzx, -⟩ := hpre'
  obtain ⟨hpc, h0, h1, h2⟩ := hh
  have hrel' := hrel
  obtain ⟨hsp, h28, h29, h18, h_rd_lr, h_rd_fp, h_rd_z, h_rd_x, h_rd_xl, h_rd_y, h_rd_rec, hmf, hlf, hinv⟩ := hrel'
  have hspn : S.sp.toNat = s.sp.toNat - 64 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hacc : S.mem.accessible (s.sp.toNat - 152) (152 + 72) true = true := by rw [hmf.accessible]; exact hw
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw hxw
  have hxacc' : S.mem.accessible xp.toNat (8 * zl.toNat) false = true := by rw [hmf.accessible]; exact hxacc
  have hk1 : BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [hk1] at h1
  have hb := b63 (k - 1) (by omega)
  have hrecl := recipWord_lt y.toNat hy y.isLt
  have hrecv : (BitVec.ofNat 64 (FvModexp.AsmDiv.recipWord y.toNat)).toNat = FvModexp.AsmDiv.recipWord y.toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hrecl
  have hr : r < y.toNat := by rw [hv.1]; exact Nat.mod_lt _ (by omega)
  have hrv : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := y.isLt; omega)
  clear hLs hout
  janus_run [hb, hrecv, hrv] until [entry + 0xa8] calls [divww impl hap]
  rename_i _ hpcT hspT h0T h1T h18T h28T h29T hmT
  refine tail impl R b L ret hret s zp zl xn xp y hpre r k hk hkz S hrel hv s' ?_ ?_ ?_ ?_ ?_ ?_ ?_ hmT IH
  · rw [hpcT]; try janus_simp
  · rw [hspT]; try janus_simp
  · rw [h0T]; try janus_simp
  · rw [h1T]; try janus_simp
  · rw [h18T]; try janus_simp
  · rw [h28T]; try janus_simp
  · rw [h29T]; try janus_simp

/-- the memory at the call of `reciprocalWord`: prologue stores and spills -/
@[reducible] def M0 (s : State) (ret : Nat) (zp zl xn xp y : BitVec 64) : Memory :=
  (((((((((s.mem.writeLE (s.sp.toNat - 64) 8 ret).writeLE (s.sp.toNat - 72) 8 (s.regs 29).toNat).writeLE
        (s.sp.toNat + 40) 8 xp.toNat).writeLE (s.sp.toNat + 16) 8 zl.toNat).writeLE (s.sp.toNat + 8) 8 zp.toNat).writeLE
        (s.sp.toNat + 32) 8 xn.toNat).writeLE (s.sp.toNat + 64) 8 y.toNat).writeLE (s.sp.toNat + 40) 8 xp.toNat).writeLE
        (s.sp.toNat + 48) 8 zl.toNat)

set_option maxRecDepth 20000 in
theorem rd0 (s : State) (ret : Nat) (zp zl xn xp y : BitVec 64) (T : State)
    (hmT : MemFrame (M0 s ret zp zl xn xp y) T.mem [(s.sp.toNat - 64 - 88, s.sp.toNat - 64 - 40)])
    (a : Nat) (ha : s.sp.toNat - 104 ≤ a) : T.mem.readLE a 8 = (M0 s ret zp zl xn xp y).readLE a 8 :=
  hmT.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
/-- `Rel` at the loop head (`k = len z`), from the memory after `reciprocalWord` and the store of `rec` -/
theorem rel_init (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (hret : ret < 2 ^ 48) (rec : Nat) (hrec : rec < 2 ^ 64) (T S' : State)
    (hmT : MemFrame (M0 s ret zp zl xn xp y) T.mem [(s.sp.toNat - 64 - 88, s.sp.toNat - 64 - 40)])
    (hsp' : S'.sp = s.sp - 64#64) (h28' : S'.regs 28 = s.regs 28) (h29' : S'.regs 29 = s.sp - 72#64)
    (h18' : S'.regs 18 = s.regs 18) (hm' : S'.mem = T.mem.writeLE (s.sp.toNat - 24) 8 rec) :
    Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat rec zl.toNat s S' := by
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, hinv⟩ := hpre
  have hW0 : MemFrame s.mem (M0 s ret zp zl xn xp y) (winA s 152 72) := by
    simp only [M0, winA]; janus_frame
  have hW1 := Janus.Contracts.Libc.memFrame_trans hW0 hmT
  have hW : MemFrame s.mem S'.mem (winA s 152 72) := by
    rw [hm']
    refine ⟨fun a n h => ?_, fun a n w => ?_⟩
    · have h' := h
      simp only [winA, outside_cons, outside_nil, and_true] at h'
      rw [Memory.readLE_writeLE_of_disjoint (m := T.mem) _ (by omega)]
      exact hW1.readLE a n (by simp only [winA, outside_append, outside_cons, outside_nil, and_true]; omega)
    · rw [Memory.accessible_writeLE, hW1.accessible]
  have hrd : ∀ a, s.sp.toNat - 104 ≤ a → (a + 8 ≤ s.sp.toNat - 24 ∨ s.sp.toNat - 16 ≤ a) →
      S'.mem.readLE a 8 = (M0 s ret zp zl xn xp y).readLE a 8 := by
    intro a h1 h2
    rw [hm', Memory.readLE_writeLE_of_disjoint (m := T.mem) _ (by omega), rd0 s ret zp zl xn xp y T hmT a h1]
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 152 ∨ s.sp.toNat + 72 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; exact this
  have hwin : ∀ r ∈ winA s 152 72, s.sp.toNat - 152 ≤ r.1 ∧ r.2 ≤ s.sp.toNat + 72 := by
    simp only [winA, List.mem_cons, List.mem_nil_iff, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega
  refine ⟨hsp', h28', h29', h18', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrd _ (by omega) (by omega)]
    simp (disch := omega) only [M0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [hrd _ (by omega) (by omega)]
    simp (disch := omega) only [M0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 29).isLt
  · rw [hrd _ (by omega) (by omega)]
    simp (disch := omega) only [M0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt zp.isLt
  · rw [hrd _ (by omega) (by omega)]
    simp (disch := omega) only [M0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt xp.isLt
  · rw [hrd _ (by omega) (by omega)]
    simp (disch := omega) only [M0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt zl.isLt
  · rw [hrd _ (by omega) (by omega)]
    simp (disch := omega) only [M0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt y.isLt
  · rw [hm', Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt hrec
  · exact hW.mono fun a n h => by
      simp only [outside_append] at h; exact h.1.2
  · refine liveFrame_of_frame (rs := winA s 152 72) ?_ hLs' hwin
    exact hW.mono fun a n h => by simp only [outside_append] at h; exact h.1
  · exact inv_frame_winA hW hout (by omega) (by omega) hinv

/-- the loop, by induction on the number `k` of limbs left -/
theorem loop (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) :
    ∀ k r (S : State), k ≤ zl.toNat → AtHead (FvModexp.AsmDiv.recipWord y.toNat) k r S →
      Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat (FvModexp.AsmDiv.recipWord y.toNat) k s S →
      Val s zp zl xn xp y k r S →
      Reaches ((LibDivWVW.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  intro k
  induction k with
  | zero => intro r S _ hh hrel hv; exact fin impl R b L ret hret s zp zl xn xp y hpre _ r S hh hrel hv
  | succ k ih =>
    intro r S hk hh hrel hv
    exact body impl hap R b L ret hret s zp zl xn xp y hpre r (k + 1) (by omega) hk S hh hrel hv
      (fun r' S' h1 h2 h3 => ih r' S' (by omega) h1 h2 h3)

set_option maxRecDepth 20000 in
/-- after `reciprocalWord` returned (`+0x44`): store `rec`, `i = len z - 1`, `r = xn`, to the loop head, then `loop` -/
theorem gen2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (T : State)
    (hpcT : T.pc = BitVec.ofNat 64 (entry + 0x44)) (hspT : T.sp = s.sp - 64#64)
    (h0T : T.regs 0 = BitVec.ofNat 64 (FvModexp.AsmDiv.recipWord y.toNat))
    (h18T : T.regs 18 = s.regs 18) (h28T : T.regs 28 = s.regs 28) (h29T : T.regs 29 = s.sp - 72#64)
    (hmT : MemFrame (M0 s ret zp zl xn xp y) T.mem [(s.sp.toNat - 64 - 88, s.sp.toNat - 64 - 40)]) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) T
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, -, -, -, -, -⟩, hy, hxn, -⟩ := hpre'
  have hTa : ∀ a n w, T.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [hmT.accessible]; simp only [M0, Memory.accessible_writeLE]
  have hacc : T.mem.accessible (s.sp.toNat - 152) (152 + 72) true = true := by rw [hTa]; exact hw
  have hspn : T.sp.toNat = s.sp.toNat - 64 := by rw [hspT, BitVec.toNat_sub]; simp; omega
  have h_rd_zl : T.mem.readLE (s.sp.toNat + 16) 8 = zl.toNat := by
    rw [rd0 s ret zp zl xn xp y T hmT _ (by omega)]
    simp (disch := omega) only [M0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt zl.isLt
  have h_rd_xn : T.mem.readLE (s.sp.toNat + 32) 8 = xn.toNat := by
    rw [rd0 s ret zp zl xn xp y T hmT _ (by omega)]
    simp (disch := omega) only [M0, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt xn.isLt
  have hrecl := recipWord_lt y.toNat hy y.isLt
  have hrecv : (BitVec.ofNat 64 (FvModexp.AsmDiv.recipWord y.toNat)).toNat = FvModexp.AsmDiv.recipWord y.toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hrecl
  have hret48 : ret < 2 ^ 48 := hret.user
  janus_run [hrecv] until [entry + 0xc4]
  refine loop impl hap R b L ret hret s zp zl xn xp y hpre zl.toNat xn.toNat _ (Nat.le_refl _) ⟨rfl, ?_, ?_, ?_⟩
    (rel_init R b L ret s zp zl xn xp y hpre hret48 _ hrecl T _ hmT ?_ ?_ ?_ ?_ ?_) ⟨?_, ?_⟩
  all_goals first | with_reducible rfl | janus_simp | skip
  · rw [FvModexp.AsmDivVW.H_top, Nat.mod_eq_of_lt hxn]
  · rw [Nat.sub_self, Nat.mul_zero, Memory.readLE_zero_eq, FvModexp.AsmDivVW.H_top, Nat.div_eq_of_lt hxn]

set_option maxRecDepth 20000 in
/-- the entry for `len x ≠ 1`: prologue, spills, `reciprocalWord(y)` -/
theorem gen1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl zc xn xp xc y : BitVec 64)
    (hs : s.pc = BitVec.ofNat 64 entry) (hx0 : s.regs 0 = zp) (hx1 : s.regs 1 = zl) (hx2 : s.regs 2 = zc)
    (hx3 : s.regs 3 = xn) (hx4 : s.regs 4 = xp) (hx5 : s.regs 5 = zl) (hx6 : s.regs 6 = xc) (hx7 : s.regs 7 = y)
    (h30 : s.regs 30 = BitVec.ofNat 64 ret)
    (hpre : Pre R b L zp zl xn xp y s) (hne : zl.toNat ≠ 1) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) s
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, hLs, -⟩, hy, hxn, -⟩ := hpre'
  have hne' : (zl = 1#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; apply hne; rw [h]; rfl
  clear hLs hout
  janus_run [hne'] until [entry + 0x44] calls [recip impl hap]
  rename_i _ hpcT hspT h0T h18T h28T h29T hmT
  refine gen2 impl hap R b L ret hret s zp zl xn xp y hpre s' ?_ ?_ ?_ ?_ ?_ ?_ hmT
  · rw [hpcT]; try janus_simp
  · rw [hspT]; try janus_simp
  · rw [h0T]; try janus_simp
  · rw [h18T]; try janus_simp
  · rw [h28T]; try janus_simp
  · rw [h29T]; try janus_simp

/-- the memory at the call of `math/bits.Div64` (`len x = 1`) -/
@[reducible] def M1 (s : State) (ret : Nat) (zp xp : BitVec 64) : Memory :=
  (((((s.mem.writeLE (s.sp.toNat - 64) 8 ret).writeLE (s.sp.toNat - 72) 8 (s.regs 29).toNat).writeLE
        (s.sp.toNat + 40) 8 xp.toNat).writeLE (s.sp.toNat + 16) 8 1).writeLE (s.sp.toNat + 8) 8 zp.toNat)

set_option maxRecDepth 20000 in
/-- after `Div64` returned (`len x = 1`, `+0x68`): store `z[0]`, return the remainder -/
theorem one2 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (hz1 : zl.toNat = 1) (T : State)
    (hpcT : T.pc = BitVec.ofNat 64 (entry + 0x68)) (hspT : T.sp = s.sp - 64#64)
    (h0T : (T.regs 0).toNat = (xn.toNat * 2 ^ 64 + s.mem.readLE xp.toNat 8) / y.toNat)
    (h1T : (T.regs 1).toNat = (xn.toNat * 2 ^ 64 + s.mem.readLE xp.toNat 8) % y.toNat)
    (h18T : T.regs 18 = s.regs 18) (h28T : T.regs 28 = s.regs 28) (h29T : T.regs 29 = s.sp - 72#64)
    (hmT : MemFrame (M1 s ret zp xp) T.mem [(s.sp.toNat - 64 - 40, s.sp.toNat - 64 - 24)]) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) T
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩, hy, hxn, hzl, hzw, -, -, -, -, -, hinv⟩ := hpre'
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw
  have hW0 : MemFrame s.mem (M1 s ret zp xp) (winA s 152 72) := by
    simp only [M1, winA]; janus_frame
  have hW1' := Janus.Contracts.Libc.memFrame_trans hW0 hmT
  have hW1 : MemFrame s.mem T.mem (winA s 152 72) := hW1'.mono fun a n h => by
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hTa : ∀ a n w, T.mem.accessible a n w = s.mem.accessible a n w := fun a n w => hW1.accessible a n w
  have hacc : T.mem.accessible (s.sp.toNat - 152) (152 + 72) true = true := by rw [hTa]; exact hw
  have hzacc' : T.mem.accessible zp.toNat (8 * zl.toNat) true = true := by rw [hTa]; exact hzacc
  have hspn : T.sp.toNat = s.sp.toNat - 64 := by rw [hspT, BitVec.toNat_sub]; simp; omega
  have hrd : ∀ a, s.sp.toNat - 64 ≤ a → T.mem.readLE a 8 = (M1 s ret zp xp).readLE a 8 :=
    fun a h => hmT.readLE a 8 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have h_rd_zl : T.mem.readLE (s.sp.toNat + 16) 8 = 1 := by
    rw [hrd _ (by omega)]
    simp (disch := omega) only [M1, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  have h_rd_z : T.mem.readLE (s.sp.toNat + 8) 8 = zp.toNat := by
    rw [hrd _ (by omega)]
    simp (disch := omega) only [M1, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt zp.isLt
  have h_rd_fp : T.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat := by
    rw [hmT.readLE _ 8 (by simp only [outside_cons, outside_nil, and_true]; omega)]
    simp (disch := omega) only [M1, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 29).isLt
  have h_rd_lr : T.mem.readLE (s.sp.toNat - 64) 8 = ret := by
    rw [hrd _ (by omega)]
    simp (disch := omega) only [M1, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := hret.user; omega)
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 152 ∨ s.sp.toNat + 72 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; exact this
  have hwin : ∀ r ∈ winA s 152 72, s.sp.toNat - 152 ≤ r.1 ∧ r.2 ≤ s.sp.toNat + 72 := by
    simp only [winA, List.mem_cons, List.mem_nil_iff, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega
  have hWz : ∀ v, MemFrame s.mem (T.mem.writeLE zp.toNat 8 v) (winA s 152 72 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) := by
    intro v
    refine ⟨fun a n h => ?_, fun a n w => by rw [Memory.accessible_writeLE]; exact hW1.accessible a n w⟩
    have h' := h
    simp only [winA, outside_append, outside_cons, outside_nil, and_true] at h'
    rw [Memory.readLE_writeLE_of_disjoint (m := T.mem) _ (by omega)]
    exact hW1.readLE a n (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have hq := FvModexp.AsmDivVW.digit_lt xn.toNat (s.mem.readLE xp.toNat 8) y.toNat hxn
    (by have := Memory.readLE_lt s.mem xp.toNat 8; simpa using this)
  have hinvT : R.inv b L (s.regs 28).toNat (view R.rt L T.mem) := inv_frame_winA hW1 hout (by omega) (by omega) hinv
  clear hLs
  janus_run
  refine ⟨?_, ?_, L, b, LiveExt.refl R L, Nat.le_refl _, ?_, ?_, ?_⟩
  · show (T.regs 1).toNat = (xn.toNat * 2 ^ (64 * zl.toNat) + s.mem.readLE xp.toNat (8 * zl.toNat)) % y.toNat
    rw [h1T, hz1]
  · show (T.mem.writeLE zp.toNat 8 (T.regs 0).toNat).readLE zp.toNat (8 * zl.toNat) =
      (xn.toNat * 2 ^ (64 * zl.toNat) + s.mem.readLE xp.toNat (8 * zl.toNat)) / y.toNat
    rw [hz1, Nat.mul_one, Nat.mul_one, Memory.readLE_writeLE_self, h0T]
    exact Nat.mod_eq_of_lt hq
  · exact inv_store_held hinvT (hzh.sub (Nat.le_refl _) (by omega))
  · exact (hWz _).mono fun a n h => by simp only [outside_append] at h ⊢; exact ⟨h.1.2, h.2⟩
  · exact liveFrame_of_frame (rs := winA s 152 72) (hWz _) hLs' hwin

set_option maxRecDepth 20000 in
/-- the entry for `len x = 1`: prologue, `bits.Div(xn, x[0], y)` -/
theorem one1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl zc xn xp xc y : BitVec 64)
    (hs : s.pc = BitVec.ofNat 64 entry) (hx0 : s.regs 0 = zp) (hx1 : s.regs 1 = zl) (hx2 : s.regs 2 = zc)
    (hx3 : s.regs 3 = xn) (hx4 : s.regs 4 = xp) (hx5 : s.regs 5 = zl) (hx6 : s.regs 6 = xc) (hx7 : s.regs 7 = y)
    (h30 : s.regs 30 = BitVec.ofNat 64 ret)
    (hpre : Pre R b L zp zl xn xp y s) (h1 : zl.toNat = 1) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) s
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, -, hLs, -⟩, hy, hxn, hzl, hzw, hxacc, hx48, -,
    hxw, -⟩ := hpre'
  simp only [Outside, and_true] at hxw
  have he : (zl = 1#64) = True := by
    simp only [eq_iff_iff, iff_true]; exact BitVec.eq_of_toNat_eq (by rw [h1]; rfl)
  clear hLs hout
  janus_run [he] until [entry + 0x68] calls [div64 impl hap]
  rename_i _ hpcT hspT h28T h29T h18T h0T h1T hmT
  refine one2 impl R b L ret hret s zp zl xn xp y hpre h1 s' ?_ ?_ h0T h1T ?_ ?_ ?_ hmT
  · rw [hpcT]; try janus_simp
  · rw [hspT]; try janus_simp
  · rw [h18T]; try janus_simp
  · rw [h28T]; try janus_simp
  · rw [h29T]; try janus_simp

/-- `divWVW` on the library program -/
theorem ens_lib (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xn xp xl xc y : BitVec 64) :
    Ensures (LibDivWVW.program.link impl) entry [zp, zl, zc, xn, xp, xl, xc, y]
      (fun s => xl = zl ∧ Pre R b L zp zl xn xp y s) (fun s s' => Post R b L zp zl xn xp y s s') := by
  intro ret hret s hs ⟨hxz, hpre⟩
  janus_intro hs
  subst hxz
  have hpc : s.pc = BitVec.ofNat 64 entry := by rw [h_pc]; rfl
  by_cases h1 : xl.toNat = 1
  · refine Janus.Tactic.returns_of_reaches ?_
    exact one1 impl hap R b L ret hret s zp xl zc xn xp xc y hpc h_x0 h_x1 h_x2 h_x3 h_x4 h_x5 h_x6 h_x7 h_lr hpre h1
  · refine Janus.Tactic.returns_of_reaches ?_
    exact gen1 impl hap R b L ret hret s zp xl zc xn xp xc y hpc h_x0 h_x1 h_x2 h_x3 h_x4 h_x5 h_x6 h_x7 h_lr hpre h1

/-- **`divWVW` (arm64)**, CONVENTIONS §3 shape (`Pre`/`Post` above; `xl = zl` is Go's `len(z) = len(x)` contract):
`X0 = (xn·B^n + x) mod y`, `z[0:n] = (xn·B^n + x) / y` for `y ≠ 0`, `xn < y`, `z = x` or apart -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xn xp xl xc y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xn, xp, xl, xc, y]
      (fun s => xl = zl ∧ Pre R b L zp zl xn xp y s) (fun s s' => Post R b L zp zl xn xp y s s') := by
  have e : Extracted.program.onlySegments names = LibDivWVW.program := LibDivWVW.eq_only.symm
  rw [e]
  exact ens_lib impl hap R b L zp zl zc xn xp xl xc y

set_option linter.defProp false in
/-- `ens` as a callee summary inside a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4) -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xn xp xl xc y : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R b L zp zl zc xn xp xl xc y) (noExit_restrict hap names)
    (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.DivWVW
