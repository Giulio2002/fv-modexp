import FvModexp.Proofs.Amd64.Nat.LibDivWVW
import FvModexp.Proofs.Amd64.Nat.AddVW
import FvModexp.Proofs.Amd64.DivWWSum
import FvModexp.Proofs.Common.AsmDivVW

/-!
# `math/big.divWVW(z []Word, xn Word, x []Word, y Word) (r Word)` (go-bigmodexpfix natdiv.go:579, Go ABIInternal, amd64)

The amd64 twin of `FvModexp.Arm64.DivWVW` (same Go source; see there and `Common/AsmDivVW.lean`). Arguments
`RAX, RBX, RCX = z`, `RDI = xn`, `RSI, R8, R9 = x`, `R10 = y`; frame `PUSH RBP; SUB $0x30` (spills up to caller
`RSP + 72`); `reciprocalWord` and `bits.Div` are inlined (`BSR`/`SHL`/`DIVQ`), the only call is `divWW` (frameless, its
return slot at `RSP - 64`): the window is `[RSP - 64, RSP + 72)`. Callee summary: `Amd64.DivWWSum.divWW_summary`.
Proof split (one `janus64_run` per declaration): `fin`, `body` (head to the return from `divWW`), `tail`, `loop`,
`gen` (`len x ≠ 1`, entry to the head), `one` (`len x = 1`), `ens_lib`, `ens`, `sum`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

set_option linter.unusedSimpArgs false
set_option linter.janusRenameI false

namespace FvModexp.Amd64.DivWVW

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.divWVW"
def names : List String := LibDivWVW.names

abbrev entry : Nat := segAddr Extracted.program fn

set_option maxRecDepth 100000 in
theorem codeIn_divww (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    CodeIn64 FvModexp.Lib.DivWWAmd64.program (LibDivWVW.program.link impl) := by
  rw [LibDivWVW.eq_only]
  exact codeIn_single hap (seg := Extracted.seg61) rfl
    (List.getElem_mem (l := Extracted.program.segments) (n := 61) (by decide)) (by decide)

theorem divww (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    Summary (LibDivWVW.program.link impl) FvModexp.Lib.DivWWAmd64.entry
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.mem.accessible (s.regs 4).toNat 8 false = true ∧
        (s.regs 1).toNat ≠ 0 ∧ (s.regs 0).toNat < (s.regs 1).toNat ∧
        (s.regs 7).toNat = FvModexp.AsmDiv.recipWord (s.regs 1).toNat)
      (fun s s' => s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8#64 ∧
        s'.regs 0 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat) / (s.regs 1).toNat) ∧
        s'.regs 3 = BitVec.ofNat 64 (((s.regs 0).toNat * 2 ^ 64 + (s.regs 3).toNat) % (s.regs 1).toNat) ∧
        s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ MemFrame s.mem s'.mem [] ∧
        s'.xmm = s.xmm ∧ s'.fsBase = s.fsBase ∧ s'.df = s.df) := by
  refine Summary.mono (Summary.of_codeIn64 (codeIn_divww impl hap) FvModexp.Amd64.DivWWSum.divWW_summary)
    (fun _ h => h) ?_
  intro s s' _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact ⟨h1, h2, h3, h4, h5 5 (by decide), h5 14 (by decide), h6, h7, h8, h9⟩

/-! ## Statement -/

/-- the precondition (`xl = zl` separately) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl xn xp y : BitVec 64) (s : State) : Prop :=
  CallEnvND R L s 64 72 ∧ y.toNat ≠ 0 ∧ xn.toNat < y.toNat ∧
    NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 64 72) ∧
    s.mem.accessible xp.toNat (8 * zl.toNat) false = true ∧ xp.toNat + 8 * zl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * zl.toNat) ∧ Outside xp.toNat (8 * zl.toNat) (win s 64 72) ∧
    (zp = xp ∨ Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * zl.toNat)) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- the dividend `xn·B^n + x` -/
@[reducible] def Dvd (m : Memory) (zl xn xp : BitVec 64) : Nat :=
  xn.toNat * 2 ^ (64 * zl.toNat) + natVal m xp.toNat zl.toNat

/-- the postcondition -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl xn xp y : BitVec 64) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
    (s'.regs 0).toNat = Dvd s.mem zl xn xp % y.toNat ∧
    natVal s'.mem zp.toNat zl.toNat = Dvd s.mem zl xn xp / y.toNat ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 64 72 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)]

/-- a state `S` inside the frame against the call state `s`: limbs `z[k:n]` written, the spill slots -/
structure Rel (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret zp xp zl y rec k : Nat) (s S : State) : Prop where
  sp : S.regs 4 = s.regs 4 - 56#64
  fp : S.regs 5 = s.regs 4 - 8#64
  g : S.regs 14 = s.regs 14
  x15 : S.xmm 15 = s.xmm 15
  x15z : s.xmm 15 = 0#128
  df : S.df = false
  fs : S.fsBase = s.fsBase
  lr : S.mem.readLE (s.regs 4).toNat 8 = ret
  sfp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  rz : S.mem.readLE ((s.regs 4).toNat + 8) 8 = zp
  rx : S.mem.readLE ((s.regs 4).toNat + 40) 8 = xp
  rxl : S.mem.readLE ((s.regs 4).toNat + 48) 8 = zl
  ry : S.mem.readLE ((s.regs 4).toNat + 64) 8 = y
  rrec : S.mem.readLE ((s.regs 4).toNat - 16) 8 = rec
  mf : MemFrame s.mem S.mem (R.rt ++ win s 64 72 ++ [(zp + 8 * k, zp + 8 * zl)])
  lf : LiveFrame s.mem S.mem L [(zp + 8 * k, zp + 8 * zl)]
  inv : R.inv b L (s.regs 14).toNat (view R.rt L S.mem)
  df0 : s.df = false

/-- the loop head (`TESTQ R9, R9` at `+0x127`), `k` limbs left (`i = k - 1`), remainder `r` -/
def AtHead (zl xp y : BitVec 64) (rec k r : Nat) (S : State) : Prop :=
  S.rip = BitVec.ofNat 64 (entry + 0x127) ∧ S.regs 0 = BitVec.ofNat 64 rec ∧ S.regs 7 = BitVec.ofNat 64 r ∧
    S.regs 9 = BitVec.ofNat 64 k - 1#64 ∧ S.regs 6 = xp ∧ S.regs 8 = zl ∧ S.regs 10 = y

/-- the loop's value invariant -/
def Val (s : State) (zp zl xn xp y : BitVec 64) (k r : Nat) (S : State) : Prop :=
  r = FvModexp.AsmDivVW.H s.mem xn.toNat xp.toNat zl.toNat k % y.toNat ∧
    S.mem.readLE (zp.toNat + 8 * k) (8 * (zl.toNat - k)) = FvModexp.AsmDivVW.H s.mem xn.toNat xp.toNat zl.toNat k / y.toNat

set_option maxRecDepth 20000 in
/-- the loop exit (`k = 0`): return `r` -/
theorem fin (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (rec r : Nat) (S : State) (hh : AtHead zl xp y rec 0 r S)
    (hrel : Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat rec 0 s S) (hv : Val s zp zl xn xp y 0 r S) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, -⟩, hy, hxn, -⟩ := hpre
  try simp only [regSP] at hb' ha hw
  obtain ⟨hpc, h0, h7, h9, h6, h8, h10⟩ := hh
  obtain ⟨hsp, h5', h14, h15, hx15, hdf, hfs, h_rd_lr, h_rd_fp, -, -, -, -, -, hmf, hlf, hinv, hdfR⟩ := hrel
  obtain ⟨hr, hq⟩ := hv
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 56 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hacc : S.mem.accessible ((s.regs 4).toNat - 64) (64 + 72) true = true := by rw [hmf.accessible]; exact hw
  have hr64 : r < 2 ^ 64 := by
    have := Nat.mod_lt (FvModexp.AsmDivVW.H s.mem xn.toNat xp.toNat zl.toNat 0) (show 0 < y.toNat by omega)
    have := y.isLt; omega
  janus64_run [BitVec.msb_eq_decide]
  refine ⟨hfs, by simp only [hdf, hdfR], ?_, ?_, L, b, LiveExt.refl R L, Nat.le_refl _, hinv, ?_, ?_⟩
  · show (BitVec.ofNat 64 r).toNat = (xn.toNat * 2 ^ (64 * zl.toNat) + s.mem.readLE xp.toNat (8 * zl.toNat)) % y.toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr64, hr, FvModexp.AsmDivVW.H_zero]
  · show S.mem.readLE zp.toNat (8 * zl.toNat) = (xn.toNat * 2 ^ (64 * zl.toNat) + s.mem.readLE xp.toNat (8 * zl.toNat)) / y.toNat
    rw [← FvModexp.AsmDivVW.H_zero]; simpa using hq
  · simpa using hmf
  · simpa using hlf

theorem b63 (j : Nat) (h : j < 2 ^ 63) : (BitVec.ofNat 64 j).msb = false := by
  rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, Nat.not_le]; omega

/-- bytes `[o, o + n)` of `x` at a state with `z[k:n]` written: unchanged since the call -/
theorem rel_x (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (rec k : Nat) (S : State)
    (hrel : Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat rec k s S) (o n : Nat) (hi : o + n ≤ 8 * zl.toNat)
    (hk : zp = xp → o + n ≤ 8 * k) :
    S.mem.readLE (xp.toNat + o) n = s.mem.readLE (xp.toNat + o) n := by
  obtain ⟨-, -, -, -, -, -, -, hxh, hxw, hzx, -⟩ := hpre
  have hmf' : MemFrame s.mem S.mem (R.rt ++ (win s 64 72 ++ [(zp.toNat + 8 * k, zp.toNat + 8 * zl.toNat)])) := by
    rw [← List.append_assoc]; exact hrel.mf
  have hlf' : LiveFrame s.mem S.mem L (win s 64 72 ++ [(zp.toNat + 8 * k, zp.toNat + 8 * zl.toNat)]) :=
    FvModexp.Amd64.AddVW.liveFrame_mono hrel.lf (fun a n h => by rw [outside_append] at h; exact h.2)
  simp only [Outside, and_true] at hxw
  refine Held.readLE (hxh.sub (by omega) (by omega)) hmf' hlf' ?_
  simp only [outside_append, win, outside_cons, outside_nil, and_true]
  refine ⟨by omega, ?_⟩
  rcases hzx with h | h
  · have := hk h; subst h; omega
  · unfold Apart at h; omega

set_option maxRecDepth 20000 in
/-- `Rel` after an iteration: the `i` spill, the return slot of `divWW`, the store of `z[k-1]` -/
theorem rel_next (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (rec k ra : Nat) (hk : 1 ≤ k) (hkz : k ≤ zl.toNat) (S T S' : State)
    (hrel : Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat rec k s S)
    (hmT : MemFrame ((S.mem.writeLE ((s.regs 4).toNat - 24) 8 (k - 1)).writeLE ((s.regs 4).toNat - 64) 8 ra) T.mem [])
    (v : Nat) (hsp' : S'.regs 4 = s.regs 4 - 56#64) (h5' : S'.regs 5 = s.regs 4 - 8#64)
    (h14' : S'.regs 14 = s.regs 14) (hx' : S'.xmm 15 = s.xmm 15) (hdf' : S'.df = false)
    (hfs' : S'.fsBase = s.fsBase) (hm' : S'.mem = T.mem.writeLE (zp.toNat + (k - 1) * 8) 8 v) :
    Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat rec (k - 1) s S' := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, hout, -, -, hLs, -⟩, -, -, hzl, hzw, -, -, -, -, -, -⟩ := hpre
  try simp only [regSP] at hb' ha hw
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw
  obtain ⟨-, -, -, -, hx15z, -, -, h_lr, h_fp, h_z, h_x, h_xl, h_y, h_rec, hmf, hlf, hinv, hdfR⟩ := hrel
  have hrd : ∀ a n, (a + n ≤ zp.toNat + (k - 1) * 8 ∨ zp.toNat + (k - 1) * 8 + 8 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 24 ∨ (s.regs 4).toNat - 16 ≤ a) →
      (a + n ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat - 56 ≤ a) → S'.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2 h3
    rw [hm', Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := T.mem) _ (by omega), hmT.readLE a n (by simp [Outside]),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := S.mem) _ (by omega)]
  have hacc : ∀ a n w, S'.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w
    have := hmT.accessible a n w
    rw [Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.accessible_writeLE] at this
    rw [hm', Janus.Arm64.Memory.accessible_writeLE, this, hmf.accessible]
  refine ⟨hsp', h5', h14', hx', hx15z, hdf', hfs', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdfR⟩
  · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h_lr
  · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h_fp
  · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h_z
  · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h_x
  · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h_xl
  · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h_y
  · rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h_rec
  · refine ⟨fun a n h => ?_, fun a n w => hacc a n w⟩
    have h' := h
    simp only [outside_append, win, outside_cons, outside_nil, and_true] at h'
    rw [hrd _ _ (by omega) (by omega) (by omega)]
    refine hmf.readLE a n ?_
    simp only [outside_append, win, outside_cons, outside_nil, and_true]
    exact ⟨⟨h'.1.1, h'.1.2⟩, by omega⟩
  · refine ⟨fun a n hin h => ?_⟩
    obtain ⟨r, hr, hr1, hr2⟩ := hin
    have hs := hLs r hr
    simp only [Outside, win, outside_cons, outside_nil, and_true] at hs h
    rw [hrd _ _ (by omega) (by omega) (by omega)]
    exact hlf.readLE a n ⟨r, hr, hr1, hr2⟩ (by simp only [outside_cons, outside_nil, and_true]; omega)
  · have hst : Outside ((s.regs 4).toNat - 24) 8 R.rt := Outside.of_sub hout (by omega) (by omega)
    have hst2 : Outside ((s.regs 4).toNat - 64) 8 R.rt := Outside.of_sub hout (by omega) (by omega)
    have h1 := inv_store_out (inv_store_out hinv hst (v := k - 1)) hst2 (v := ra)
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
  have hxl : xk < 2 ^ 64 := by
    rw [hxk]; have := Janus.Arm64.Memory.readLE_lt s.mem (xp.toNat + (k - 1) * 8) 8; simpa using this
  obtain ⟨e1, e2⟩ := FvModexp.AsmDivVW.inv_step _ _ r xk y.toNat (by omega) hr hq
  rw [show xp.toNat + (k - 1) * 8 = xp.toNat + 8 * (k - 1) by omega] at hxk
  refine ⟨?_, ?_⟩
  · rw [hH, ← hxk, e2]
  · rw [hm', show zp.toNat + (k - 1) * 8 = zp.toNat + 8 * (k - 1) by omega, FvModexp.AsmDivVW.q_store _ _ _ _ _ hk hkz,
      hTz, Nat.mod_eq_of_lt (FvModexp.AsmDivVW.digit_lt _ _ _ hrl hxl), e1, hH, hxk]

set_option maxRecDepth 20000 in
/-- the second half of an iteration: after `divWW` returned (`+0xff`), store the digit, reload, back to the head -/
theorem tail (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (r k : Nat) (hk : 1 ≤ k) (hkz : k ≤ zl.toNat) (S : State)
    (hrel : Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat (FvModexp.AsmDiv.recipWord y.toNat) k s S)
    (hv : Val s zp zl xn xp y k r S) (T : State)
    (hpcT : T.rip = BitVec.ofNat 64 (entry + 0xff)) (hspT : T.regs 4 = s.regs 4 - 56#64)
    (h0T : T.regs 0 = BitVec.ofNat 64 ((r * 2 ^ 64 + s.mem.readLE (xp.toNat + (k - 1) * 8) 8) / y.toNat))
    (h3T : T.regs 3 = BitVec.ofNat 64 ((r * 2 ^ 64 + s.mem.readLE (xp.toNat + (k - 1) * 8) 8) % y.toNat))
    (h5T : T.regs 5 = s.regs 4 - 8#64) (h14T : T.regs 14 = s.regs 14) (hxT : T.xmm 15 = s.xmm 15)
    (hfsT : T.fsBase = s.fsBase) (hdfT : T.df = false)
    (hmT : MemFrame ((S.mem.writeLE ((s.regs 4).toNat - 24) 8 (k - 1)).writeLE ((s.regs 4).toNat - 64) 8 6219871)
      T.mem [])
    (IH : ∀ r' S', AtHead zl xp y (FvModexp.AsmDiv.recipWord y.toNat) (k - 1) r' S' →
      Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat (FvModexp.AsmDiv.recipWord y.toNat) (k - 1) s S' →
      Val s zp zl xn xp y (k - 1) r' S' →
      Reaches ((LibDivWVW.program.link impl).withExit ret) S'
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s')) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) T
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, -⟩, hy, hxn, hzl, hzw, hxacc, hx48, hxh,
    hxw, hzx, -⟩ := hpre'
  try simp only [regSP] at hb' ha hw
  have hrel' := hrel
  obtain ⟨hsp, h5', h14, h15, hx15, hdf, hfs, h_rd_lr', h_rd_fp', h_rd_z', h_rd_x', h_rd_xl', h_rd_y', h_rd_rec', hmf,
    hlf, hinv, hdfR⟩ := hrel'
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw hxw
  have hT : ∀ a n, T.mem.readLE a n =
      ((S.mem.writeLE ((s.regs 4).toNat - 24) 8 (k - 1)).writeLE ((s.regs 4).toNat - 64) 8 6219871).readLE a n :=
    fun a n => hmT.readLE a n (by simp [Outside])
  have hTa : ∀ a n w, T.mem.accessible a n w = S.mem.accessible a n w := by
    intro a n w; have := hmT.accessible a n w
    rw [Janus.Arm64.Memory.accessible_writeLE, Janus.Arm64.Memory.accessible_writeLE] at this
    first | exact this.symm | exact this
  have hW : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat - 56 ≤ a) →
      (a + 8 ≤ (s.regs 4).toNat - 24 ∨ (s.regs 4).toNat - 16 ≤ a) → T.mem.readLE a 8 = S.mem.readLE a 8 := by
    intro a h1 h2
    rw [hT, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := S.mem) _ (by omega)]
  have h_rd_i : T.mem.readLE ((s.regs 4).toNat - 24) 8 = k - 1 := by
    rw [hT, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  have h_rd_z : T.mem.readLE ((s.regs 4).toNat + 8) 8 = zp.toNat := by rw [hW _ (by omega) (by omega)]; exact h_rd_z'
  have h_rd_x : T.mem.readLE ((s.regs 4).toNat + 40) 8 = xp.toNat := by rw [hW _ (by omega) (by omega)]; exact h_rd_x'
  have h_rd_xl : T.mem.readLE ((s.regs 4).toNat + 48) 8 = zl.toNat := by rw [hW _ (by omega) (by omega)]; exact h_rd_xl'
  have h_rd_y : T.mem.readLE ((s.regs 4).toNat + 64) 8 = y.toNat := by rw [hW _ (by omega) (by omega)]; exact h_rd_y'
  have h_rd_rec : T.mem.readLE ((s.regs 4).toNat - 16) 8 = FvModexp.AsmDiv.recipWord y.toNat := by
    rw [hW _ (by omega) (by omega)]; exact h_rd_rec'
  have hspn : (T.regs 4).toNat = (s.regs 4).toNat - 56 := by rw [hspT, BitVec.toNat_sub]; simp; omega
  have hacc : T.mem.accessible ((s.regs 4).toNat - 64) (64 + 72) true = true := by rw [hTa, hmf.accessible]; exact hw
  have hzacc' : T.mem.accessible zp.toNat (8 * zl.toNat) true = true := by rw [hTa, hmf.accessible]; exact hzacc
  have hTz : T.mem.readLE (zp.toNat + 8 * k) (8 * (zl.toNat - k)) =
      S.mem.readLE (zp.toNat + 8 * k) (8 * (zl.toNat - k)) := by
    rw [hT, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := S.mem) _ (by omega)]
  clear hLs hout
  janus64_run until [entry + 0x127]
  refine IH _ _ ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (rel_next R b L ret s zp zl xn xp y hpre _ k 6219871 hk hkz S T _ hrel hmT
      ((r * 2 ^ 64 + s.mem.readLE (xp.toNat + (k - 1) * 8) 8) / y.toNat) ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    (val_next s zp zl xn xp y hy k r hk hkz S T _ hv _ rfl hTz ?_)
  all_goals first | with_reducible rfl | janus64_simp | skip
  exact hfsT

set_option maxRecDepth 20000 in
/-- one iteration (`k ≥ 1` limbs left): head to the return from `divWW`, then `tail` -/
theorem body (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (r k : Nat) (hk : 1 ≤ k) (hkz : k ≤ zl.toNat) (S : State)
    (hh : AtHead zl xp y (FvModexp.AsmDiv.recipWord y.toNat) k r S)
    (hrel : Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat (FvModexp.AsmDiv.recipWord y.toNat) k s S)
    (hv : Val s zp zl xn xp y k r S)
    (IH : ∀ r' S', AtHead zl xp y (FvModexp.AsmDiv.recipWord y.toNat) (k - 1) r' S' →
      Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat (FvModexp.AsmDiv.recipWord y.toNat) (k - 1) s S' →
      Val s zp zl xn xp y (k - 1) r' S' →
      Reaches ((LibDivWVW.program.link impl).withExit ret) S'
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s')) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  have h_rd_xk := rel_x R b L ret s zp zl xn xp y hpre _ k S hrel ((k - 1) * 8) 8 (by omega) (fun _ => by omega)
  have hpre' := hpre
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, -⟩, hy, hxn, hzl, hzw, hxacc, hx48, hxh,
    hxw, hzx, -⟩ := hpre'
  try simp only [regSP] at hb' ha hw
  obtain ⟨hpc, h0, h7, h9, h6, h8, h10⟩ := hh
  have hrel' := hrel
  obtain ⟨hsp, h5', h14, h15, hx15, hdf, hfs, h_rd_lr, h_rd_fp, h_rd_z, h_rd_x, h_rd_xl, h_rd_y, h_rd_rec, hmf, hlf,
    hinv⟩ := hrel'
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 56 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hacc : S.mem.accessible ((s.regs 4).toNat - 64) (64 + 72) true = true := by rw [hmf.accessible]; exact hw
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw hxw
  have hxacc' : S.mem.accessible xp.toNat (8 * zl.toNat) false = true := by rw [hmf.accessible]; exact hxacc
  have hk1 : BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [hk1] at h9
  have hb := b63 (k - 1) (by omega)
  have hrecl := FvModexp.AsmDivVW.recipWord_lt y.toNat hy y.isLt
  have hrecv : (BitVec.ofNat 64 (FvModexp.AsmDiv.recipWord y.toNat)).toNat = FvModexp.AsmDiv.recipWord y.toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hrecl
  have hr : r < y.toNat := by rw [hv.1]; exact Nat.mod_lt _ (by omega)
  have hrv : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := y.isLt; omega)
  clear hLs hout
  janus64_run [hb, hrecv, hrv] until [entry + 0xff] calls [divww impl hap]
  rename_i _ hpcT hspT h0T h3T h5T h14T hmT hxT hfsT hdfT
  refine tail impl R b L ret hret s zp zl xn xp y hpre r k hk hkz S hrel hv s' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hmT IH
  · rw [hpcT]; try janus64_simp
  · rw [hspT]; try janus64_simp
  · rw [h0T]; try janus64_simp
  · rw [h3T]; try janus64_simp
  · rw [h5T]; try janus64_simp
  · rw [h14T]; try janus64_simp
  · rw [hxT]; try janus64_simp
  · rw [hfsT]; try janus64_simp
    try exact hfs
  · rw [hdfT]; try janus64_simp

/-- the memory at the loop head after the entry (`len x ≠ 1`): saved `RBP`, spills, `rec` -/
@[reducible] def M0 (s : State) (zp zl xp y : BitVec 64) (rec : Nat) : Memory :=
  (((((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 8) 8 zp.toNat).writeLE
        ((s.regs 4).toNat + 40) 8 xp.toNat).writeLE ((s.regs 4).toNat + 64) 8 y.toNat).writeLE
        ((s.regs 4).toNat + 48) 8 zl.toNat).writeLE ((s.regs 4).toNat + 40) 8 xp.toNat).writeLE
        ((s.regs 4).toNat + 8) 8 zp.toNat).writeLE ((s.regs 4).toNat - 16) 8 rec

set_option maxRecDepth 20000 in
/-- `Rel` at the loop head (`k = len z`) after the entry -/
theorem rel_init (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) (hra : s.mem.readLE (s.regs 4).toNat 8 = ret) (hz15 : s.xmm 15 = 0#128)
    (hdf0 : s.df = false) (rec : Nat) (hrec : rec < 2 ^ 64) (S' : State)
    (hsp' : S'.regs 4 = s.regs 4 - 56#64) (h5' : S'.regs 5 = s.regs 4 - 8#64) (h14' : S'.regs 14 = s.regs 14)
    (hx' : S'.xmm 15 = s.xmm 15) (hdf' : S'.df = false) (hfs' : S'.fsBase = s.fsBase)
    (hm' : S'.mem = M0 s zp zl xp y rec) :
    Rel R b L ret zp.toNat xp.toNat zl.toNat y.toNat rec zl.toNat s S' := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, -, hout, -, -, hLs, -⟩, -, -, -, -, -, -, -, -, -, hinv⟩ := hpre
  try simp only [regSP] at hb' ha hw
  have hW : MemFrame s.mem S'.mem (win s 64 72) := by
    rw [hm']; simp only [M0, win]; janus_frame
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat + 72 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [win, Outside, outside_cons, outside_nil, and_true] at this; exact this
  have hwin : ∀ r ∈ win s 64 72, (s.regs 4).toNat - 64 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat + 72 := by
    simp only [win, List.mem_cons, List.mem_nil_iff, or_false]
    rintro r rfl; simp only; omega
  have hrt : ∀ a n, (s.regs 4).toNat - 64 ≤ a → a + n ≤ (s.regs 4).toNat + 72 → Outside a n R.rt :=
    fun a n h1 h2 => Outside.of_sub hout h1 (by omega)
  refine ⟨hsp', h5', h14', hx', hz15, hdf', hfs', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdf0⟩
  · rw [hm']; simp (disch := omega) only [M0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hra
  · rw [hm']; simp (disch := omega) only [M0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 5).isLt
  · rw [hm']; simp (disch := omega) only [M0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt zp.isLt
  · rw [hm']; simp (disch := omega) only [M0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt xp.isLt
  · rw [hm']; simp (disch := omega) only [M0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt zl.isLt
  · rw [hm']; simp (disch := omega) only [M0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt y.isLt
  · rw [hm']; simp (disch := omega) only [M0, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt hrec
  · exact hW.mono fun a n h => by simp only [outside_append] at h; exact h.1.2
  · refine liveFrame_of_frame (rs := win s 64 72) ?_ hLs' hwin
    exact hW.mono fun a n h => by simp only [outside_append] at h; exact h.1
  · rw [hm']
    exact inv_store_out (inv_store_out (inv_store_out (inv_store_out (inv_store_out (inv_store_out (inv_store_out
      (inv_store_out hinv (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega)))
      (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega)))
      (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega))

/-- the loop, by induction on the number `k` of limbs left -/
theorem loop (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl xn xp y : BitVec 64)
    (hpre : Pre R b L zp zl xn xp y s) :
    ∀ k r (S : State), k ≤ zl.toNat → AtHead zl xp y (FvModexp.AsmDiv.recipWord y.toNat) k r S →
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
/-- the entry for `len x ≠ 1`: prologue, the inlined `reciprocalWord(y)`, to the loop head -/
theorem gen (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl zc xn xp xc y : BitVec 64)
    (hs : s.rip = BitVec.ofNat 64 entry) (hx0 : s.regs 0 = zp) (hx3 : s.regs 3 = zl) (hx1 : s.regs 1 = zc)
    (hx7 : s.regs 7 = xn) (hx6 : s.regs 6 = xp) (hx8 : s.regs 8 = zl) (hx9 : s.regs 9 = xc) (hx10 : s.regs 10 = y)
    (hra : s.mem.readLE (s.regs 4).toNat 8 = ret) (hz15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hpre : Pre R b L zp zl xn xp y s) (hne : zl.toNat ≠ 1) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) s
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, -⟩, hy, hxn, -⟩ := hpre'
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  have hne' : (zl = 1#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; apply hne; rw [h]; rfl
  have hy0 : (y.toNat = 0) = False := by simp [hy]
  have hn := FvModexp.AsmDiv.clz_norm64 y.toNat hy y.isLt
  generalize hc : Janus.Arm64.clzNat 64 y.toNat = c at hn
  obtain ⟨hc63, hU1, hU2⟩ := hn
  have hz : 63 - c - 63 = 0 := by omega
  have e1 : (18446744073709551615 - (63 - c)) % 64 = c := by omega
  have hU : y <<< c = BitVec.ofNat 64 (y.toNat * 2 ^ c) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  have hUv : (BitVec.ofNat 64 (y.toNat * 2 ^ c)).toNat = y.toNat * 2 ^ c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hU2
  have hUn : (~~~BitVec.ofNat 64 (y.toNat * 2 ^ c)).toNat = 2 ^ 64 - 1 - y.toNat * 2 ^ c := by
    rw [BitVec.toNat_not, hUv]
  have hrv := FvModexp.AsmDivVW.recip_val _ hU1 hU2
  have hrl : 340282366920938463463374607431768211455 / (y.toNat * 2 ^ c) - 18446744073709551616 <
      18446744073709551616 := FvModexp.AsmDivVW.recip_lt _ hU1
  have hA : ∀ x : BitVec 64, x &&& 18446744073709551615#64 = x := fun x => by
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
  clear hLs hout
  by_cases hc0 : c = 0
  · subst hc0
    have hY1 : 2 ^ 63 ≤ y.toNat := by simpa using hU1
    have hY2 : y.toNat < 2 ^ 64 := y.isLt
    have hrv0 := FvModexp.AsmDivVW.recip_val _ hY1 hY2
    have hrl0 : 340282366920938463463374607431768211455 / y.toNat - 18446744073709551616 <
        18446744073709551616 := FvModexp.AsmDivVW.recip_lt _ hY1
    janus64_run [hne', hy0, hc, hA, BitVec.toNat_not, hrv0] until [entry + 0x127]
    have hrw : FvModexp.AsmDiv.recipWord y.toNat =
        340282366920938463463374607431768211455 / y.toNat - 18446744073709551616 := by
      unfold FvModexp.AsmDiv.recipWord; rw [hc, Nat.pow_zero, Nat.mul_one]
    have hrecl := FvModexp.AsmDivVW.recipWord_lt y.toNat hy y.isLt
    refine loop impl hap R b L ret hret s zp zl xn xp y hpre zl.toNat xn.toNat _ (Nat.le_refl _)
      ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      (rel_init R b L ret s zp zl xn xp y hpre hra hz15 hdf _ hrecl _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ⟨?_, ?_⟩
    all_goals try rw [hrw]
    all_goals first | with_reducible rfl | janus64_simp | skip
    · rw [FvModexp.AsmDivVW.H_top, Nat.mod_eq_of_lt hxn]
    · rw [Nat.sub_self, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero_eq, FvModexp.AsmDivVW.H_top,
        Nat.div_eq_of_lt hxn]
  · have hc0' : (c = 0) = False := by simp [hc0]
    have hcnd : (18446744073709551616 - (18446744073709551553 + (63 - c)) < 64) = True := by simp; omega
    janus64_run [hne', hy0, hc, hz, e1, hc0', hcnd, if_true, hU, hUv, hUn, hrv, hA, BitVec.and_allOnes]
      until [entry + 0x127]
    have hrw : FvModexp.AsmDiv.recipWord y.toNat =
        340282366920938463463374607431768211455 / (y.toNat * 2 ^ c) - 18446744073709551616 := by
      unfold FvModexp.AsmDiv.recipWord; rw [hc]
    have hrecl := FvModexp.AsmDivVW.recipWord_lt y.toNat hy y.isLt
    refine loop impl hap R b L ret hret s zp zl xn xp y hpre zl.toNat xn.toNat _ (Nat.le_refl _)
      ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      (rel_init R b L ret s zp zl xn xp y hpre hra hz15 hdf _ hrecl _ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ⟨?_, ?_⟩
    all_goals try rw [hrw]
    all_goals first | with_reducible rfl | janus64_simp | skip
    · rw [FvModexp.AsmDivVW.H_top, Nat.mod_eq_of_lt hxn]
    · rw [Nat.sub_self, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero_eq, FvModexp.AsmDivVW.H_top,
        Nat.div_eq_of_lt hxn]

set_option maxRecDepth 20000 in
/-- the entry for `len x = 1`: the inlined `bits.Div(xn, x[0], y)`, `z[0] = q`, return `r` -/
theorem one (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibDivWVW.program.link impl) ret) (s : State) (zp zl zc xn xp xc y : BitVec 64)
    (hs : s.rip = BitVec.ofNat 64 entry) (hx0 : s.regs 0 = zp) (hx3 : s.regs 3 = zl) (hx1 : s.regs 1 = zc)
    (hx7 : s.regs 7 = xn) (hx6 : s.regs 6 = xp) (hx8 : s.regs 8 = zl) (hx9 : s.regs 9 = xc) (hx10 : s.regs 10 = y)
    (hra : s.mem.readLE (s.regs 4).toNat 8 = ret) (hz15 : s.xmm 15 = 0#128) (hdf : s.df = false)
    (hpre : Pre R b L zp zl xn xp y s) (hz1 : zl.toNat = 1) :
    Reaches ((LibDivWVW.program.link impl).withExit ret) s
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xn xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, -⟩, hy, hxn, hzl, hzw, hxacc, hx48, hxh,
    hxw, hzx, hinv⟩ := hpre'
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw hxw
  have he : (zl = 1#64) = True := by
    simp only [eq_iff_iff, iff_true]; exact BitVec.eq_of_toNat_eq (by rw [hz1]; rfl)
  have hx0l : s.mem.readLE xp.toNat 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt s.mem xp.toNat 8; simpa using this
  have hq : (xn.toNat * 18446744073709551616 + s.mem.readLE xp.toNat 8) / y.toNat < 18446744073709551616 :=
    FvModexp.AsmDivVW.digit_lt _ _ _ hxn hx0l
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat + 72 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [win, Outside, outside_cons, outside_nil, and_true] at this; exact this
  have hwin : ∀ r ∈ win s 64 72, (s.regs 4).toNat - 64 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat + 72 := by
    simp only [win, List.mem_cons, List.mem_nil_iff, or_false]
    rintro r rfl; simp only; omega
  have hrt : ∀ a n, (s.regs 4).toNat - 64 ≤ a → a + n ≤ (s.regs 4).toNat + 72 → Outside a n R.rt :=
    fun a n h1 h2 => Outside.of_sub hout h1 (by omega)
  clear hLs
  janus64_run [he]
  have hWz : MemFrame s.mem ((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat + 8) 8 zp.toNat).writeLE ((s.regs 4).toNat + 40) 8 xp.toNat).writeLE zp.toNat 8
      ((xn.toNat * 18446744073709551616 + s.mem.readLE xp.toNat 8) / y.toNat))
      (win s 64 72 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) := by
    simp only [win, List.cons_append, List.nil_append]; janus_frame
  have hym : (xn.toNat * 18446744073709551616 + s.mem.readLE xp.toNat 8) % y.toNat < 2 ^ 64 := by
    have := Nat.mod_lt (xn.toNat * 18446744073709551616 + s.mem.readLE xp.toNat 8) (show 0 < y.toNat by omega)
    have := y.isLt; omega
  refine ⟨rfl, by simp only [hdf], ?_, ?_, L, b, LiveExt.refl R L, Nat.le_refl _, ?_, ?_, ?_⟩
  · show (BitVec.ofNat 64 ((xn.toNat * 18446744073709551616 + s.mem.readLE xp.toNat 8) % y.toNat)).toNat =
      (xn.toNat * 2 ^ (64 * zl.toNat) + s.mem.readLE xp.toNat (8 * zl.toNat)) % y.toNat
    rw [hz1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hym]
  · show (((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat + 8) 8 zp.toNat).writeLE ((s.regs 4).toNat + 40) 8 xp.toNat).writeLE zp.toNat 8
      ((xn.toNat * 18446744073709551616 + s.mem.readLE xp.toNat 8) / y.toNat))).readLE zp.toNat (8 * zl.toNat) =
      (xn.toNat * 2 ^ (64 * zl.toNat) + s.mem.readLE xp.toNat (8 * zl.toNat)) / y.toNat
    rw [hz1, Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt hq
  · exact inv_store_held (inv_store_out (inv_store_out (inv_store_out hinv
      (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega)))
      (hzh.sub (Nat.le_refl _) (by omega))
  · exact hWz.mono fun a n h => by simp only [outside_append] at h ⊢; exact ⟨h.1.2, h.2⟩
  · exact liveFrame_of_frame (rs := win s 64 72) hWz hLs' hwin

/-- `divWVW` on the library program -/
theorem ens_lib (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xn xp xl xc y : BitVec 64) :
    Ensures (LibDivWVW.program.link impl) entry [zp, zl, zc, xn, xp, xl, xc, y]
      (fun s => xl = zl ∧ Pre R b L zp zl xn xp y s) (fun s s' => Post R b L zp zl xn xp y s s') := by
  janus64_ensures_old [FvModexp.Amd64.DivWVW.Pre, FvModexp.Amd64.Callees.CallEnvND, FvModexp.NatLive, FvModexp.Amd64.win]
  intro ret hret s hs ⟨hxz, hpre⟩
  janus64_intro hs
  subst hxz
  have hpc : s.rip = BitVec.ofNat 64 entry := by rw [h_rip]; rfl
  refine Janus.Amd64.Tactic.returns_of_reaches ?_
  by_cases h1 : xl.toNat = 1
  · exact one impl R b L ret hret s zp xl zc xn xp xc y hpc h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_ret h_x15 h_df
      hpre h1
  · exact gen impl hap R b L ret hret s zp xl zc xn xp xc y hpc h_a0 h_a1 h_a2 h_a3 h_a4 h_a5 h_a6 h_a7 h_ret h_x15
      h_df hpre h1

/-- **`divWVW` (amd64)**, CONVENTIONS §3 shape (`Pre`/`Post` above; `xl = zl` is Go's `len(z) = len(x)` contract):
`RAX = (xn·B^n + x) mod y`, `z[0:n] = (xn·B^n + x) / y` for `y ≠ 0`, `xn < y`, `z = x` or apart -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xn xp xl xc y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xn, xp, xl, xc, y]
      (fun s => xl = zl ∧ Pre R b L zp zl xn xp y s) (fun s s' => Post R b L zp zl xn xp y s s') := by
  have e : Extracted.program.onlySegments names = LibDivWVW.program := LibDivWVW.eq_only.symm
  rw [e]
  exact ens_lib impl hap R b L zp zl zc xn xp xl xc y

set_option linter.defProp false in
/-- `ens` as a callee summary inside a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4) -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xn xp xl xc y : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R b L zp zl zc xn xp xl xc y) (A64.noExit_restrict64 hap names)
    (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.DivWVW
