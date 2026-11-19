import FvModexp.Proofs.Amd64.SetRetLemmas
import FvModexp.Proofs.Amd64.Nat.Trunc
import FvModexp.Proofs.Amd64.Exp.RdIn0

/-!
# `nat.trunc` (amd64) with an empty-tolerant `x` (`RdIn0`) — twin of `FvModexp.Arm64.Trunc` (Arm64/Nat/TruncE0.lean)

`Pre0` = `Pre` with `x`'s operand fact in `RdIn0` form (no location fact when `len x = 0`, e.g. a `nil` result of
`nat.expNN`) and `len x = 0 → zp = x` (infra's call is `trunc(r, r, n)`).

* `emptyX`: `len x = 0`, `zp = x`: Go's `copy` calls nothing (equal pointers); the result is `z[:0]` (any `cap z`),
  memory changed only in the window.
* **`ens0`** (`Hyp0`): `len x = 0` → `emptyX`; `0 < len x` → `Pre0` is `Pre` (`RdIn0.toRdIn`) → `full`.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (liveFrame_of_memFrame inv_win)
open FvModexp.Amd64.RunIface (Serves)

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Trunc

/-- infra's amd64 `TruncPre` with `x` as `RdIn0` -/
@[reducible] def TruncPre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl n : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ EvenHyp.WrOut R L s stk above zp zc ∧
    EvenHyp.RdIn0 R L s stk above x xl ∧
    xl ≤ 2 ^ 16 ∧ n ≤ 2 ^ 20 ∧ (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    makeCost (EvenHyp.truncNeed xl n) ≤ b ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem)

/-- the precondition with an empty-tolerant `x` -/
def Pre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl n : Nat) (s : State) : Prop :=
  TruncPre0 R b L 4192 64 zp zl zc x xl n s ∧ (NatNorm s.mem x xl ∨ wOf n ≤ xl) ∧
    (zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n)) ∧ (xl = 0 → zp = x)

/-- the premise shape `Hyp2` with `Pre0` -/
def Hyp0 (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z zl zc x xl xc n : BitVec 64),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fn)
      [z, zl, zc, x, xl, xc, n]
      (fun s => TruncPre0 R b L stk above z.toNat zl.toNat zc.toNat x.toNat xl.toNat n.toNat s ∧
        (NatNorm s.mem x.toNat xl.toNat ∨ (n.toNat + 63) / 64 ≤ xl.toNat) ∧
        (z.toNat = x.toNat ∨ 0 < zc.toNat ∨ (0 < xl.toNat ∧ 0 < n.toNat)) ∧ (xl.toNat = 0 → z.toNat = x.toNat))
      (fun s s' => EvenHyp.TruncPost R b L stk above z.toNat zc.toNat x.toNat xl.toNat n.toNat s s')

theorem pre_of_pre0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl n : Nat} {s : State}
    (h : Pre0 R b L zp zl zc x xl n s) (hx : 0 < xl) : Pre R b L zp zl zc x xl n s := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, -⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5.toRdIn hx, h6⟩, h7, h8⟩

theorem pre_env0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x xl n : Nat} {s : State}
    (hpre : Pre0 R b L zp zl zc x xl n s) :
    (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4192 < (s.regs 4).toNat ∧ 4192 ≤ (s.regs 4).toNat ∧
    (s.regs 4).toNat + 64 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 4192) (4192 + 64) true = true ∧ (s.regs 4).toNat % 8 = 0 ∧ TlsG s := by
  obtain ⟨⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩

/-- the post of the empty result `z[:0]` (any `cap z`) -/
theorem postE {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x n : Nat} {s : State}
    (hpre : Pre0 R b L zp zl zc x 0 n s)
    {M' : Janus.Arm64.Memory} (hF : MemFrame s.mem M' (win s 4192 64)) (s' : State) (hm : s'.mem = M')
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 3 = BitVec.ofNat 64 0) (h2 : s'.regs 1 = BitVec.ofNat 64 zc)
    (hfs : s'.fsBase = s.fsBase) :
    PostI R b L zp zc x 0 n s s' := by
  subst hm
  obtain ⟨⟨⟨_, ⟨hb', _, _⟩, _, _, hout, _, _, hLs, _⟩, _, _, ⟨hz40, hzl, -⟩, _, _, _, _, _, hinv⟩, _, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hb'
  have hk : EvenHyp.truncNeed 0 n = 0 := by unfold EvenHyp.truncNeed; omega
  refine ⟨hfs, zp, 0, zc, h0, h1, h2, L, b, ⟨by rw [natVal_zero]; simp, Or.inl rfl, Nat.zero_le _, hz40,
    fun hc => ?_, fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by omega)⟩, fun h => absurd h (by omega),
    ⟨LiveExt.refl R L, Nat.sub_le _ _, inv_win hF hout hb' hinv⟩, ?_, ?_⟩
  · obtain ⟨q1, q2, q3, q4⟩ := hzl hc
    exact ⟨q1, q2, by rw [hF.accessible]; exact q3, q4⟩
  · exact hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2
  · exact liveFrame_of_frame (rs := win s 4192 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp only; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`len x = 0`, `z = x`**: `return z[:0]` without a call (as `zeroPath`, any `cap z`) -/
theorem emptyX (impl : List Amd64.Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xc n : Nat) (s : State)
    (he : Entry s zp zl zc x 0 xc n) (hzx : zp = x) (hpre : Pre0 R b L zp zl zc x 0 n s) :
    ReachesRet (LibTrunc.program.link impl) (retAddrOf s) s fun s' => RegsOK s s' ∧ PostI R b L zp zc x 0 n s s' := by
  obtain ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := he
  obtain ⟨hg1, hg2, hg3, hb', ha, hwa, hal, htg⟩ := pre_env0 hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, -, ⟨hz40, -, -⟩, -, -, hn20, -, -, -⟩, -, -⟩ := hpre'
  have hsh := shr_w n hn20
  have hsh' := shr_w' n hn20
  have hzc' : zc % 18446744073709551616 = zc := Nat.mod_eq_of_lt (by omega)
  subst hzx
  by_cases hn0 : n = 0
  · subst hn0
    have hw0 : wOf 0 = 0 := rfl
    rw [hw0] at hsh hsh'
    have hr0' : BitVec.ofNat 64 0 &&& 63#64 = 0#64 := rfl
    janus64_run [hsh, hsh', hzc', hr0', BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, postE hpre ?hF _ rfl ?_ ?_ ?_ ?_⟩
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip
  · have hwp : 0 < wOf n := by unfold wOf; omega
    have hwm : wOf n % 18446744073709551616 = wOf n := Nat.mod_eq_of_lt (by unfold wOf; omega)
    janus64_run [hsh, hsh', hwm, hzc', BitVec.msb_eq_decide]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, postE hpre ?hF _ rfl ?_ ?_ ?_ ?_⟩
    case hF => simp only [win]; janus_frame
    all_goals try janus64_simp
    all_goals first | exact hx15 | exact hdf | skip

set_option maxRecDepth 20000 in
theorem full0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) :
    Summary (LibTrunc.program.link impl) (segAddr Extracted.program fn)
      (fun s => EntryP s zp zl zc x xl xc n ∧ Pre0 R b L zp zl zc x xl n s)
      (fun s s' => RegsOK s s' ∧ PostI R b L zp zc x xl n s s') := by
  intro s hpc ⟨hE, hpre⟩
  rcases Nat.eq_zero_or_pos xl with hx0 | hx0
  · subst hx0
    obtain ⟨hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ := hE
    exact emptyX impl R b L zp zl zc x xc n s ⟨hpc, hra, hx15, hdf, h0, h3, h1, h7, h6, h8, h9⟩ (hpre.2.2.2 rfl) hpre
  · exact full impl hap R hmk hmv b L zp zl zc x xl xc n s hpc ⟨hE, pre_of_pre0 hpre hx0⟩

/-- **`nat.trunc`** (amd64) with an empty-tolerant `x`: `Hyp0` (= `Hyp2` with `x` as `RdIn0` and `len x = 0 → z = x`);
`Hyp2` (`ens`) stays as it was -/
theorem ens0 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) :
    Hyp0 impl R names 4192 64 := by
  intro b L z zl zc x xl xc n
  rw [show names = LibTrunc.names from rfl, ← LibTrunc.eq_only]
  janus64_ensures_old [FvModexp.Amd64.Trunc.TruncPre0, FvModexp.Amd64.natNorm_setRet, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.CallEnv, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn0, FvModexp.Amd64.win, FvModexp.Amd64.TlsOK, FvModexp.NatLive, FvModexp.Amd64.EvenHyp.RdIn]
  intro ret hret s hs hpre
  janus64_intro hs
  refine Summary.returns (full0 impl hap R hmk hmv b L z.toNat zl.toNat zc.toNat x.toNat xl.toNat xc.toNat
      n.toNat) hret (by rw [h_rip]; rfl)
    (by rw [retAddrOf, h_ret]) ⟨⟨by rw [h_ret]; exact hret.user, h_x15, h_df, by simp [h_a0], by simp [h_a1],
      by simp [h_a2], by simp [h_a3], by simp [h_a4], by simp [h_a5], by simp [h_a6]⟩, hpre⟩
    fun s' ⟨⟨a, b, c, d, e⟩, hfs, hq⟩ => ⟨⟨a, b, c, d⟩, hfs, e.trans h_df.symm, hq⟩

end FvModexp.Amd64.Trunc
