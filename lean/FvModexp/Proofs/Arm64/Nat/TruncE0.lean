import FvModexp.Proofs.Arm64.Nat.Trunc
import FvModexp.Proofs.Arm64.Exp.RdIn0

/-!
# `nat.trunc` (arm64) with an empty-tolerant `x` (`RdIn0`, coordinator decision on "[infra s30] FINDING")

`Pre0` = `Pre` with `x`'s operand fact in `RdIn0` form (no location fact when `len x = 0`, e.g. a `nil` result of
`nat.expNN`) and one more fact: an empty `x` is `z` itself (`len x = 0 → zp = x`; infra's call is `trunc(r, r, n)`).

* `emptyX`: `len x = 0`, `zp = x`: both pointers agree, so Go's `copy` calls nothing; the result is `z[:0]` (any
  `cap z`), memory changed only in the window.
* **`ens0`** (`Hyp0`): `len x = 0` → `emptyX`; `0 < len x` → `Pre0` is `Pre` (`RdIn0.toRdIn`) → `ens`.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (liveFrame_of_memFrame)
open FvModexp.Arm64.RunIface (Serves)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Trunc

/-- infra's `TruncPre` (window `4208 / 64`) with `x` as `RdIn0` -/
@[reducible] def TruncPre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zl zc x xl n : Nat) (s : State) :
    Prop :=
  CallEnv R L s stk above ∧ Serves R ∧ zl ≤ zc ∧ ExpHyp.WrOut R L s stk above zp zc ∧
    ExpHyp.RdIn0 R L s stk above x xl ∧
    xl ≤ 2 ^ 16 ∧ n ≤ 2 ^ 20 ∧ (zp = x ∨ (0 < zc → 0 < xl → Apart zp (8 * zc) x (8 * xl))) ∧
    makeCost (EvenHyp.truncNeed xl n) ≤ b ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem)

/-- the precondition with an empty-tolerant `x` -/
def Pre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl n : Nat) (s : State) : Prop :=
  TruncPre0 R b L 4208 64 zp zl zc x xl n s ∧ (NatNorm s.mem x xl ∨ wOf n ≤ xl) ∧
    (zp = x ∨ 0 < zc ∨ (0 < xl ∧ 0 < n)) ∧ (xl = 0 → zp = x)

/-- the premise shape `Hyp2` with `Pre0` -/
def Hyp0 (impl : List Segment) (R : RtInv) (ns : List String) (stk above : Nat) : Prop :=
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

/-- the post of the empty result `z[:0]` (any `cap z`) -/
theorem postE {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zl zc x n : Nat} {s : State}
    (hpre : Pre0 R b L zp zl zc x 0 n s)
    {M' : Memory} (hF : MemFrame s.mem M' (winA s 4208 64)) (s' : State) (hm : s'.mem = M')
    (h0 : s'.regs 0 = BitVec.ofNat 64 zp) (h1 : s'.regs 1 = BitVec.ofNat 64 0) (h2 : s'.regs 2 = BitVec.ofNat 64 zc) :
    Post R b L zp zc x 0 n s s' := by
  subst hm
  obtain ⟨⟨⟨_, ⟨_, hb', _, _⟩, _, hout, _, _, hLs, _⟩, _, _, ⟨hz40, hzl, -⟩, _, _, _, _, _, hinv⟩, _, _⟩ := hpre
  have hk : EvenHyp.truncNeed 0 n = 0 := by unfold EvenHyp.truncNeed; omega
  refine ⟨zp, 0, zc, h0, h1, h2, L, b, ⟨by rw [natVal_zero]; simp, Or.inl rfl, Nat.zero_le _, hz40,
    fun hc => ?_, fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by omega)⟩, fun h => absurd h (by omega),
    ⟨LiveExt.refl R L, Nat.sub_le _ _, inv_frame_winA hF hout hb' (by omega) hinv⟩, ?_, ?_⟩
  · obtain ⟨q1, q2, q3, q4⟩ := hzl hc
    exact ⟨q1, q2, by rw [hF.accessible]; exact q3, q4⟩
  · exact hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2
  · exact liveFrame_of_frame (rs := winA s 4208 64) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`len x = 0`, `z = x`**: `return z[:0]` without a call -/
theorem emptyX (impl : List Segment) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xc n : Nat) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 (segAddr Extracted.program fn))
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (h0 : s.regs 0 = BitVec.ofNat 64 zp)
    (h1 : s.regs 1 = BitVec.ofNat 64 zl) (h2 : s.regs 2 = BitVec.ofNat 64 zc) (h3 : s.regs 3 = BitVec.ofNat 64 x)
    (h4 : s.regs 4 = BitVec.ofNat 64 0) (h5 : s.regs 5 = BitVec.ofNat 64 xc) (h6 : s.regs 6 = BitVec.ofNat 64 n)
    (hzx : zp = x) (hpre : Pre0 R b L zp zl zc x 0 n s) :
    ReachesRet (LibTrunc.program.link impl) (s.regs 30) s fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x 0 n s s' := by
  have hpre' := hpre
  obtain ⟨⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hwa⟩, -, hout, hga, -, -, -⟩, -, -, ⟨hz40, -, -⟩,
    -, hx16, hn20, -, -, -⟩, -, -⟩ := hpre'
  have hsh := shr_w n hn20
  have hsh2 : (BitVec.ofNat 64 n + 63#64).rotateRight 6 &&& 18446744073709551615#64 &&& 288230376151711743#64 =
      BitVec.ofNat 64 (wOf n) := by rw [TruncMath.rot6, hsh]
  have hzc' : zc % 18446744073709551616 = zc := Nat.mod_eq_of_lt (by omega)
  subst hzx
  by_cases hn0 : n = 0
  · subst hn0
    janus_run [hsh, hsh2, hzc']
    refine postE hpre ?hF _ rfl ?_ ?_ ?_
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp
  · have hwp : 0 < wOf n := by unfold wOf; omega
    have hwm : wOf n % 18446744073709551616 = wOf n := Nat.mod_eq_of_lt (by unfold wOf; omega)
    janus_run [hsh, hsh2, hwm, hzc']
    refine postE hpre ?hF _ rfl ?_ ?_ ?_
    case hF => simp only [winA]; janus_frame
    all_goals janus_simp

theorem full0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc x xl xc n : Nat) :
    Summary (LibTrunc.program.link impl) (segAddr Extracted.program fn)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = BitVec.ofNat 64 zp ∧
        s.regs 1 = BitVec.ofNat 64 zl ∧ s.regs 2 = BitVec.ofNat 64 zc ∧ s.regs 3 = BitVec.ofNat 64 x ∧
        s.regs 4 = BitVec.ofNat 64 xl ∧ s.regs 5 = BitVec.ofNat 64 xc ∧ s.regs 6 = BitVec.ofNat 64 n ∧
        Pre0 R b L zp zl zc x xl n s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl n s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, hpre⟩
  rcases Nat.eq_zero_or_pos xl with hx0 | hx0
  · subst hx0
    exact emptyX impl R b L zp zl zc x xc n s hpc hl4 hl48 h0 h1 h2 h3 h4 h5 h6 (hpre.2.2.2 rfl) hpre
  · exact full impl hap R hmk hmv b L zp zl zc x xl xc n s hpc
      ⟨hl4, hl48, h0, h1, h2, h3, h4, h5, h6, pre_of_pre0 hpre hx0⟩

/-- **`nat.trunc`** (arm64) with an empty-tolerant `x`: `Hyp0` (= `Hyp2` with `x` as `RdIn0` and `len x = 0 → z = x`);
`Hyp2` (`ens`) stays as it was -/
theorem ens0 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) : Hyp0 impl R names 4208 64 := by
  intro b L z zl zc x xl xc n
  rw [show names = LibTrunc.names from rfl, ← LibTrunc.eq_only]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  have hr4 := hret.aligned
  refine Summary.returns (full0 impl hap R hmk hmv b L z.toNat zl.toNat zc.toNat x.toNat xl.toNat xc.toNat n.toNat)
    hret h_pc h_lr ⟨?_, ?_, by simp [h_x0], by simp [h_x1], by simp [h_x2], by simp [h_x3], by simp [h_x4],
      by simp [h_x5], by simp [h_x6], hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
  · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

end FvModexp.Arm64.Trunc
