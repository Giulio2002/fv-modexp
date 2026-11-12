import FvModexp.Proofs.Arm64.Exp.NDefs
import FvModexp.Proofs.Common.BitLemmas

/-!
# `nat.expNN` (arm64): after `z = z.make(len m)` — the dispatch (nat.go:698-718)

From one of the three points after the make (`P` = fn+0x330 reuse / fn+0x35c after `makeslice(1,1)` / fn+0x3b4 after
`makeslice(n, n+4)`; each sets the flags by `CMP $1, R8` itself) through `J4` = fn+0x3f0: `slow` false (byte 0);
`len y == 1 && nlz(y[0]) ≥ 59` → `expNNSlow` entry; `m[0]` odd → `expNNOdd` entry; else the `isPow2` loop head
(fn+0x57c, `R13 = 0`). Continuation form; the callee args are `X0..X2 = (zp, n, zc)`, `X3 = st`, `x`, `y`, `m`
(`X10..X12`) unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

/-- entries: `expNNSlow`, `expNNOdd`, `expNNPowerOfTwo`; the `isPow2` loop head -/
abbrev slowA : Nat := 1788352
abbrev oddA : Nat := 1798352
abbrev p2A : Nat := 1792288
abbrev powH : Nat := 1787948

/-- the spill slots `SP' + 232, 296 .. 368` (`st`, `x`, `y`, `m`, `slow`) as the make's `makeslice` paths reload them -/
@[reducible] def Spills (M : Memory) (sp st xp xl xc yp yl yc mp n mc : Nat) : Prop :=
  M.readLE (sp + 1056 + 232) 8 = st ∧ M.readLE (sp + 1056 + 296) 8 = xp ∧ M.readLE (sp + 1056 + 304) 8 = xl ∧
  M.readLE (sp + 1056 + 312) 8 = xc ∧ M.readLE (sp + 1056 + 320) 8 = yp ∧ M.readLE (sp + 1056 + 328) 8 = yl ∧
  M.readLE (sp + 1056 + 336) 8 = yc ∧ M.readLE (sp + 1056 + 344) 8 = mp ∧ M.readLE (sp + 1056 + 352) 8 = n ∧
  M.readLE (sp + 1056 + 360) 8 = mc ∧ M.readLE (sp + 1056 + 368) 1 = 0

/-- the callee arguments `z = (zp, n, zc)`, `st`, `x`, `y`, `m` -/
@[reducible] def DArgs (S : State) (zp zc st xp xl xc yp yl yc mp n mc : Nat) : Prop :=
  S.regs 0 = BitVec.ofNat 64 zp ∧ S.regs 1 = BitVec.ofNat 64 n ∧ S.regs 2 = BitVec.ofNat 64 zc ∧
  S.regs 3 = BitVec.ofNat 64 st ∧
  S.regs 4 = BitVec.ofNat 64 xp ∧ S.regs 5 = BitVec.ofNat 64 xl ∧ S.regs 6 = BitVec.ofNat 64 xc ∧
  S.regs 7 = BitVec.ofNat 64 yp ∧ S.regs 8 = BitVec.ofNat 64 yl ∧ S.regs 9 = BitVec.ofNat 64 yc ∧
  S.regs 10 = BitVec.ofNat 64 mp ∧ S.regs 11 = BitVec.ofNat 64 n ∧ S.regs 12 = BitVec.ofNat 64 mc

/-- the state at a dispatch start point: reuse (fn+0x330: registers) or after a `makeslice` (fn+0x35c with `n = zc = 1`,
fn+0x3b4 with `zc` in `SP' + 128`: spills) -/
@[reducible] def DStart (S : State) (sp zp zc st xp xl xc yp yl yc mp n mc : Nat) : Prop :=
  S.regs 0 = BitVec.ofNat 64 zp ∧
  ((S.pc = BitVec.ofNat 64 1787360 ∧ S.regs 2 = BitVec.ofNat 64 zc ∧ S.regs 3 = BitVec.ofNat 64 st ∧
     S.regs 4 = BitVec.ofNat 64 xp ∧ S.regs 5 = BitVec.ofNat 64 xl ∧ S.regs 6 = BitVec.ofNat 64 xc ∧
     S.regs 7 = BitVec.ofNat 64 yp ∧ S.regs 8 = BitVec.ofNat 64 yl ∧ S.regs 9 = BitVec.ofNat 64 yc ∧
     S.regs 10 = BitVec.ofNat 64 mp ∧ S.regs 11 = BitVec.ofNat 64 n ∧ S.regs 12 = BitVec.ofNat 64 mc ∧
     S.regs 13 = 0#64) ∨
   (S.pc = BitVec.ofNat 64 1787404 ∧ zc = 1 ∧ n = 1 ∧ Spills S.mem sp st xp xl xc yp yl yc mp n mc) ∨
   (S.pc = BitVec.ofNat 64 1787492 ∧ S.mem.readLE (sp + 1056 + 128) 8 = zc ∧ Spills S.mem sp st xp xl xc yp yl yc mp n mc))

theorem clzNat_le' : ∀ n x, clzNat n x ≤ n
  | 0, _ => Nat.le_refl _
  | n + 1, x => by
    simp only [clzNat]; split
    · omega
    · have := clzNat_le' n x; omega

theorem lsb0 (v : Nat) : ((BitVec.ofNat 64 v).getLsbD 0 == true) = true ↔ v % 2 = 1 := by
  simp only [BitVec.getLsbD_ofNat, Nat.testBit_zero]
  by_cases h : v % 2 = 1 <;> simp [h]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem disp (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0) (Q : Outcome → Prop)
    (sp zp zc st xp xl xc yp yl yc mp n mc : Nat) (M : Memory)
    (hzp : zp < 2 ^ 64) (hzc : zc < 2 ^ 64) (hst : st < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxl : xl < 2 ^ 64)
    (hxc : xc < 2 ^ 64) (hyp : yp < 2 ^ 64) (hyl : yl < 2 ^ 64) (hyc : yc < 2 ^ 64) (hmp : mp < 2 ^ 64)
    (hn : n < 2 ^ 64) (hmc : mc < 2 ^ 64)
    (hya : M.accessible yp 8 false = true) (hma : M.accessible mp 8 false = true)
    (hal : sp % 16 = 0) (hsp1 : 8 ≤ sp) (hsp2 : sp + 1432 ≤ 2 ^ 48) (hacc : M.accessible (sp + 1048) 384 true = true)
    (S : State) (hsp : S.sp = BitVec.ofNat 64 (sp + 1056)) (hR : DStart S sp zp zc st xp xl xc yp yl yc mp n mc)
    (hmem : S.mem = M)
    (KS : yl = 1 → 59 ≤ clzNat 64 (M.readLE yp 8) → ∀ S' : State, S'.pc = BitVec.ofNat 64 slowA →
      S'.sp = S.sp → DArgs S' zp zc st xp xl xc yp yl yc mp n mc → S'.regs 18 = S.regs 18 →
      S'.regs 28 = S.regs 28 → S'.regs 30 = BitVec.ofNat 64 1787596 → S'.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q)
    (KO : ¬(yl = 1 ∧ 59 ≤ clzNat 64 (M.readLE yp 8)) → M.readLE mp 8 % 2 = 1 → ∀ S' : State,
      S'.pc = BitVec.ofNat 64 oddA → S'.sp = S.sp → DArgs S' zp zc st xp xl xc yp yl yc mp n mc →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 30 = BitVec.ofNat 64 1787680 → S'.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q)
    (KP : ¬(yl = 1 ∧ 59 ≤ clzNat 64 (M.readLE yp 8)) → M.readLE mp 8 % 2 = 0 → ∀ S' : State,
      S'.pc = BitVec.ofNat 64 powH → S'.sp = S.sp → DArgs S' zp zc st xp xl xc yp yl yc mp n mc →
      S'.regs 13 = 0#64 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have hy8 : M.readLE yp 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  have hm8 : M.readLE mp 8 < 2 ^ 64 := Memory.readLE_lt _ _ _
  obtain ⟨h0, hR⟩ := hR
  rw [hmem] at hR
  rcases hR with ⟨hpc, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ |
    ⟨hpc, rfl, rfl, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ |
    ⟨hpc, hzc', s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
  all_goals have hcz := clzNat_le' 64 (M.readLE yp 8)
  have hcz := clzNat_le' 64 (M.readLE yp 8)
  · janus_run [] until [slowA, oddA, powH]
    all_goals (try simp only [lsb0] at *)
    all_goals first
      | (refine KS (by omega) (by omega) _ rfl ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_)
      | (refine KO (by omega) (by omega) _ rfl ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_)
      | (refine KP (by omega) (by omega) _ rfl ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_)
    all_goals first | (janus_simp; done) | (simp only [setReg, *]; done) | trace_state
  · janus_run [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11] until [slowA, oddA, powH]
    all_goals (try simp only [lsb0] at *)
    all_goals first
      | (refine KS (by omega) (by omega) _ rfl ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_)
      | (refine KO (by omega) (by omega) _ rfl ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_)
      | (refine KP (by omega) (by omega) _ rfl ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_)
    all_goals first | (janus_simp; done) | (simp only [setReg, *]; done) | trace_state
  · janus_run [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, hzc'] until [slowA, oddA, powH]
    all_goals (try simp only [lsb0] at *)
    all_goals first
      | (refine KS (by omega) (by omega) _ rfl ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_)
      | (refine KO (by omega) (by omega) _ rfl ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_)
      | (refine KP (by omega) (by omega) _ rfl ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_)
    all_goals first | (janus_simp; done) | (simp only [setReg, *]; done) | trace_state

end FvModexp.Arm64.ExpN
