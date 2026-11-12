import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4K0
import FvModexp.Proofs.Arm64.Exp.W4LshR

/-!
# window-4 prologue (arm64): run pieces between the `x` join and the first `stk.nat(2n)`

* `toK`: `xJ` (fn+0x2e8, `CBZ R8` = `len(y) == 0`, refuted; `CBZ R11` = `len(m) == 0`, refuted; `m[0]` load; Newton start
  `R13 = 2 - m0`, `R9 = m0 - 1`, `R1 = 1`) → `kHead` (nat.go:1389-1394, 1273-1276);
* `toSn1`: `kExit` (fn+0x374: spills of `x`, `[224] = R13`, `[128] = 2n`) → entry of `stk.nat(2n)` (nat.go:1397).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

/-- `CBZ R8` after the `x` normalisation -/
abbrev xJ : Nat := 1799256

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toK (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (ylen mp n m0 : Nat) (M : Memory)
    (hyl : 0 < ylen) (hyl' : ylen < 2 ^ 64) (hn : 0 < n) (hn' : n < 2 ^ 64) (hm48 : mp + 8 ≤ 2 ^ 48)
    (hma : M.accessible mp 8 false = true) (hm0 : M.readLE mp 8 = m0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 xJ) (h8 : S.regs 8 = BitVec.ofNat 64 ylen)
    (h10 : S.regs 10 = BitVec.ofNat 64 mp) (h11 : S.regs 11 = BitVec.ofNat 64 n) (hmem : S.mem = M)
    (KH : ∀ (S' : State), S'.pc = BitVec.ofNat 64 kHead → S'.sp = S.sp → S'.mem = M →
      S'.regs 1 = BitVec.ofNat 64 (2 ^ 0) →
      S'.regs 9 = BitVec.ofNat 64 ((m0 + 18446744073709551616 - 1) % 18446744073709551616) →
      S'.regs 13 = BitVec.ofNat 64 ((2 + 18446744073709551616 - m0 % 18446744073709551616) % 18446744073709551616) →
      S'.regs 3 = S.regs 3 → S'.regs 4 = S.regs 4 → S'.regs 5 = S.regs 5 → S'.regs 6 = S.regs 6 →
      S'.regs 11 = S.regs 11 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  generalize e3 : S.regs 3 = x3 at KH
  generalize e4 : S.regs 4 = x4 at KH
  generalize e5 : S.regs 5 = x5 at KH
  generalize e6 : S.regs 6 = x6 at KH
  generalize e18 : S.regs 18 = x18 at KH
  generalize e28 : S.regs 28 = x28 at KH
  generalize e29 : S.regs 29 = x29 at KH
  generalize esp : S.sp = xsp at KH
  have hy0 : BitVec.ofNat 64 ylen ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hn0 : BitVec.ofNat 64 n ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hm0' : m0 < 2 ^ 64 := by have := M.readLE_lt mp 8; rw [hm0] at this; omega
  janus_run [hy0, hn0, hm0] until [kHead]
  refine KH _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip
  all_goals (janus_simp; apply BitVec.eq_of_toNat_eq
             simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toSn1 (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (sp st xp xc n t : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 4288 ≤ sp) (hsp2 : sp + 1040 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4288) (4288 + 1040) true = true)
    (hst : st < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxc : xc < 2 ^ 64) (hn : n ≤ 128) (ht : t < 2 ^ 64)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 kExit) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 n)
    (h6 : S.regs 6 = BitVec.ofNat 64 xc) (h11 : S.regs 11 = BitVec.ofNat 64 n) (h13 : S.regs 13 = BitVec.ofNat 64 t)
    (hmem : S.mem = M)
    (KS : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 snE → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 1 = BitVec.ofNat 64 (2 * n) → S'.regs 30 = BitVec.ofNat 64 sn1Ret →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 128, sp + 136), (sp + 224, sp + 232), (sp + 320, sp + 336), (sp + 904, sp + 912)] →
      M'.regions = M.regions →
      M'.readLE (sp + 904) 8 = xp → M'.readLE (sp + 328) 8 = n → M'.readLE (sp + 320) 8 = xc →
      M'.readLE (sp + 224) 8 = t → M'.readLE (sp + 128) 8 = 2 * n →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  generalize e18 : S.regs 18 = x18 at KS
  generalize e28 : S.regs 28 = x28 at KS
  generalize e29 : S.regs 29 = x29 at KS
  have e2n : BitVec.ofNat 64 n + BitVec.ofNat 64 n = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  janus_run [e2n] until [snE]
  refine KS _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?q1 ?q2 ?q3 ?q4 ?q5
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 128, sp + 136)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 224, sp + 232)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 320, sp + 336)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 904, sp + 912)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow]
  all_goals omega

end FvModexp.Arm64.W4Pro
