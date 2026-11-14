import FvModexp.Proofs.Arm64.Exp.W4XnDefs
import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.W4XjR

/-!
# window-4 prologue (arm64): run pieces of the `x` normalisation (nat.go:1377-1386, fn+0x1a4 .. `xJ` = fn+0x2e8)

* `xnSplit`: `xnE` (fn+0x1a4, `CMP R5, R11; BGE`) → `j238` (`len x ≤ n`) or the entry of `stk.nat(len x - n + 1)` (path A);
* `xnA1`: return of that `stk.nat` (`aSn1Ret`) → entry of `stk.nat(n)` (spills of `q`);
* `xnA2`: return of `stk.nat(n)` (`aSn2Ret`) → entry of `nat.div` (`q.div(stk, z2, x, m)`, return `aDivRet`);
* `xnA3`: `aDivRet` → `j238` (`x := r`);
* `xnJ`: `j238` (`CMP R5, R11; BLE`) → `xJ` (`n ≤ len x`, path C) or the entry of `rr := stk.nat(n)` (path B);
* `xnB`: return of that `stk.nat` (`bSnRet`) → `xJ`: `copy(rr, x)` (memmove), `clear(rr[len x:])` (memclr).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

abbrev aSn1Ret : Nat := 1798956
abbrev aSn2Ret : Nat := 1798980
abbrev aDivRet : Nat := 1799036
abbrev j238 : Nat := 1799080
abbrev bSnRet : Nat := 1799108

theorem toInt_ofNat_lt {v : Nat} (h : v < 2 ^ 63) : (BitVec.ofNat 64 v).toInt = (v : Int) := by
  have e : (BitVec.ofNat 64 v).toNat = v := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toInt_eq_toNat_cond, e]; split <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnSplit (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (st xl n : Nat) (hst : st < 2 ^ 64) (hxl : xl < 2 ^ 40) (hn : n ≤ 128)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 xnE) (h3 : S.regs 3 = BitVec.ofNat 64 st)
    (h5 : S.regs 5 = BitVec.ofNat 64 xl) (h11 : S.regs 11 = BitVec.ofNat 64 n)
    (KJ : xl ≤ n → ∀ S' : State, S'.pc = BitVec.ofNat 64 j238 → S'.sp = S.sp → S'.mem = S.mem →
      (∀ i, S'.regs i = S.regs i) → Reaches ((LibW.program.link impl).withExit ret) S' Q)
    (KA : n < xl → ∀ S' : State, S'.pc = BitVec.ofNat 64 snE → S'.sp = S.sp → S'.mem = S.mem →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 1 = BitVec.ofNat 64 (xl - n + 1) →
      S'.regs 30 = BitVec.ofNat 64 aSn1Ret →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  have tx := toInt_ofNat_lt (v := xl) (by omega)
  have tn := toInt_ofNat_lt (v := n) (by omega)
  by_cases hc : xl ≤ n
  · have hb : ¬ (BitVec.ofNat 64 n).toInt < (BitVec.ofNat 64 xl).toInt := by rw [tx, tn]; omega
    janus_run [hb, tx, tn] until [j238]
    refine KJ hc _ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip
    intro i; janus_simp
  · have hb : (BitVec.ofNat 64 n).toInt < (BitVec.ofNat 64 xl).toInt := by rw [tx, tn]; omega
    generalize e18 : S.regs 18 = x18 at KA
    generalize e28 : S.regs 28 = x28 at KA
    generalize e29 : S.regs 29 = x29 at KA
    have es : BitVec.ofNat 64 xl - BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (xl - n + 1) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus_run [hb, tx, tn, es] until [snE]
    refine KA (by omega) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnA1 (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (sp st n qp ql qc : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 4288 ≤ sp) (hsp2 : sp + 1040 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4288) (4288 + 1040) true = true)
    (hqp : qp < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qc < 2 ^ 64)
    (r960 : M.readLE (sp + 960) 8 = st) (r1024 : M.readLE (sp + 1024) 8 = n)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 aSn1Ret) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 qp) (h1 : S.regs 1 = BitVec.ofNat 64 ql) (h2 : S.regs 2 = BitVec.ofNat 64 qc)
    (hmem : S.mem = M)
    (KS : ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 snE → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 1 = BitVec.ofNat 64 n → S'.regs 30 = BitVec.ofNat 64 aSn2Ret →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 320, sp + 336), (sp + 904, sp + 912)] → M'.regions = M.regions →
      M'.readLE (sp + 904) 8 = qp → M'.readLE (sp + 328) 8 = ql → M'.readLE (sp + 320) 8 = qc →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  generalize e18 : S.regs 18 = x18 at KS
  generalize e28 : S.regs 28 = x28 at KS
  generalize e29 : S.regs 29 = x29 at KS
  janus_run [r960, r1024] until [snE]
  refine KS _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?q1 ?q2 ?q3
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 320, sp + 336)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 904, sp + 912)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow]
  all_goals omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnA2 (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (sp st qp ql qc xp xl xc mp n mc : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 4288 ≤ sp) (hsp2 : sp + 1040 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4288) (4288 + 1040) true = true)
    (r960 : M.readLE (sp + 960) 8 = st) (r904 : M.readLE (sp + 904) 8 = qp) (r328 : M.readLE (sp + 328) 8 = ql)
    (r320 : M.readLE (sp + 320) 8 = qc) (r968 : M.readLE (sp + 968) 8 = xp) (r976 : M.readLE (sp + 976) 8 = xl)
    (r984 : M.readLE (sp + 984) 8 = xc)
    (r1016 : M.readLE (sp + 1016) 8 = mp) (r1024 : M.readLE (sp + 1024) 8 = n) (r1032 : M.readLE (sp + 1032) 8 = mc)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 aSn2Ret) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KD : ∀ (S' : State), S'.pc = BitVec.ofNat 64 divE → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 qp → S'.regs 1 = BitVec.ofNat 64 ql → S'.regs 2 = BitVec.ofNat 64 qc →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = S.regs 0 → S'.regs 5 = S.regs 1 →
      S'.regs 6 = S.regs 2 → S'.regs 7 = BitVec.ofNat 64 xp → S'.regs 8 = BitVec.ofNat 64 xl →
      S'.regs 9 = BitVec.ofNat 64 xc → S'.regs 10 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 n →
      S'.regs 12 = BitVec.ofNat 64 mc → S'.regs 30 = BitVec.ofNat 64 aDivRet →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  generalize e0 : S.regs 0 = y0 at KD
  generalize e1 : S.regs 1 = y1 at KD
  generalize e2 : S.regs 2 = y2 at KD
  generalize e18 : S.regs 18 = x18 at KD
  generalize e28 : S.regs 28 = x28 at KD
  generalize e29 : S.regs 29 = x29 at KD
  janus_run [r960, r904, r328, r320, r968, r976, r984, r1016, r1024, r1032] until [divE]
  refine KD _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnA3 (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (sp st yl mp n : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 4288 ≤ sp) (hsp2 : sp + 1040 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4288) (4288 + 1040) true = true)
    (r960 : M.readLE (sp + 960) 8 = st) (r1000 : M.readLE (sp + 1000) 8 = yl)
    (r1016 : M.readLE (sp + 1016) 8 = mp) (r1024 : M.readLE (sp + 1024) 8 = n)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 aDivRet) (hsp : S.sp = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (KJ : ∀ (S' : State), S'.pc = BitVec.ofNat 64 j238 → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 3 = BitVec.ofNat 64 st → S'.regs 4 = S.regs 3 → S'.regs 5 = S.regs 4 → S'.regs 6 = S.regs 5 →
      S'.regs 8 = BitVec.ofNat 64 yl → S'.regs 10 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 n →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  generalize e3 : S.regs 3 = y3 at KJ
  generalize e4 : S.regs 4 = y4 at KJ
  generalize e5 : S.regs 5 = y5 at KJ
  generalize e18 : S.regs 18 = x18 at KJ
  generalize e28 : S.regs 28 = x28 at KJ
  generalize e29 : S.regs 29 = x29 at KJ
  janus_run [r960, r1000, r1016, r1024] until [j238]
  refine KJ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | (janus_simp; done) | skip

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem xnJ (impl : List Segment) (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret)
    (Q : Outcome → Prop) (sp st xp xl n : Nat) (M : Memory)
    (hal : sp % 16 = 0) (hsp1 : 4288 ≤ sp) (hsp2 : sp + 1040 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4288) (4288 + 1040) true = true)
    (hst : st < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxl : xl < 2 ^ 40) (hn : n ≤ 128)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 j238) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 st) (h4 : S.regs 4 = BitVec.ofNat 64 xp) (h5 : S.regs 5 = BitVec.ofNat 64 xl)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (hmem : S.mem = M)
    (KC : n ≤ xl → ∀ S' : State, S'.pc = BitVec.ofNat 64 xJ → S'.sp = S.sp → S'.mem = S.mem →
      (∀ i, S'.regs i = S.regs i) → Reaches ((LibW.program.link impl).withExit ret) S' Q)
    (KB : xl < n → ∀ (S' : State) (M' : Memory), S'.pc = BitVec.ofNat 64 snE → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 1 = BitVec.ofNat 64 n → S'.regs 30 = BitVec.ofNat 64 bSnRet →
      S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 → S'.mem = M' →
      MemFrame M M' [(sp + 312, sp + 320), (sp + 896, sp + 904)] → M'.regions = M.regions →
      M'.readLE (sp + 312) 8 = xl → M'.readLE (sp + 896) 8 = xp →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  have tx := toInt_ofNat_lt (v := xl) (by omega)
  have tn := toInt_ofNat_lt (v := n) (by omega)
  by_cases hc : n ≤ xl
  · have hb : (BitVec.ofNat 64 n).toInt ≤ (BitVec.ofNat 64 xl).toInt := by rw [tx, tn]; omega
    janus_run [hb, tx, tn] until [xJ]
    refine KC hc _ ?_ ?_ ?_ ?_
    all_goals first | (janus_simp; done) | skip
    intro i; janus_simp
  · have hb : ¬ (BitVec.ofNat 64 n).toInt ≤ (BitVec.ofNat 64 xl).toInt := by rw [tx, tn]; omega
    generalize e18 : S.regs 18 = x18 at KB
    generalize e28 : S.regs 28 = x28 at KB
    generalize e29 : S.regs 29 = x29 at KB
    janus_run [hb, tx, tn] until [snE]
    refine KB (by omega) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?q1 ?q2
    case mf =>
      repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 312, sp + 320)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 896, sp + 904)) (by simp) (by simp only; omega) (by simp only; omega))
      exact MemFrame.refl _ _
    all_goals first | (janus_simp; done) | skip
    all_goals simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
      BitVec.toNat_ofNat, Nat.reducePow]
    all_goals omega

end FvModexp.Arm64.W4Pro
