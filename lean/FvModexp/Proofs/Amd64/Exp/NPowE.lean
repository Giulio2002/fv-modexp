import FvModexp.Proofs.Amd64.Exp.NPow
import FvModexp.Proofs.Amd64.Exp.EvDefs
import FvModexp.Proofs.Common.NPowNot

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): `m.isPow2()` fails (nat.go:376-388, inlined at `0x5e7800..0x5e7842`) → `expNNEven` entry
(agent expmc s73; twin of `Arm64.ExpN.powAllE`)

For a normalised even `m` that is not a power of two (`Expmc.notPow_step`): the loop skips the zero words, and at the
first non-zero word the test `i == len(m)-1 && x&(x-1) == 0` fails, so `logM, ok = 0, false` and
`z.expNNEven(stk, x, y, m)` is called (`0x5e78ba..0x5e78f2`: `y` stored to `[t - 0x108, t - 0xf0)`, `m` to
`[t - 0xf0, t - 0xd8)` (`R13`, the caller's `len m`/`cap m` words `t + 0x28`/`t + 0x30`), `AX := [t - 0x60]`,
`BX := R11`; return `evR = 0x5e78f7` pushed at `t - 0x110`). On `LibNE` (the callee `expNNEven` is not in `LibN`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- the return point of the `expNNEven` call (`0x5e78f7`) -/
abbrev evR : Nat := 6191351

/-- the continuation at `expNNEven`'s entry (`RSP = t - 0x110`; registers as at the loop head except `BX := R11`) -/
def EvK (impl : List Amd64.Segment) (ret0 : Nat) (Q : Amd64.Outcome → Prop) (G : Nat → BitVec 64)
    (fs : BitVec 64) (df : Bool) (x15 : BitVec 128) (t : Nat) (M : Janus.Arm64.Memory) : Prop :=
  ∀ (S' : State) (M' : Janus.Arm64.Memory),
    S'.rip = BitVec.ofNat 64 ExpEven.fnE → S'.regs 4 = BitVec.ofNat 64 (t - 0x110) →
    S'.regs 0 = G 0 → S'.regs 1 = G 1 → S'.regs 3 = G 11 → S'.regs 7 = G 7 →
    S'.regs 6 = G 6 → S'.regs 8 = G 8 → S'.regs 9 = G 9 →
    S'.regs 14 = G 14 → S'.fsBase = fs → S'.df = df → S'.xmm 15 = x15 → S'.mem = M' →
    MemFrame M M' [(t - 0x110, t - 0xd8)] → M'.regions = M.regions →
    M'.readLE (t - 0x110) 8 = evR → M'.readLE (t - 0x108) 8 = (G 12).toNat → M'.readLE (t - 0x100) 8 = (G 15).toNat →
    M'.readLE (t - 0xf8) 8 = (G 2).toNat → M'.readLE (t - 0xf0) 8 = (G 13).toNat →
    M'.readLE (t - 0xe8) 8 = M.readLE (t + 0x28) 8 → M'.readLE (t - 0xe0) 8 = M.readLE (t + 0x30) 8 →
    Reaches ((LibNE.program.link impl).withExit ret0) S' Q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.unusedSimpArgs false in
theorem powStepE (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (G : Nat → BitVec 64) (fs : BitVec 64) (df : Bool) (x15 : BitVec 128)
    (t mp n i : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x110) 0x188 true = true)
    (hmp : mp + 8 * n ≤ 2 ^ 48) (hma : M.accessible mp (8 * n) false = true) (hi : i < n)
    (hc : M.readLE (mp + 8 * i) 8 = 0 → i + 1 < n)
    (hc2 : M.readLE (mp + 8 * i) 8 ≠ 0 → i + 1 = n →
      (M.readLE (mp + 8 * i) 8 - 1) &&& M.readLE (mp + 8 * i) 8 ≠ 0)
    (h0 : M.readLE (t - 0x60) 8 = (G 0).toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 powH) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (hG : ∀ r, r ≠ 10 → S.regs r = G r) (h3 : G 3 = BitVec.ofNat 64 n) (h13 : G 13 = BitVec.ofNat 64 mp)
    (h10 : S.regs 10 = BitVec.ofNat 64 i) (hfs : S.fsBase = fs) (hdf : S.df = df) (hx : S.xmm 15 = x15)
    (hmem : S.mem = M)
    (KN : M.readLE (mp + 8 * i) 8 = 0 → ∀ S' : State, S'.rip = BitVec.ofNat 64 powH → (∀ r, r ≠ 10 → S'.regs r = G r) →
      S'.regs 10 = BitVec.ofNat 64 (i + 1) → S'.fsBase = fs → S'.df = df → S'.xmm 15 = x15 → S'.mem = M →
      Reaches ((LibNE.program.link impl).withExit ret0) S' Q)
    (KE : M.readLE (mp + 8 * i) 8 ≠ 0 → EvK impl ret0 Q G fs df x15 t M) :
    Reaches ((LibNE.program.link impl).withExit ret0) S Q := by
  have ha : M.accessible (mp + 8 * i) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hma (by omega) (by omega)
  have s0 := hG 0 (by decide); have s1 := hG 1 (by decide); have s2 := hG 2 (by decide)
  have s3 := hG 3 (by decide); have s6 := hG 6 (by decide); have s7 := hG 7 (by decide)
  have s8 := hG 8 (by decide); have s9 := hG 9 (by decide); have s11 := hG 11 (by decide)
  have s12 := hG 12 (by decide); have s13 := hG 13 (by decide); have s14 := hG 14 (by decide)
  have s15 := hG 15 (by decide)
  rw [h3] at s3; rw [h13] at s13
  have aa8 : t - 0x108 + 0xa8 = t - 0x60 := by omega
  have a130 : t - 0x108 + 0x130 = t + 0x28 := by omega
  have a138 : t - 0x108 + 0x138 = t + 0x30 := by omega
  have g0 : BitVec.ofNat 64 (G 0).toNat = G 0 := BitVec.ofNat_toNat _ _
  have hlt : M.readLE (mp + i * 8) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hi45 : i < 2 ^ 45 := by omega
  have r28 : M.readLE (t + 0x28) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have r30 : M.readLE (t + 0x30) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  subst hmem
  by_cases hw0 : S.mem.readLE (mp + 8 * i) 8 = 0
  · have hw' : S.mem.readLE (mp + i * 8) 8 = 0 := by rw [Nat.mul_comm]; exact hw0
    have := hc hw0
    janus64_run [hw', aa8, h0, g0] until [ExpEven.fnE, powH, 6191290, 6191436]
    refine KN hw0 _ rfl (fun r hr => ?_) ?_ hfs rfl hx rfl
    · simp only [setRegF_apply]
      by_cases r0 : r = 0
      · subst r0; simp
      · simp only [hr, r0, ite_false]; exact hG r hr
    · apply BitVec.eq_of_toNat_eq
      simp only [setRegF_apply, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega
  · have hw' : S.mem.readLE (mp + i * 8) 8 ≠ 0 := by rw [Nat.mul_comm]; exact hw0
    have es1 : BitVec.ofNat 64 (t - 0x108) - 8#64 = BitVec.ofNat 64 (t - 0x110) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    by_cases hl : i + 1 = n
    · have hand : (S.mem.readLE (mp + i * 8) 8 - 1) &&& S.mem.readLE (mp + i * 8) 8 ≠ 0 := by
        rw [Nat.mul_comm]; exact hc2 hw0 hl
      have hand' : S.mem.readLE (mp + i * 8) 8 &&& (S.mem.readLE (mp + i * 8) 8 - 1) ≠ 0 := by
        rw [Nat.and_comm]; exact hand
      janus64_run [hw', hand, hand', es1, aa8, a130, a138, h0, g0] until [ExpEven.fnE, powH, 6191436]
      refine KE hw0 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      iterate 9 (first | rfl | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; janus_assumption))
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; janus_assumption
      · exact hfs
      · rfl
      · exact hx
      · janus_frame
      · simp only [Janus.Arm64.Memory.regions_writeLE]
      all_goals (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, rdd_eq, Nat.mod_eq_of_lt (BitVec.isLt _), Nat.reducePow, Nat.reduceMod, h13, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt r28, Nat.mod_eq_of_lt r30]) <;> omega
    · janus64_run [hw', es1, aa8, a130, a138, h0, g0] until [ExpEven.fnE, powH, 6191436]
      refine KE hw0 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      iterate 9 (first | rfl | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; janus_assumption))
      · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; janus_assumption
      · exact hfs
      · rfl
      · exact hx
      · janus_frame
      · simp only [Janus.Arm64.Memory.regions_writeLE]
      all_goals (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, rdd_eq, Nat.mod_eq_of_lt (BitVec.isLt _), Nat.reducePow, Nat.reduceMod, h13, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt r28, Nat.mod_eq_of_lt r30]) <;> omega

/-- the whole failing `isPow2` loop from `i` (words `0..i-1` zero) to `expNNEven`'s entry -/
theorem powAllE (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (G : Nat → BitVec 64) (fs : BitVec 64) (df : Bool) (x15 : BitVec 128)
    (t mp n : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x110) 0x188 true = true)
    (hmp : mp + 8 * n ≤ 2 ^ 48) (hma : M.accessible mp (8 * n) false = true) (hn : 0 < n) (hN : NatNorm M mp n)
    (hnp : ¬∃ k, natVal M mp n = 2 ^ k)
    (h0 : M.readLE (t - 0x60) 8 = (G 0).toNat) (h3 : G 3 = BitVec.ofNat 64 n) (h4 : G 4 = BitVec.ofNat 64 (t - 0x108))
    (h13 : G 13 = BitVec.ofNat 64 mp)
    (KE : EvK impl ret0 Q G fs df x15 t M) :
    ∀ d i (S : State), n - 1 - i = d → i < n → (∀ j, j < i → M.readLE (mp + 8 * j) 8 = 0) →
      S.rip = BitVec.ofNat 64 powH → (∀ r, r ≠ 10 → S.regs r = G r) →
      S.regs 10 = BitVec.ofNat 64 i → S.fsBase = fs → S.df = df → S.xmm 15 = x15 → S.mem = M →
      Reaches ((LibNE.program.link impl).withExit ret0) S Q := by
  intro d
  induction d with
  | zero =>
    intro i S hd hi hz hpc hG h10 hfs hdf hx hmem
    have hst := Expmc.notPow_step M mp n i hn hN hnp hz hi
    exact powStepE impl ret0 hret Q G fs df x15 t mp n i M ht1 ht2 hacc hmp hma hi hst.1 hst.2 h0 S hpc
      ((hG 4 (by decide)).trans h4) hG h3 h13 h10 hfs hdf hx hmem (fun h0' => absurd (hst.1 h0') (by omega))
      (fun _ => KE)
  | succ d ih =>
    intro i S hd hi hz hpc hG h10 hfs hdf hx hmem
    have hst := Expmc.notPow_step M mp n i hn hN hnp hz hi
    exact powStepE impl ret0 hret Q G fs df x15 t mp n i M ht1 ht2 hacc hmp hma hi hst.1 hst.2 h0 S hpc
      ((hG 4 (by decide)).trans h4) hG h3 h13 h10 hfs hdf hx hmem
      (fun hw S' e1 e2 e3 e4 e5 e6 e7 => ih (i + 1) S' (by omega) (hst.1 hw)
        (fun j hj => if h : j < i then hz j h else by rw [show j = i by omega]; exact hw) e1 e2 e3 e4 e5 e6 e7)
      (fun _ => KE)

end FvModexp.Amd64.ExpN
