import FvModexp.Proofs.Amd64.Exp.SlowDefs

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64): the runs of the two loop exits and the word test (agent asm s74; nat.go:749, 766-769)

* `runTX`: `t1` with `j = w` (`CMPQ CX, R15; JGE t1x`) → `t1x` (`R11 = len y - 2`, `R13 = [0xa0]`, `R15 = [0xa8]`,
  `CX = [0x90]`) → `iT`;
* `runSX`: `t2` with `j = 64` (`R12 = [0xb0]; CMPQ R12, $0x40; JGE iS`) → `iS` (`R11--`, `R9 = [0x218]`,
  `R12 = [0x1b8]`) → `iT`;
* `runEX`: `iT` with `R11 = -1` (`TESTQ R11, R11; JL ex`) → `ex`;
* `runIX`: `iT` with `R11 = i ≥ 0`: `[0xc0] = i`, `R9 = y[i]`, `[0x190] = AX`, `[0xb0] = 0`, `AX = [0x190]` → `t2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpSlow

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem runTX {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp yl w : Nat) (M : Memory)
    (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x220 ≤ 2 ^ 48)
    (hyl0 : 0 < yl) (hyl : yl ≤ 2 ^ 9) (hw : w ≤ 63)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 t1) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h1 : S.regs 1 = BitVec.ofNat 64 w) (h15 : S.regs 15 = BitVec.ofNat 64 w) (h11 : S.regs 11 = BitVec.ofNat 64 yl)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 iT → S'.mem = M →
      S'.regs 11 = BitVec.ofNat 64 (yl - 1) - 1#64 → S'.regs 13 = BitVec.ofNat 64 (M.readLE (sp + 0xa0) 8) →
      S'.regs 15 = BitVec.ofNat 64 (M.readLE (sp + 0xa8) 8) → S'.regs 1 = BitVec.ofNat 64 (M.readLE (sp + 0x90) 8) →
      (∀ k, k ≠ 1 → k ≠ 11 → k ≠ 13 → k ≠ 15 → S'.regs k = S.regs k) →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [hacc] until [iT]
  refine K _ ?rip ?mm ?g11 ?g13 ?g15 ?g1 ?gk ?gfs ?gx ?gdf
  case rip => rfl
  case mm => rfl
  case g11 =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  case g13 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g15 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g1 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case gk =>
    intro k k1 k11 k13 k15
    simp only [setRegF_apply, k1, k11, k13, k15, ↓reduceIte]
  case gfs => exact xf
  case gx => exact xx
  case gdf => rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem runSX {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp i : Nat) (M : Memory)
    (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x220 ≤ 2 ^ 48)
    (hi : i < 2 ^ 9) (hj : M.readLE (sp + 0xb0) 8 = 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 t2) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h11 : S.regs 11 = BitVec.ofNat 64 i)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 iT → S'.mem = M →
      S'.regs 11 = BitVec.ofNat 64 i - 1#64 → S'.regs 9 = BitVec.ofNat 64 (M.readLE (sp + 0x218) 8) →
      S'.regs 12 = BitVec.ofNat 64 (M.readLE (sp + 0x1b8) 8) →
      (∀ k, k ≠ 9 → k ≠ 11 → k ≠ 12 → S'.regs k = S.regs k) →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  subst hmem
  janus64_run [hacc, hj] until [iT]
  refine K _ ?rip ?mm ?g11 ?g9 ?g12 ?gk ?gfs ?gx ?gdf
  case rip => rfl
  case mm => rfl
  case g11 =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g9 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case g12 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case gk =>
    intro k k9 k11 k12
    simp only [setRegF_apply, k9, k11, k12, ↓reduceIte]
  case gfs => exact xf
  case gx => exact xx
  case gdf => rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem runEX {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 iT) (h11 : S.regs 11 = BitVec.ofNat 64 18446744073709551615)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 ex → S'.mem = S.mem → S'.regs = S.regs →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  janus64_run [BitVec.msb_eq_decide] until [ex]
  exact K _ rfl rfl rfl rfl rfl rfl

/-- `runIX`'s writes -/
@[reducible] def FI (sp : Nat) : List (Nat × Nat) :=
  [(sp + 0xc0, sp + 0xc8), (sp + 0x190, sp + 0x198), (sp + 0xb0, sp + 0xb8)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem runIX {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop) (sp yp i : Nat) (M : Memory)
    (hacc : M.accessible (sp - 8) 0x228 true = true) (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x220 ≤ 2 ^ 48)
    (hi : i < 2 ^ 9) (hy48 : yp + i * 8 + 8 ≤ 2 ^ 48) (hya : M.accessible (yp + i * 8) 8 false = true)
    (hyo : yp + i * 8 + 8 ≤ sp + 0xc0 ∨ sp + 0xc8 ≤ yp + i * 8)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 iT) (h4 : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h11 : S.regs 11 = BitVec.ofNat 64 i) (h12 : S.regs 12 = BitVec.ofNat 64 yp)
    (K : ∀ S' : State, S'.rip = BitVec.ofNat 64 t2 → MemFrame M S'.mem (FI sp) → S'.mem.regions = M.regions →
      S'.mem.readLE (sp + 0xc0) 8 = i → S'.mem.readLE (sp + 0xb0) 8 = 0 →
      S'.regs 9 = BitVec.ofNat 64 (M.readLE (yp + i * 8) 8) →
      (∀ k, k ≠ 9 → S'.regs k = S.regs k) →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hi9 : i % 18446744073709551616 = i := Nat.mod_eq_of_lt (by omega)
  generalize xf : S.fsBase = rf at K
  generalize xx : S.xmm 15 = rx at K
  generalize xd : S.df = rd at K
  generalize x0 : S.regs 0 = r0 at K
  subst hmem
  janus64_run [hacc, hya, BitVec.msb_eq_decide, hi9] until [t2]
  refine K _ ?rip ?mf ?rg ?mc0 ?mb0 ?g9 ?gk ?gfs ?gx ?gdf
  case rip => rfl
  case mf =>
    repeat (first
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xc0, sp + 0xc8)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0x190, sp + 0x198)) (by simp) (by simp only; omega) (by simp only; omega)
        | refine MemFrame.writeLE ?_ _ (r := (sp + 0xb0, sp + 0xb8)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  case rg => simp only [Janus.Arm64.Memory.regions_writeLE]
  case mc0 =>
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    simp only [Nat.reducePow]; omega
  case mb0 => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case g9 => simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  case gk =>
    intro k k9
    simp only [setRegF_apply, k9, ↓reduceIte]
    split <;> subst_vars <;> rfl
  case gfs => exact xf
  case gx => exact xx
  case gdf => rfl

end FvModexp.Amd64.ExpSlow
