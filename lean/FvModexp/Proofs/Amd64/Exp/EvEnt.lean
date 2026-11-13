import FvModexp.Proofs.Amd64.Exp.EvDefs

set_option autoImplicit false

/-!
# `nat.expNNEven` (amd64): the straight-line entry segments (asm s56; twin of infra's arm64 `EvEnt`)

* `entA`: `fnE` → `tzH` (stack guard, `PUSHQ BP`, `SUBQ $0x140`, `X15` into the defer slot `0x138`, spills
  `R9 → 0x1b0, CX → 0x190, AX → 0x180, SI → 0x1a0, R8 → 0x1a8`, defer bit `0x77 = 0`, result `0xe0 .. 0xf8` zeroed,
  `DX = ml` (`[sp + 0x170]`), `ml ≠ 0` → `R10 = mp`, `BX = 0`).
* `entB`: `enS` → `(*stack).nat`'s entry (`AX = st`, `BX = a1 n`, return address `nat1R` at `sp - 8`): spills `DI → 0x198`,
  `n → 0xb0`, `a2 ml n → 0xd8`, the defer record (`0x120 = deferwrap1`, `0x128 = st`, `0x130 = len`, `0x138 = sp + 0x120`),
  defer bit `0x77 = 1`.
Only the listed registers are carried over; memory changes are framed by `FW sp` / `FB sp`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpEven

/-- `(*stack).nat`'s entry -/
abbrev stkNatE : Nat := 0x5e6480


/-- `entA`'s writes -/
@[reducible] def FW (sp : Nat) : List (Nat × Nat) := [(sp + 0x77, sp + 0xf8), (sp + 0x138, sp + 0x148), (sp + 0x180, sp + 0x1b8)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`fnE` → `tzH`** -/
theorem entA {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop)
    (sp g zp zc st xp xl xc mp ml bp : Nat) (M : Memory)
    (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48) (hacc : M.accessible sp 0x1b8 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 < sp + 0x80)
    (hml : 0 < ml) (hml' : ml < 2 ^ 64) (hmp : mp < 2 ^ 64) (hbp : bp < 2 ^ 64)
    (hzp : zp < 2 ^ 64) (hzc : zc < 2 ^ 64) (hxp : xp < 2 ^ 64) (hxl : xl < 2 ^ 64) (hxc : xc < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 fnE) (h4 : S.regs 4 = BitVec.ofNat 64 (sp + 0x148))
    (h0 : S.regs 0 = BitVec.ofNat 64 zp) (h1 : S.regs 1 = BitVec.ofNat 64 zc) (h7 : S.regs 7 = BitVec.ofNat 64 st)
    (h6 : S.regs 6 = BitVec.ofNat 64 xp) (h8 : S.regs 8 = BitVec.ofNat 64 xl) (h9 : S.regs 9 = BitVec.ofNat 64 xc)
    (h5 : S.regs 5 = BitVec.ofNat 64 bp) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (hrm : M.readLE (sp + 0x170) 8 = ml) (hrp : M.readLE (sp + 0x168) 8 = mp)
    (KT : ∀ (S' : State) (M' : Memory),
      S'.rip = BitVec.ofNat 64 tzH → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = BitVec.ofNat 64 (sp + 0x140) →
      S'.regs 3 = BitVec.ofNat 64 0 → S'.regs 2 = BitVec.ofNat 64 ml → S'.regs 10 = BitVec.ofNat 64 mp →
      S'.regs 7 = BitVec.ofNat 64 st → S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase = S.fsBase →
      S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.mem = M' → MemFrame M M' (FW sp) → M'.regions = M.regions →
      M'.readLE (sp + 0x140) 8 = bp → M'.readLE (sp + 0x180) 8 = zp → M'.readLE (sp + 0x190) 8 = zc →
      M'.readLE (sp + 0x1a0) 8 = xp → M'.readLE (sp + 0x1a8) 8 = xl → M'.readLE (sp + 0x1b0) 8 = xc →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (sp + 328) - 328#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (sp + 320) - 320#64 = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es3 : BitVec.ofNat 64 (sp + 328) - 8#64 = BitVec.ofNat 64 (sp + 320) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus64_run [hrm, hrp, es1, es2, es3] until [tzH]
  refine KT _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x77, sp + 0xf8)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x138, sp + 0x148)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x180, sp + 0x1b8)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | skip

theorem sar_small (x : BitVec 64) (k : Nat) (h : x.toNat < 2 ^ 63) : x.sshiftRight k = x >>> k :=
  BitVec.sshiftRight_eq_of_msb_false (by rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega)

/-- `ml - n/64` (`SARQ $0x3f; SHRQ $0x3a; ADDQ; SARQ $6; SUBQ`, signed rounding with `n ≥ 0`) -/
theorem a2_nat {n ml : Nat} (hn : n < 2 ^ 20) (hnm : n / 64 ≤ ml) (hml : ml < 2 ^ 20) :
    (18446744073709551616 - ((BitVec.ofNat 64 n + (BitVec.ofNat 64 n).sshiftRight 63 >>> 58).sshiftRight 6).toNat + ml) %
      18446744073709551616 = a2 ml n := by
  have h1 : (BitVec.ofNat 64 n).toNat < 2 ^ 63 := by rw [BitVec.toNat_ofNat]; omega
  have e0 : (BitVec.ofNat 64 n).sshiftRight 63 >>> 58 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [sar_small _ _ h1]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
  rw [e0, BitVec.add_zero, sar_small _ _ h1, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  simp only [a2, Nat.reducePow]; omega

/-- `entB`'s writes -/
@[reducible] def FB (sp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0x77, sp + 0x78), (sp + 0xb0, sp + 0xb8), (sp + 0xd8, sp + 0xe0), (sp + 0x120, sp + 0x140),
    (sp + 0x198, sp + 0x1a0)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`enS` → `(*stack).nat`'s entry** (`AX = st`, `BX = n/64 + 1`, return address `nat1R`) -/
theorem entB {impl : List Amd64.Segment} (ret0 : W64) (Q : State → Prop)
    (sp g st ml n len0 : Nat) (M : Memory)
    (hsp1 : 8 ≤ sp) (hsp2 : sp + 0x1b8 ≤ 2 ^ 48) (hacc : M.accessible (sp - 8) 0x1c0 true = true)
    (hst1 : M.accessible st 24 false = true) (hst2 : st + 24 ≤ 2 ^ 48) (hstw : st + 24 ≤ sp - 8 ∨ sp + 0x1b8 ≤ st)
    (hl0 : M.readLE (st + 8) 8 = len0) (hn : n < 2 ^ 20) (hml : ml < 2 ^ 20) (hnm : n / 64 < ml)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 enS) (h4 : S.regs 4 = BitVec.ofNat 64 sp)
    (h3 : S.regs 3 = BitVec.ofNat 64 n) (h7 : S.regs 7 = BitVec.ofNat 64 st) (h2 : S.regs 2 = BitVec.ofNat 64 ml)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (KN : ∀ (S' : State) (M' : Memory),
      S'.rip = BitVec.ofNat 64 stkNatE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = BitVec.ofNat 64 st → S'.regs 3 = BitVec.ofNat 64 (a1 n) → S'.regs 5 = S.regs 5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      S'.mem = M' → MemFrame M M' (FB sp) → M'.regions = M.regions →
      M'.readLE (sp - 8) 8 = nat1R → M'.readLE (sp + 0x198) 8 = st → M'.readLE (sp + 0xb0) 8 = n →
      M'.readLE (sp + 0xd8) 8 = a2 ml n → M'.readLE (sp + 0x120) 8 = dwE → M'.readLE (sp + 0x128) 8 = st →
      M'.readLE (sp + 0x130) 8 = len0 → M'.readLE (sp + 0x138) 8 = sp + 0x120 →
      ReachesRet (LibNE.program.link impl) ret0 S' Q) :
    ReachesRet (LibNE.program.link impl) ret0 S Q := by
  have hl0' : M.readLE (st + 8) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have e3 : (BitVec.ofNat 64 n + 64#64) >>> 6 = BitVec.ofNat 64 (a1 n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, a1]; omega
  have e4 : BitVec.ofNat 64 sp - 8#64 = BitVec.ofNat 64 (sp - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus64_run [hl0, e3, e4] until [stkNatE]
  refine KN _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf =>
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (sp - 8, sp)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x77, sp + 0x78)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0xb0, sp + 0xb8)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0xd8, sp + 0xe0)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x120, sp + 0x140)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (sp + 0x198, sp + 0x1a0)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus64_simp; done) | skip
  all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | omega | exact a2_nat hn (by omega) hml

end FvModexp.Amd64.ExpEven
