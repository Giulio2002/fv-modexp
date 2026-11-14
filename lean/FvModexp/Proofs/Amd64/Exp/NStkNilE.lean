import FvModexp.Proofs.Amd64.Exp.NStk
import FvModexp.Proofs.Amd64.Exp.LibNE
import FvModexp.Proofs.Amd64.Nat.Free

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`: `J2` = fn+0x19c → the `sync.(*Pool).Get` entry (agent expmc s74; twin of
`Arm64.ExpN.stkNilE`, directly on `LibNE`)

nat.go:663-676, 287 with `len m ≠ 0`, `stk == nil` (`RDI = 0`; `RSP = t - 0x108`): spills `R8 → t + 0x60`,
`SI → t + 0x58` (the `y == 1 && len m == 0` test falls through since `R11 = len m ≠ 0`), `R10` byte `→ t + 0x70`,
`R9 → t + 0x68`, `TESTQ DI` taken: `BX → t - 0x80`, `CX → t - 0x70`, `AX → t - 0x38`, `LEAQ stackPool, AX`,
`CALL sync.(*Pool).Get` (return `getR` = fn+0x310 pushed at `t - 0x110`). Continuation form.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- the return point of the `Pool.Get` call (`0x5e72b0`) -/
abbrev getR : Nat := 6189744
/-- the return point of the `newobject(type:big.stack)` call (`0x5e72df`) -/
abbrev noR : Nat := 6189791

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.unusedSimpArgs false in
theorem stkNilE (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibNE.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (t yp yl n : Nat)
    (M : Janus.Arm64.Memory) (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48)
    (hacc : M.accessible (t - 0x110) 0x188 true = true)
    (hyl : yl < 2 ^ 64) (hn : n < 2 ^ 64) (hn0 : 0 < n) (hyp : yp < 2 ^ 64)
    (hya : yl = 1 → M.accessible yp 8 false = true)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 6189372) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (h7 : S.regs 7 = 0#64) (h12 : S.regs 12 = BitVec.ofNat 64 yp) (h15 : S.regs 15 = BitVec.ofNat 64 yl)
    (h11 : S.regs 11 = BitVec.ofNat 64 n) (hmem : S.mem = M)
    (KG : ∀ (X : State) (M' : Janus.Arm64.Memory),
      X.rip = BitVec.ofNat 64 (cA "sync.(*Pool).Get") → X.regs 4 = BitVec.ofNat 64 (t - 0x110) →
      X.regs 0 = BitVec.ofNat 64 Free.poolA → X.regs 5 = S.regs 5 →
      X.regs 14 = S.regs 14 → X.fsBase = S.fsBase → X.df = S.df → X.xmm 15 = S.xmm 15 → X.mem = M' →
      MemFrame M M' [(t - 0x110, t - 0x108), (t - 0x80, t - 0x78), (t - 0x70, t - 0x68), (t - 0x38, t - 0x30),
        (t + 0x58, t + 0x78)] →
      M'.regions = M.regions →
      M'.readLE (t - 0x110) 8 = getR → M'.readLE (t - 0x80) 8 = (S.regs 3).toNat →
      M'.readLE (t - 0x70) 8 = (S.regs 1).toNat → M'.readLE (t - 0x38) 8 = (S.regs 0).toNat →
      M'.readLE (t + 0x58) 8 = (S.regs 6).toNat → M'.readLE (t + 0x60) 8 = (S.regs 8).toNat →
      M'.readLE (t + 0x68) 8 = (S.regs 9).toNat → M'.readLE (t + 0x70) 1 = (S.regs 10).toNat % 256 →
      Reaches ((LibNE.program.link impl).withExit ret0) X Q) :
    Reaches ((LibNE.program.link impl).withExit ret0) S Q := by
  have es1 : BitVec.ofNat 64 (t - 0x108) - 8#64 = BitVec.ofNat 64 (t - 0x110) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have bn : (BitVec.ofNat 64 n = 0#64) = False := by
    simp only [eq_iff_iff, iff_false]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this; omega
  subst hmem
  by_cases hy1 : yl = 1
  · have hya' := hya hy1
    janus64_run [es1, bn] until [cA "sync.(*Pool).Get"]
    all_goals refine KG _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | (simp only [Janus.Arm64.Memory.regions_writeLE]; done)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
      | janus_frame
      | (janus64_simp; done)
      | rfl
  · janus64_run [es1, bn] until [cA "sync.(*Pool).Get"]
    all_goals refine KG _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | (simp only [Janus.Arm64.Memory.regions_writeLE]; done)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done)
      | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
          rd_wr_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
      | janus_frame
      | (janus64_simp; done)
      | rfl

end FvModexp.Amd64.ExpN
