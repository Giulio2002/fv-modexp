import FvModexp.Proofs.Amd64.Exp.LibExp
import FvModexp.Proofs.Common.BitLemmas

set_option autoImplicit false

/-!
# `(*Int).exp` (amd64), segment A: entry → the alias test (int.go:575-593; fn+0x0 .. fn+0x11a) (agent expmc s76;
twin of `Arm64.IExp.runA`)

`z.exp(x = z, y, m, slow = false)` as `Run` calls it (`AX = BX = z`, `CX = y`, `DI = m`, `SI = 0`; entry `RSP = t`):
stack check (`LEAQ -0xb0(SP), R12; CMPQ R12, 0x10(R14); JBE` falls through), `PUSHQ BP` (`[t - 8]`), `MOVQ SP, BP`,
`SUBQ $0x128, SP` (`RSP = t - 0x130`), the spills `AX → t + 8`, `BX → t + 0x10`, `DI → t + 0x20`, byte `SI → t + 0x28`,
`xWords = x.abs` (`DX, R11, R12`), `y.neg = false` (`JE` taken), `yWords = y.abs` (`R15, R13, CX`; `len → t - 0xa8`,
`ptr → t - 0x68`), `m ≠ nil`, `z ≠ m`; stops at `pA` = fn+0x11a (`MOVQ 0x18(AX), R8`, the alias test). The off-path
targets (`y.neg`, `m == nil`, `z == m`, morestack) are refuted by the premises.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IExp

/-- `(*Int).exp`'s entry -/
abbrev fnI : Nat := 0x5e3180
/-- `nat.expNN`'s entry -/
abbrev fnN : Nat := 0x5e6fa0
/-- the return point of the `expNN` call (fn+0x4a5) -/
abbrev raN : Nat := 0x5e3625
/-- the alias test `alias(z.abs, m.abs)` (fn+0x11a) -/
abbrev pA : Nat := 0x5e329a
/-- the join after the alias test (fn+0x436: `MOVQ 0x8(DX), DI` with `DX = m`) -/
abbrev pJ : Nat := 0x5e35b6

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runA (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibExp.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop)
    (t g zA yA mA zp zl zc yp yl yc : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x138 ≤ t) (ht2 : t + 0x30 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x130) 0x160 true = true)
    (hg1 : g + 24 ≤ 2 ^ 48) (hg2 : M.accessible (g + 16) 8 false = true) (hg3 : M.readLE (g + 16) 8 + 0xb0 < t)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : M.accessible zA 32 false = true) (hzS : zA + 32 ≤ t - 0x130 ∨ t + 0x30 ≤ zA)
    (hyA : yA + 32 ≤ 2 ^ 48) (hya : M.accessible yA 32 false = true) (hyS : yA + 32 ≤ t - 0x130 ∨ t + 0x30 ≤ yA)
    (hmA0 : mA ≠ 0) (hmA : mA < 2 ^ 64) (hzm : zA ≠ mA)
    (hz8 : M.readLE (zA + 8) 8 = zp) (hz16 : M.readLE (zA + 16) 8 = zl) (hz24 : M.readLE (zA + 24) 8 = zc)
    (hy0 : M.readLE yA 1 = 0)
    (hy8 : M.readLE (yA + 8) 8 = yp) (hy16 : M.readLE (yA + 16) 8 = yl) (hy24 : M.readLE (yA + 24) 8 = yc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 fnI) (hsp : S.regs 4 = BitVec.ofNat 64 t)
    (h0 : S.regs 0 = BitVec.ofNat 64 zA) (h3 : S.regs 3 = BitVec.ofNat 64 zA) (h1 : S.regs 1 = BitVec.ofNat 64 yA)
    (h7 : S.regs 7 = BitVec.ofNat 64 mA) (h6 : S.regs 6 = 0#64)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hmem : S.mem = M)
    (KA : ∀ (S' : State) (M' : Janus.Arm64.Memory),
      S'.rip = BitVec.ofNat 64 pA → S'.regs 4 = BitVec.ofNat 64 (t - 0x130) →
      S'.regs 0 = BitVec.ofNat 64 zA → S'.regs 3 = BitVec.ofNat 64 zA → S'.regs 7 = BitVec.ofNat 64 mA →
      S'.regs 6 = 0#64 → S'.regs 2 = BitVec.ofNat 64 zp → S'.regs 11 = BitVec.ofNat 64 zl →
      S'.regs 12 = BitVec.ofNat 64 zc → S'.regs 13 = BitVec.ofNat 64 yl → S'.regs 15 = BitVec.ofNat 64 yp →
      S'.regs 1 = BitVec.ofNat 64 yc → S'.regs 5 = BitVec.ofNat 64 (t - 8) →
      S'.regs 14 = S.regs 14 → S'.fsBase = S.fsBase → S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = M' →
      MemFrame M M' [(t - 0x130, t), (t + 8, t + 0x30)] → M'.regions = M.regions →
      M'.readLE (t - 8) 8 = (S.regs 5).toNat → M'.readLE (t + 8) 8 = zA → M'.readLE (t + 0x10) 8 = zA →
      M'.readLE (t + 0x20) 8 = mA → M'.readLE (t + 0x28) 1 = 0 → M'.readLE (t - 0xa8) 8 = yl →
      M'.readLE (t - 0x68) 8 = yp →
      Reaches ((LibExp.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret0) S Q := by
  have hgs : M.readLE (g + 16) 8 < 2 ^ 64 := Janus.Arm64.Memory.readLE_lt _ _ _
  have hzp : zp < 2 ^ 64 := hz8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hzl : zl < 2 ^ 64 := hz16 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := hz24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyp : yp < 2 ^ 64 := hy8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyl : yl < 2 ^ 64 := hy16 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hyc : yc < 2 ^ 64 := hy24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have h5 : (S.regs 5).toNat < 2 ^ 64 := (S.regs 5).isLt
  have es1 : BitVec.ofNat 64 t - 8#64 = BitVec.ofNat 64 (t - 8) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have es2 : BitVec.ofNat 64 (t - 8) - 296#64 = BitVec.ofNat 64 (t - 0x130) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hm0 : (BitVec.ofNat 64 mA = 0#64) = False := by
    apply propext; constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
    · intro h; exact h.elim
  have hzm' : (BitVec.ofNat 64 mA - BitVec.ofNat 64 zA = 0#64) = False := by
    apply propext; constructor
    · intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
    · intro h; exact h.elim
  have a1 : t - 0x130 + 0x138 = t + 8 := by omega
  have a2 : t - 0x130 + 0x140 = t + 0x10 := by omega
  have a3 : t - 0x130 + 0x150 = t + 0x20 := by omega
  have a4 : t - 0x130 + 0x158 = t + 0x28 := by omega
  have a5 : t - 0x130 + 0x88 = t - 0xa8 := by omega
  have a6 : t - 0x130 + 0xc8 = t - 0x68 := by omega
  subst hz8 hz16 hz24 hy8 hy16 hy24 hmem
  janus64_run [es1, es2, hm0, hzm', a1, a2, a3, a4, a5, a6, hy0] until [pA]
  refine KA _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7
  case mf => janus_frame
  all_goals first | (janus64_simp; done) | skip
  all_goals first | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done) | skip
  all_goals first | omega | skip

end FvModexp.Amd64.IExp
