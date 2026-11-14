import FvModexp.Proofs.Amd64.Exp.IExpA

set_option autoImplicit false

/-!
# `(*Int).exp` (amd64), segment C: `mWords = m.abs` and the call `z.abs.expNN(nil, x.abs, y.abs, mWords, false)`
(int.go:596-599; fn+0x436 .. `nat.expNN`'s entry) (agent expmc s76; twin of `Arm64.IExp.runC`)

From `pJ` (`DX = m`, `RSP = t - 0x130`): `mWords` spilled at `t - 0x80`, `t - 0x78`, `t - 0x58` (len, cap, ptr), the
register arguments `AX, BX, CX` = z.abs (reloaded from `z`), `DI = 0` (stk = nil), `SI, R8, R9` = x.abs (`R8, R11,
R12`), `R10 = slow` (`MOVL SI, R10`, `SI = 0`), the stack arguments y.abs (`R15, R13, CX`) and m.abs at
`t - 0x130 … t - 0x100`, `CALL nat.expNN` (`[t - 0x138] = raN`). Stops at expNN's entry (`RSP = t - 0x138`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IExp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runC (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibExpI.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop)
    (t zA mA zp zl zc yp yl yc mp n mc : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x140 ≤ t) (ht2 : t + 0x30 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x138) 0x168 true = true)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : M.accessible zA 32 false = true) (hzS : zA + 32 ≤ t - 0x138 ∨ t + 0x30 ≤ zA)
    (hmA : mA + 32 ≤ 2 ^ 48) (hma : M.accessible mA 32 false = true)
    (hz8 : M.readLE (zA + 8) 8 = zp) (hz16 : M.readLE (zA + 16) 8 = zl) (hz24 : M.readLE (zA + 24) 8 = zc)
    (hm8 : M.readLE (mA + 8) 8 = mp) (hm16 : M.readLE (mA + 16) 8 = n) (hm24 : M.readLE (mA + 24) 8 = mc)
    (hyp : yp < 2 ^ 64) (hyl : yl < 2 ^ 64) (hyc : yc < 2 ^ 64)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 pJ) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x130))
    (h0 : S.regs 0 = BitVec.ofNat 64 zA) (h2 : S.regs 2 = BitVec.ofNat 64 mA) (h6 : S.regs 6 = 0#64)
    (h15 : S.regs 15 = BitVec.ofNat 64 yp) (h13 : S.regs 13 = BitVec.ofNat 64 yl)
    (h1 : S.regs 1 = BitVec.ofNat 64 yc) (hmem : S.mem = M)
    (KC : ∀ (S' : State) (M' : Janus.Arm64.Memory),
      S'.rip = BitVec.ofNat 64 fnN → S'.regs 4 = BitVec.ofNat 64 (t - 0x138) →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 3 = BitVec.ofNat 64 zl → S'.regs 1 = BitVec.ofNat 64 zc →
      S'.regs 7 = 0#64 → S'.regs 6 = S.regs 8 → S'.regs 8 = S.regs 11 → S'.regs 9 = S.regs 12 →
      S'.regs 10 = 0#64 → S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = M' →
      MemFrame M M' [(t - 0x138, t - 0x100), (t - 0x80, t - 0x70), (t - 0x58, t - 0x50)] → M'.regions = M.regions →
      M'.readLE (t - 0x138) 8 = raN →
      M'.readLE (t - 0x130) 8 = yp → M'.readLE (t - 0x128) 8 = yl → M'.readLE (t - 0x120) 8 = yc →
      M'.readLE (t - 0x118) 8 = mp → M'.readLE (t - 0x110) 8 = n → M'.readLE (t - 0x108) 8 = mc →
      M'.readLE (t - 0x80) 8 = n → M'.readLE (t - 0x78) 8 = mc → M'.readLE (t - 0x58) 8 = mp →
      Reaches ((LibExpI.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibExpI.program.link impl).withExit ret0) S Q := by
  have hzp : zp < 2 ^ 64 := hz8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hzl : zl < 2 ^ 64 := hz16 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := hz24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmp : mp < 2 ^ 64 := hm8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hn : n < 2 ^ 64 := hm16 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmc : mc < 2 ^ 64 := hm24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have es1 : BitVec.ofNat 64 (t - 0x130) - 8#64 = BitVec.ofNat 64 (t - 0x138) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have b1 : t - 0x130 + 0xb0 = t - 0x80 := by omega
  have b2 : t - 0x130 + 0xb8 = t - 0x78 := by omega
  have b3 : t - 0x130 + 0xd8 = t - 0x58 := by omega
  have c1 : t - 0x130 + 8 = t - 0x128 := by omega
  have c2 : t - 0x130 + 0x10 = t - 0x120 := by omega
  have c3 : t - 0x130 + 0x18 = t - 0x118 := by omega
  have c4 : t - 0x130 + 0x20 = t - 0x110 := by omega
  have c5 : t - 0x130 + 0x28 = t - 0x108 := by omega
  subst hz8 hz16 hz24 hm8 hm16 hm24 hmem
  janus64_run [es1, b1, b2, b3, c1, c2, c3, c4, c5] until [fnN]
  refine KC _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case mf => janus_frame
  all_goals first | (janus64_simp; done) | skip
  all_goals first | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done) | skip
  all_goals first | omega | skip

end FvModexp.Amd64.IExp
