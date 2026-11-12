import FvModexp.Proofs.Arm64.Exp.IExpA

/-!
# `(*Int).exp` (arm64), segment C: `mWords = m.abs` and the call `z.abs.expNN(nil, x.abs, y.abs, mWords, false)`
(int.go:596-599; fn+0x28c .. `nat.expNN`'s entry)

From `pJ` (X17 = m): `mWords` spilled at `SP' + 240, + 192, + 200` (= `t - 80`, `t - 128`, `t - 120`), the arguments
X0..X2 = z.abs (reloaded from `z`), X3 = 0 (stk = nil), X4..X6 = x.abs (X14..X16), X7..X9 = y.abs, X10..X12 = m.abs,
X13 = slow (X4 = 0), `CALL nat.expNN` (X30 = `raN`). Stops at expNN's entry.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IExp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runC (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibExp.program.link impl) ret0)
    (Q : Outcome → Prop)
    (t zA mA zp zl zc mp n mc : Nat) (M : Memory)
    (hal : t % 16 = 0) (ht1 : 336 ≤ t) (ht2 : t + 48 ≤ 2 ^ 48)
    (hacc : M.accessible (t - 328) 376 true = true)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : M.accessible zA 32 false = true) (hzS : zA + 32 ≤ t - 328 ∨ t + 48 ≤ zA)
    (hmA : mA + 32 ≤ 2 ^ 48) (hma : M.accessible mA 32 false = true)
    (hz8 : M.readLE (zA + 8) 8 = zp) (hz16 : M.readLE (zA + 16) 8 = zl) (hz24 : M.readLE (zA + 24) 8 = zc)
    (hm8 : M.readLE (mA + 8) 8 = mp) (hm16 : M.readLE (mA + 16) 8 = n) (hm24 : M.readLE (mA + 24) 8 = mc)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 pJ) (hsp : S.sp = BitVec.ofNat 64 (t - 320))
    (h0 : S.regs 0 = BitVec.ofNat 64 zA) (h4 : S.regs 4 = 0#64) (h17 : S.regs 17 = BitVec.ofNat 64 mA)
    (hmem : S.mem = M)
    (KC : ∀ (S' : State) (M' : Memory),
      S'.pc = BitVec.ofNat 64 fnN → S'.sp = BitVec.ofNat 64 (t - 320) →
      S'.regs 0 = BitVec.ofNat 64 zp → S'.regs 1 = BitVec.ofNat 64 zl → S'.regs 2 = BitVec.ofNat 64 zc →
      S'.regs 3 = 0#64 → S'.regs 4 = S.regs 14 → S'.regs 5 = S.regs 15 → S'.regs 6 = S.regs 16 →
      S'.regs 7 = S.regs 7 → S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 →
      S'.regs 10 = BitVec.ofNat 64 mp → S'.regs 11 = BitVec.ofNat 64 n → S'.regs 12 = BitVec.ofNat 64 mc →
      S'.regs 13 = 0#64 → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 → S'.regs 29 = S.regs 29 →
      S'.regs 30 = BitVec.ofNat 64 raN → S'.mem = M' →
      MemFrame M M' [(t - 128, t - 112), (t - 80, t - 72)] → M'.regions = M.regions →
      M'.readLE (t - 128) 8 = n → M'.readLE (t - 120) 8 = mc → M'.readLE (t - 80) 8 = mp →
      Reaches ((LibExp.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret0) S Q := by
  have hzp : zp < 2 ^ 64 := hz8 ▸ Memory.readLE_lt _ _ _
  have hzl : zl < 2 ^ 64 := hz16 ▸ Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := hz24 ▸ Memory.readLE_lt _ _ _
  have hmp : mp < 2 ^ 64 := hm8 ▸ Memory.readLE_lt _ _ _
  have hn : n < 2 ^ 64 := hm16 ▸ Memory.readLE_lt _ _ _
  have hmc : mc < 2 ^ 64 := hm24 ▸ Memory.readLE_lt _ _ _
  subst hz8 hz16 hz24 hm8 hm16 hm24
  janus_run until [fnN]
  refine KC _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?mf ?rg ?_ ?_ ?_
  case mf =>
    dsimp only
    repeat (first
      | refine MemFrame.writeLE ?_ _ (r := (t - 128, t - 112)) (by simp) (by simp only; omega) (by simp only; omega)
      | refine MemFrame.writeLE ?_ _ (r := (t - 80, t - 72)) (by simp) (by simp only; omega) (by simp only; omega))
    exact MemFrame.refl _ _
  all_goals first | (janus_simp; done) | skip
  all_goals first | (simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; done) | skip
  all_goals first | omega | skip

end FvModexp.Arm64.IExp
