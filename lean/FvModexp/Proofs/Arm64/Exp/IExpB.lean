import FvModexp.Proofs.Arm64.Exp.IExpA
import FvModexp.Proofs.Arm64.Exp.NPro

/-!
# `(*Int).exp` (arm64), segment B: the alias test `alias(z.abs, m.abs)` (int.go:593, nat.go:228; fn+0xcc .. fn+0x28c)

From `pA` with X0 = z, X3 = m: `cap(z.abs) == 0`, `cap(m.abs) == 0` or different last capacity words → the join `pJ`
with X17 = m (all three ways; no stores). The aliased case (`m = new(Int).Set(m)`, fn+0xfc) is refuted by `hali`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.IExp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runB (impl : List Segment) (ret0 : Nat) (hret : RetAddr (LibExp.program.link impl) ret0)
    (Q : Outcome → Prop)
    (zA mA zp zc mp mc : Nat) (M : Memory)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : M.accessible zA 32 false = true)
    (hmA : mA + 32 ≤ 2 ^ 48) (hma : M.accessible mA 32 false = true)
    (hz8 : M.readLE (zA + 8) 8 = zp) (hz24 : M.readLE (zA + 24) 8 = zc)
    (hm8 : M.readLE (mA + 8) 8 = mp) (hm24 : M.readLE (mA + 24) 8 = mc)
    (hali : zc = 0 ∨ mc = 0 ∨ ExpN.lastA zp zc ≠ ExpN.lastA mp mc)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 pA)
    (h0 : S.regs 0 = BitVec.ofNat 64 zA) (h3 : S.regs 3 = BitVec.ofNat 64 mA) (hmem : S.mem = M)
    (KB : ∀ (S' : State),
      S'.pc = BitVec.ofNat 64 pJ → S'.sp = S.sp →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 2 = S.regs 2 → S'.regs 3 = S.regs 3 →
      S'.regs 4 = S.regs 4 → S'.regs 7 = S.regs 7 → S'.regs 8 = S.regs 8 → S'.regs 9 = S.regs 9 →
      S'.regs 14 = S.regs 14 → S'.regs 15 = S.regs 15 → S'.regs 16 = S.regs 16 →
      S'.regs 17 = BitVec.ofNat 64 mA → S'.regs 18 = S.regs 18 → S'.regs 28 = S.regs 28 →
      S'.regs 29 = S.regs 29 → S'.regs 30 = S.regs 30 → S'.mem = M →
      Reaches ((LibExp.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret0) S Q := by
  have hzp : zp < 2 ^ 64 := hz8 ▸ Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := hz24 ▸ Memory.readLE_lt _ _ _
  have hmp : mp < 2 ^ 64 := hm8 ▸ Memory.readLE_lt _ _ _
  have hmc : mc < 2 ^ 64 := hm24 ▸ Memory.readLE_lt _ _ _
  subst hz8 hz24 hm8 hm24
  janus_run until [pJ, 0x1b13ec]
  all_goals first
    | (exfalso; (try simp only [ExpN.lastA] at *); omega)
    | (refine KB _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> first | (janus_simp; done) | rfl)

end FvModexp.Arm64.IExp
