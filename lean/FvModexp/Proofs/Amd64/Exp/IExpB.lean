import FvModexp.Proofs.Amd64.Exp.IExpA
import FvModexp.Proofs.Amd64.Exp.NPro

set_option autoImplicit false

/-!
# `(*Int).exp` (amd64), segment B: the alias test `alias(z.abs, m.abs)` (int.go:593, nat.go:228; fn+0x11a .. fn+0x436)
(agent expmc s76; twin of `Arm64.IExp.runB`)

From `pA` with `AX = z`, `DI = m`, `RSP = t - 0x130`: `cap(z.abs) == 0`, `cap(m.abs) == 0` or different last-element
addresses (`ExpN.lastA`, mod `2^64`) → the join `pJ` with `DX = m`, `R8 = ` the old `DX` (`x.abs.ptr`) and `BX = z`
(reloaded from `t + 0x10` on the third way); no stores. The aliased case (`m = new(Int).Set(m)`, fn+0x15f) is refuted
by `hali`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.IExp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem runB (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibExp.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop)
    (t zA mA zp zc mp mc : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x138 ≤ t) (ht2 : t + 0x30 ≤ 2 ^ 48)
    (hzA : zA + 32 ≤ 2 ^ 48) (hza : M.accessible zA 32 false = true)
    (hmA : mA + 32 ≤ 2 ^ 48) (hma : M.accessible mA 32 false = true)
    (hacc : M.accessible (t + 0x10) 8 false = true) (hxs : M.readLE (t + 0x10) 8 = zA)
    (hz8 : M.readLE (zA + 8) 8 = zp) (hz24 : M.readLE (zA + 24) 8 = zc)
    (hm8 : M.readLE (mA + 8) 8 = mp) (hm24 : M.readLE (mA + 24) 8 = mc)
    (hali : zc = 0 ∨ mc = 0 ∨ ExpN.lastA zp zc ≠ ExpN.lastA mp mc)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 pA) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x130))
    (h0 : S.regs 0 = BitVec.ofNat 64 zA) (h3 : S.regs 3 = BitVec.ofNat 64 zA) (h7 : S.regs 7 = BitVec.ofNat 64 mA)
    (hmem : S.mem = M)
    (KB : ∀ (S' : State),
      S'.rip = BitVec.ofNat 64 pJ → S'.regs 4 = S.regs 4 →
      S'.regs 0 = S.regs 0 → S'.regs 1 = S.regs 1 → S'.regs 3 = BitVec.ofNat 64 zA → S'.regs 5 = S.regs 5 →
      S'.regs 6 = S.regs 6 → S'.regs 7 = S.regs 7 → S'.regs 11 = S.regs 11 → S'.regs 12 = S.regs 12 →
      S'.regs 13 = S.regs 13 → S'.regs 14 = S.regs 14 → S'.regs 15 = S.regs 15 →
      S'.regs 2 = BitVec.ofNat 64 mA → S'.regs 8 = S.regs 2 →
      S'.fsBase = S.fsBase → S'.df = S.df → S'.xmm 15 = S.xmm 15 → S'.mem = M →
      Reaches ((LibExp.program.link impl).withExit ret0) S' Q) :
    Reaches ((LibExp.program.link impl).withExit ret0) S Q := by
  have hzp : zp < 2 ^ 64 := hz8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hzc : zc < 2 ^ 64 := hz24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmp : mp < 2 ^ 64 := hm8 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have hmc : mc < 2 ^ 64 := hm24 ▸ Janus.Arm64.Memory.readLE_lt _ _ _
  have bz : ∀ v : Nat, v < 2 ^ 64 → ((BitVec.ofNat 64 v = 0#64) = (v = 0)) := by
    intro v hv; apply propext; constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
    · intro h; subst h; rfl
  have bl : ∀ a c a' c' : Nat, 0 < c → 0 < c' → ((BitVec.ofNat 64 a + BitVec.ofNat 64 c <<< 3 - 8#64 -
      (BitVec.ofNat 64 a' + BitVec.ofNat 64 c' <<< 3 - 8#64) = 0#64) = (ExpN.lastA a c = ExpN.lastA a' c')) := by
    intro a c a' c' hc hc'; apply propext
    simp only [ExpN.lastA, ← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have a2 : t - 0x130 + 0x140 = t + 0x10 := by omega
  have bzc := bz zc hzc; have bmc := bz mc hmc
  subst hz8 hz24 hm8 hm24 hmem
  by_cases hz0 : S.mem.readLE (zA + 24) 8 = 0
  · janus64_run [bzc, hz0, a2, hxs] until [pJ]
    refine KB _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> first | (janus64_simp; done) | rfl
  by_cases hm0 : S.mem.readLE (mA + 24) 8 = 0
  · janus64_run [bzc, hz0, bmc, hm0, a2, hxs] until [pJ]
    refine KB _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> first | (janus64_simp; done) | rfl
  have hne : ExpN.lastA (S.mem.readLE (mA + 8) 8) (S.mem.readLE (mA + 24) 8) ≠
      ExpN.lastA (S.mem.readLE (zA + 8) 8) (S.mem.readLE (zA + 24) 8) := by
    rcases hali with h | h | h
    · exact absurd h hz0
    · exact absurd h hm0
    · exact fun e => h e.symm
  have bx := bl (S.mem.readLE (mA + 8) 8) (S.mem.readLE (mA + 24) 8) (S.mem.readLE (zA + 8) 8)
    (S.mem.readLE (zA + 24) 8) (Nat.pos_of_ne_zero hm0) (Nat.pos_of_ne_zero hz0)
  janus64_run [bzc, hz0, bmc, hm0, bx, hne, a2, hxs] until [pJ]
  refine KB _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> first | (janus64_simp; done) | rfl

end FvModexp.Amd64.IExp
