import FvModexp.Proofs.Arm64.ExpQ.SlowGQ
import FvModexp.Proofs.Arm64.NatQ.MulHypQ
import FvModexp.Proofs.Arm64.Exp.EvMulG

set_option autoImplicit false

/-! (Q-form twin of Exp/EvMulG.lean, TIGHT COSTS, agent expmc s44; adapted from infra's `ExpEven.NatMulG`)
# `nat.mul` (arm64) in the empty-tolerant Q-form premise `Q.ExpSlow.MulHypGQ`

`x_preGQ`: `MulPreG ∧ CapIn0 ∧ CapIn0 ∧ MulXG ∧ level twin` gives divmc's Q-form `Q.NatMul.MPre` (whose operand facts
are already guarded by `0 < xl`/`0 < xc`, and whose alias disjunction is vacuous for an empty `z` or operand);
the post is divmc's `Q.NatMul.q_post`. `mulGQ` from `Q.NatMul.ens` (no separate empty path: `nat.mul`'s Q summary
already admits empty operands).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (RdIn RdIn0)
open FvModexp.Arm64.ExpEven (CapIn0 MulPreG MulXG)
open FvModexp.Arm64.NatMul (wordT_rt')

set_option maxRecDepth 20000 in
theorem x_preMQ {R : RtInv} {H b : Nat} {L : List (Nat × Nat)} {zp zl zc st x xl xc y yl yc : Nat} {s : State}
    (h : MulPreG R b (mulCQ xl yl + stkR H s.mem st) L mulWX 88 zp zl zc st x xl y yl s)
    (hcx : CapIn0 R L x xl xc) (hcy : CapIn0 R L y yl yc)
    (hx : MulXG R L s mulWX 88 st zp zc x xl xc y yl yc) (hH : stLen s.mem st + 4 * (xl + yl) + 64 ≤ H) :
    Q.NatMul.MPre R b H L mulWX zp zc st x xl xc y yl yc s := by
  obtain ⟨hce, hsv, hglb, -, ⟨hz40, hzl, hzw⟩, ⟨hxl40, hxr⟩, ⟨hyl40, hyr⟩, hx12, hy12, hzx, hzy,
    ⟨hsok, hstw, hstg, hsta⟩, hlen, hza, hxa, hya, hcost, hinv⟩ := h
  obtain ⟨hxc, hxc40, hxh⟩ := hcx
  obtain ⟨hyc, hyc40, hyh⟩ := hcy
  obtain ⟨⟨hst0, hswb, hfh, hfw, hfg, hsf, hsgA, hfgA⟩, hzo, hzxc, hzyc, hzop, hxop, hyop⟩ := hx
  have hro : RoOut R := hce.2.2.2.2.2.2.2
  refine ⟨hce, mulW_le_X hx12 hy12, hsv, hglb, wordT_rt' hro,
    ⟨⟨hxc, hxc40, hx12, fun h0 => (hxr h0).2.1, hxh,
      fun h0 => ⟨(hxr h0).2.2.2.2, (hxa (by omega)).1.symm, (hxop (by omega)).1, (hxop (by omega)).2⟩⟩,
     ⟨hyc, hyc40, hy12, fun h0 => (hyr h0).2.1, hyh,
      fun h0 => ⟨(hyr h0).2.2.2.2, (hya (by omega)).1.symm, (hyop (by omega)).1, (hyop (by omega)).2⟩⟩,
     ⟨hz40, hzl, hzo, fun h0 => ⟨(hzw h0).2, (hza (by omega)).1.symm, (hzop (by omega)).1, (hzop (by omega)).2⟩,
      ?_, ?_⟩, hlen⟩,
    ⟨hst0, hsok, hstw, hstg, hsta, hfg, hfw, hsf, hswb, hfh, hsgA, hfgA⟩, ⟨hH, hcost⟩, hinv⟩
  · by_cases hz0 : 0 < zc
    · by_cases hx0 : 0 < xl
      · by_cases he : zp = x
        · exact Or.inl ⟨he, hzxc he hz0 hx0⟩
        · rcases hzx with h1 | h1
          · exact absurd h1 he
          · exact Or.inr h1
      · exact Or.inr fun _ h1 => absurd h1 hx0
    · exact Or.inr fun h1 => absurd h1 hz0
  · by_cases hz0 : 0 < zc
    · by_cases hy0 : 0 < yl
      · by_cases he : zp = y
        · exact Or.inl ⟨he, hzyc he hz0 hy0⟩
        · rcases hzy with h1 | h1
          · exact absurd h1 he
          · exact Or.inr h1
      · exact Or.inr fun _ h1 => absurd h1 hy0
    · exact Or.inr fun h1 => absurd h1 hz0

/-- **`nat.mul`** (arm64) in the empty-tolerant Q-form premise `MulHypGQ`, window `mulWX`, `above = 88`, cost `mulCQ` -/
theorem mulGQ (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2) :
    MulHypGQ impl R NatMul.names mulWX 88 mulCQ := fun H b L z zl zc st x xl xc y yl yc =>
  (Q.NatMul.ens impl hap R hmk hgr hmc hmv hwb H b L mulWX z zl zc st x xl xc y yl yc).mono_ret
    (fun _ ⟨h1, h2, h3, h4, h5⟩ => x_preMQ h1 h2 h3 h4 h5) (fun _ _ _ _ hq => Q.NatMul.q_post hq)

end FvModexp.Arm64.Q.ExpSlow
