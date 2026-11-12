import FvModexp.Proofs.Arm64.Exp.IExpFun

set_option autoImplicit false

/-!
# `(*Int).exp` (arm64) in the final `RunIface.ExpSpec` form (+ `ModX`)

`ExpSpecM` = `RunIface.ExpSpec` with ONE more (last) pre conjunct `RunIface.ModX s.mem z` (`z`'s array apart from the
threshold globals `gA`; batch "[expmc s40] ANNOUNCE" item 5: `x = z.abs` is the `x` of `expNNSlow`'s `zz.mul(stk, z, x)`,
whose operands must be apart from `gA` — the same fact `ModSpec` carries for `(*Int).Mod`). top folds it into
`RunIface.ExpSpec` (then `ExpSpecM` is that text). `ExpSpecX.toSpecM`: top's final `ExpSpec` pre (… `PoolG` ∧
`mm ≠ 0` ∧ `Apart z 32 wbA 4`, `IntOK`'s cap conjunct) + `ModX` gives `ExpX`; the post's extra cap conjunct is dropped
(it is inside `IntPost`'s `IntOK`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.IExp

open FvModexp.Arm64.RunIface (IntPre IntPost IntV IntLenLe OneG maxW ExpBudget lenW namesExp)

/-- `RunIface.ExpSpec` + `ModX` of `z` as the last pre conjunct (see the module doc) -/
def ExpSpecM (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64),
    Ensures ((Extracted.program.onlySegments namesExp).link impl) (segAddr Extracted.program (RunIface.P ++ "(*Int).exp"))
      [z, z, y, mm, 0#64]
      (fun s => IntPre R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat)) (lenW s.mem y.toNat))
        L stk above [z.toNat, y.toNat, mm.toNat] s ∧ 0 < IntV s.mem mm.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ IntLenLe s.mem mm.toNat maxW ∧
        OneG R L s.mem (win s stk above) [z.toNat, y.toNat, mm.toNat] ∧
        RunIface.PoolG R s.mem (win s stk above) ∧ mm.toNat ≠ 0 ∧ Apart z.toNat 32 RunIface.wbA 4 ∧ RunIface.ModX s.mem z.toNat)
      (fun s s' => s'.regs 0 = z ∧
        IntPost R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat)) (lenW s.mem y.toNat))
          L stk above z.toNat (IntV s.mem z.toNat ^ IntV s.mem y.toNat % IntV s.mem mm.toNat) s s')

theorem ExpSpecX.toSpecM {impl : List Segment} {R : RtInv} {stk above : Nat} (h : ExpSpecX impl R stk above) :
    ExpSpecM impl R stk above := by
  intro b L z y mm
  refine (h b L z y mm).mono (fun s hp => ?_) (fun _ _ _ hq => ⟨hq.1, hq.2.1⟩)
  obtain ⟨hIP, hm, h1, h2, h3, hone, hpg, hmm, hwb, hmx⟩ := hp
  have hc : ∀ a ∈ [z.toNat, y.toNat, mm.toNat], s.mem.readLE (a + 24) 8 < 2 ^ 40 := fun a ha =>
    (hIP.2.2.2.2.2.1 a ha).1.2.2.2.2.2.2.2.2.2
  exact ⟨hIP, hm, h1, h2, h3, hone, hpg, hc _ (by simp), hc _ (by simp), hc _ (by simp), hmm, hwb, hmx⟩

end FvModexp.Arm64.IExp
