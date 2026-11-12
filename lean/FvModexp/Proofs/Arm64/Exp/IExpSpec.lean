import FvModexp.Proofs.Arm64.Exp.IExpFun

set_option autoImplicit false

/-!
# `(*Int).exp` (arm64) in the final `RunIface.ExpSpec` form

`ExpSpecX.toSpec`: top's final `ExpSpec` pre (… `PoolG` ∧ `mm ≠ 0` ∧ `Apart z 32 wbA 4`, `IntOK`'s cap conjunct) gives
`ExpX`; the post's extra cap conjunct is dropped (it is inside `IntPost`'s `IntOK`). `ensS` = `IExp.ens` in that form.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.IExp

theorem ExpSpecX.toSpec {impl : List Segment} {R : RtInv} {stk above : Nat} (h : ExpSpecX impl R stk above) :
    RunIface.ExpSpec impl R stk above := by
  intro b L z y mm
  refine (h b L z y mm).mono (fun s hp => ?_) (fun _ _ _ hq => ⟨hq.1, hq.2.1⟩)
  obtain ⟨hIP, hm, h1, h2, h3, hone, hpg, hmm, hwb⟩ := hp
  have hc : ∀ a ∈ [z.toNat, y.toNat, mm.toNat], s.mem.readLE (a + 24) 8 < 2 ^ 40 := fun a ha =>
    (hIP.2.2.2.2.2.1 a ha).1.2.2.2.2.2.2.2.2.2
  exact ⟨hIP, hm, h1, h2, h3, hone, hpg, hc _ (by simp), hc _ (by simp), hc _ (by simp), hmm, hwb⟩

end FvModexp.Arm64.IExp
