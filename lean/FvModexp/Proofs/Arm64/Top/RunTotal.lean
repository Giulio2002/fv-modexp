import FvModexp.Proofs.Arm64.Top.RunSucc
import FvModexp.Proofs.Arm64.Top.RunErr
import FvModexp.Proofs.Arm64.Top.RunGate

set_option autoImplicit false

/-!
# Row 1, arm64: `(*bigModExp).Run` on EVERY input slice, one theorem (agent asm s77, REDTEAM-arm64 R4)

`correctness_total`: the BRIEF row-1 sentence as one kernel-checked statement. Under the success row's environment
(`RunSucc.correctness`'s premises and precondition, minus `LengthsPass`), with the budget demanded only when the lengths
pass (`LengthsPass data → okBudget (parseLengths data) ≤ b`; failing headers can be up to `2^256` and would otherwise
demand an absurd budget) plus the error path's 512 bytes, `Run` returns, for every input:
* `LengthsPass data` and `(out, nil)` with `out = compute data (parseLengths data)` (`OkRet`, `FrameW`), or
* `LengthsFail data` and `(nil, err)`, `err ≠ nil` (`ErrRet`, `Frame`).
Proof: `by_cases` on `LengthsPass`; the failing case weakens the success environment to `Run.correctness`'s
(`EnvW … W → Env …` for `W ≥ 4800`: guard, stack, window facts on the sub-window; `OkReqs → ErrReqs`' requests).
A corollary of the two row theorems (not a separate Janus row); its precondition is satisfiable: `total_nonvacuous`
(the success witness `RunSucc.Witness.nonvacuous` meets it).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool
open FvModexp FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run

/-- the success environment (window `W ≥ 4800`) contains the error path's (window 4800) -/
theorem env_of_envW {R : RtInv} {L : List (Nat × Nat)} {s : State} {W : Nat} (hW : 4800 ≤ W)
    (h : RunArm64.EnvW R L s W) : RunArm64.Env R L s := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hs1, hs2, hs3, hs4⟩, hdl, hor, hap, hgo, hls, hdo⟩, _⟩ := h
  refine ⟨⟨hg1, hg2, by omega⟩, ⟨hs1, by omega, hs3, Memory.accessible_mono _ hs4 (by omega) (by omega)⟩, hdl,
    Outside.of_sub hor (by omega) (by omega), by unfold Apart at hap ⊢; omega, hgo, ?_, hdo⟩
  intro r hr
  obtain ⟨h1, -⟩ := hls r hr
  exact ⟨by omega, trivial⟩

/-- the success path's runtime service covers the error path's requests -/
theorem errReqs_of_okReqs {R : RtInv} {b : Nat} {len : BitVec 64} (h : RunArm64.OkReqs R)
    (hb : 3 * RunArm64.blockBound 64 + RunArm64.blockBound 16 ≤ b) : RunArm64.ErrReqs R b len :=
  ⟨h.1 _ 4 8 (by decide), fun _ d sr n hn => h.2.1 d sr n (by omega), h.2.2.2.2.1 _, hb⟩

/-- **Row 1, arm64, every input**: `Run` returns `(compute data (parseLengths data), nil)` when the lengths pass
EIP-7823 and `(nil, err)` with `err ≠ nil` when they fail. -/
theorem correctness_total (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmkz : MakesliceZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (S : PoolShape)
    (hget : PoolGetLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      WitSitesArm64.stkT S)
    (hput : PoolPutLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      WitSitesArm64.stkT S)
    (hwb4 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4)
    (W : Nat) (hW : 624 + 72944 ≤ W) (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp]
      (fun s => S = StkShape ∧ RunArm64.EnvW R L s W ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.OkReqs R ∧
        RunArm64.Globals R s.mem (RunArm64.windowW s W) ∧ RunArm64.NatOne R s.mem (RunArm64.windowW s W) ∧
        RunArm64.StackPool R s.mem (RunArm64.windowW s W) ∧
        (LengthsPass (bytesAt s.mem p.toNat len.toNat) →
          RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b) ∧
        3 * RunArm64.blockBound 64 + RunArm64.blockBound 16 ≤ b)
      (fun s s' =>
        (LengthsPass (bytesAt s.mem p.toNat len.toNat) ∧ RunArm64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
          RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') ∨
        (LengthsFail (bytesAt s.mem p.toNat len.toNat) ∧ RunArm64.ErrRet s' ∧
          RunArm64.Frame R b (3 * RunArm64.blockBound 64 + RunArm64.blockBound 16) L s s')) := by
  intro ret hret s hs ⟨hS, hE, hI, hO, hinv, hR, hG, hN, hP, hB, hB0⟩
  by_cases hL : LengthsPass (bytesAt s.mem p.toNat len.toNat)
  · exact (RunSucc.correctness impl hap R hmk hmkz hmv hmz hno hgr hmc hwb S hget hput hwb4 W hW b L c p len cp
      ret hret s hs ⟨hS, hE, hI, hO, hinv, hR, hG, hN, hP, hB hL, hL⟩).mono
      fun _ ⟨ha, h1, h2⟩ => ⟨ha, Or.inl ⟨hL, h1, h2⟩⟩
  · exact (correctness impl hap R hmk hmv hno b L c p len cp ret hret s hs
      ⟨env_of_envW (by omega) hE, hI, hO, hinv, errReqs_of_okReqs hR hB0, hL⟩).mono
      fun _ ⟨ha, h1, h2⟩ => ⟨ha, Or.inr ⟨hL, h1, h2⟩⟩

end FvModexp.Arm64.Run

namespace FvModexp.Arm64.Run.TotalWitness

set_option maxRecDepth 100000

/-- `correctness_total` is not vacuous: every premise and every precondition conjunct hold together and the call
returns (the success witness `RunSucc.Witness.nonvacuous`: `3^5 mod 7`, output `[5]`; its budget covers the error
path's 512 bytes by `RunGate.errBudget_le_okBudget`). -/
theorem total_nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (c p len cp : BitVec 64) (ret : Nat) (s : State) (W : Nat),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MakesliceZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    GrowsliceLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    PoolGetLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R
      WitSitesArm64.stkT StkShape ∧
    PoolPutLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R
      WitSitesArm64.stkT StkShape ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4 ∧
    624 + 72944 ≤ W ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp] s ∧
    (StkShape = StkShape ∧ RunArm64.EnvW R L s W ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.OkReqs R ∧
        RunArm64.Globals R s.mem (RunArm64.windowW s W) ∧ RunArm64.NatOne R s.mem (RunArm64.windowW s W) ∧
        RunArm64.StackPool R s.mem (RunArm64.windowW s W) ∧
        (LengthsPass (bytesAt s.mem p.toNat len.toNat) →
          RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b) ∧
        3 * RunArm64.blockBound 64 + RunArm64.blockBound 16 ≤ b) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧
        ((LengthsPass (bytesAt s.mem p.toNat len.toNat) ∧ RunArm64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
          RunArm64.FrameW R b (RunArm64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') ∨
        (LengthsFail (bytesAt s.mem p.toNat len.toNat) ∧ RunArm64.ErrRet s' ∧
          RunArm64.Frame R b (3 * RunArm64.blockBound 64 + RunArm64.blockBound 16) L s s')) := by
  obtain ⟨impl, R, b, L, c, p, len, cp, ret, s, W, hap, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hW, hret, hs,
    hSS, hE, hI, hO, hinv, hR, hG, hN, hP, hB, hL, -, -, -, -, -, -, -, -, -, -, -, -, hRet⟩ :=
    RunSucc.Witness.nonvacuous
  exact ⟨impl, R, b, L, c, p, len, cp, ret, s, W, hap, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hW, hret, hs,
    ⟨hSS, hE, hI, hO, hinv, hR, hG, hN, hP, fun _ => hB,
      Nat.le_trans (RunGate.errBudget_le_okBudget _) hB⟩,
    hRet.mono fun _ ⟨ha, h1, h2⟩ => ⟨ha, Or.inl ⟨hL, h1, h2⟩⟩⟩

end FvModexp.Arm64.Run.TotalWitness
