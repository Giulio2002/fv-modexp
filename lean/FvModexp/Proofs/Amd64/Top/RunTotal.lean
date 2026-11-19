import FvModexp.Proofs.Amd64.Top.RunSucc
import FvModexp.Proofs.Amd64.Top.RunErr
import FvModexp.Proofs.Amd64.Top.RunGate

set_option autoImplicit false

/-!
# Row 1, amd64: `(*bigModExp).Run` on EVERY input slice, one theorem (agent asm s82, REDTEAM-amd64; twin of Arm64/Top/RunTotal)

`correctness_total`: the BRIEF row-1 sentence as one kernel-checked statement. Under the success row's environment
(`RunSucc.correctness`'s premises and precondition, minus `LengthsPass`), with the budget demanded only when the lengths
pass (`LengthsPass data → okBudget (parseLengths data) ≤ b`; failing headers can be up to `2^256` and would otherwise
demand an absurd budget) plus the error path's 512 bytes, `Run` returns, for every input:
* `LengthsPass data` and `(out, nil)` with `out = compute data (parseLengths data)` (`OkRet`, `FrameW`), or
* `LengthsFail data` and `(nil, err)`, `err ≠ nil` (`ErrRet`, `Frame`).
Proof: `by_cases` on `LengthsPass`; the failing case weakens the success environment to `Run.correctness`'s
(`EnvW … W → Env …` for `W ≥ 4800`: guard, stack, window facts on the sub-window; `OkReqs → ErrReqs`' requests).
Witness `Witness.correctness_total` (Janus pairs `Witness.<X>` with the main `<X>`): the success witness
`RunSucc.Witness.nonvacuous` meets it.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool
open FvModexp FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Amd64.Run

/-- the success environment (window `W ≥ 4800`) contains the error path's (window 4800) -/
theorem env_of_envW {R : RtInv} {L : List (Nat × Nat)} {s : State} {W : Nat} (hW : 4800 ≤ W)
    (h : RunAmd64.EnvW R L s W) : RunAmd64.Env R L s := by
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hs1, hs2, hs3⟩, h8, hdl, hor, hap, hgo, hls, hdo, ⟨htl, htlo, htla⟩⟩, _⟩ := h
  refine ⟨⟨hg1, hg2, by omega⟩, ⟨by omega, hs2, Janus.Arm64.Memory.accessible_mono _ hs3 (by omega) (by omega)⟩, h8, hdl,
    Outside.of_sub hor (by omega) (by omega), by unfold Apart at hap ⊢; omega, hgo, ?_, hdo,
    ⟨htl, htlo, by unfold Apart at htla ⊢; omega⟩⟩
  intro r hr
  obtain ⟨h1, -⟩ := hls r hr
  exact ⟨by omega, trivial⟩

/-- the success path's runtime service covers the error path's requests -/
theorem errReqs_of_okReqs {R : RtInv} {b : Nat} {len : BitVec 64} (h : RunAmd64.OkReqs R)
    (hb : 3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16 ≤ b) : RunAmd64.ErrReqs R b len :=
  ⟨h.1 _ 4 8 (by decide), fun _ d sr n hn => h.2.1 d sr n (by omega), h.2.2.2.2.1 _, hb⟩

/-- **Row 1, amd64, every input**: `Run` returns `(compute data (parseLengths data), nil)` when the lengths pass
EIP-7823 and `(nil, err)` with `err ≠ nil` when they fail. -/
theorem correctness_total (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmkz : MakesliceZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
      4096 R 2)
    (S : PoolShape)
    (hget : Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R WitSitesAmd64.stkT S)
    (hput : Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R WitSitesAmd64.stkT S)
    (hwb4 : WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4")
      4096 R 4)
    (W : Nat) (hW : 616 + 43736 ≤ W)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp]
      (fun s => S = StkShape ∧ RunAmd64.EnvW R L s W ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.OkReqs R ∧
        RunAmd64.Globals R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.NatOne R s.mem (RunAmd64.windowW s W) ∧
        RunAmd64.StackPool R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.CpuOne s.mem ∧
        (LengthsPass (bytesAt s.mem p.toNat len.toNat) →
          RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b) ∧
        3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16 ≤ b)
      (fun s s' =>
        (LengthsPass (bytesAt s.mem p.toNat len.toNat) ∧ RunAmd64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
          RunAmd64.FrameW R b (RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') ∨
        (LengthsFail (bytesAt s.mem p.toNat len.toNat) ∧ RunAmd64.ErrRet s' ∧
          RunAmd64.Frame R b (3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16) L s s')) := by
  janus64_ensures_old [FvModexp.Spec.RunAmd64.EnvW, FvModexp.Spec.RunAmd64.Input, FvModexp.Spec.OsakaReceiver, FvModexp.Spec.RunAmd64.Globals, FvModexp.Spec.RunAmd64.windowW, FvModexp.Spec.RunAmd64.NatOne, FvModexp.Spec.RunAmd64.StackPool, FvModexp.Spec.RunAmd64.CpuOne, FvModexp.Spec.bytesAt, FvModexp.Spec.RunAmd64.window, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.RunIface.wbA, FvModexp.Mdl.karatsubaThreshold, FvModexp.Mdl.basicSqrThreshold, FvModexp.Mdl.karatsubaSqrThreshold, FvModexp.Amd64.IExp.pA, Janus.Spec.Pool.newOffset, FvModexp.Amd64.MontHyp.hasADX, FvModexp.Spec.byteOf]
  intro ret hret s hs ⟨hS, hE, hI, hO, hinv, hR, hG, hN, hP, hC, hB, hB0⟩
  by_cases hL : LengthsPass (bytesAt s.mem p.toNat len.toNat)
  · exact ((RunSucc.correctness impl hap R hmk hmkz hmv hmz hno hgr hmc hwb S hget hput hwb4 W hW b L c p len cp).toOld
      ret hret s hs ⟨hS, hE, hI, hO, hinv, hR, hG, hN, hP, hC, hB hL, hL⟩).mono
      fun _ ⟨ha, h1, h2⟩ => ⟨ha, Or.inl ⟨hL, h1, h2⟩⟩
  · exact ((correctness impl hap R hmk hmv hno b L c p len cp).toOld ret hret s hs
      ⟨env_of_envW (by omega) hE, hI, hO, hinv, errReqs_of_okReqs hR hB0, hL⟩).mono
      fun _ ⟨ha, h1, h2⟩ => ⟨ha, Or.inr ⟨hL, h1, h2⟩⟩

end FvModexp.Amd64.Run

namespace FvModexp.Amd64.Run.Witness

set_option maxRecDepth 100000

/-- `Run.correctness_total` is not vacuous: every premise and every precondition conjunct hold together and the call
returns, with one call-site state per contract (the success witness `RunSucc.Witness.nonvacuous`: `3^5 mod 7`, output
`[5]`; its budget covers the error path's 512 bytes by `RunGate.errBudget_le_okBudget`). -/
theorem correctness_total : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (c p len cp : BitVec 64) (ret : Nat) (s : State) (W : Nat),
    ImplApart Extracted.program impl ∧
    MakesliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MakesliceZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.makeslice") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    MemmoveZeroLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.PoolAmd64.PoolGetLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Get") 4096 R WitSitesAmd64.stkT StkShape ∧
    Janus.Contracts.PoolAmd64.PoolPutLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "sync.(*Pool).Put") 4096 R WitSitesAmd64.stkT StkShape ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4096 R 4 ∧
    616 + 43736 ≤ W ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup0 (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp] s ∧
    (StkShape = StkShape ∧ RunAmd64.EnvW R L s W ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
      R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.OkReqs R ∧
      RunAmd64.Globals R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.NatOne R s.mem (RunAmd64.windowW s W) ∧
      RunAmd64.StackPool R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.CpuOne s.mem ∧
      (LengthsPass (bytesAt s.mem p.toNat len.toNat) →
        RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b) ∧
      3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16 ≤ b) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      WitSitesAmd64.mkSite R (Extracted.program.contractAddr "runtime.makeslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧
      ((MakeslicePre64 4096 s_c ∧ StackRoom64 s_c 4096 3 ∧
        LiveAt R (Extracted.program.contractAddr "runtime.makeslice") [(s_c.regs 0).toNat, (s_c.regs 3).toNat,
          (s_c.regs 1).toNat] L b 0 (s_c.regs 14).toNat s_c.mem (liveWin64 s_c 4096 3)) ∧
        typSize s_c.mem (s_c.regs 0).toNat * (s_c.regs 1).toNat = 0 ∧
        Outside (s_c.regs 0).toNat 16 (calleeStack64 s_c 4096 3))) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      WitSitesAmd64.mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      ((s_c.regs 1).toNat = 0 ∧ MemPre64 4096 3 s_c ∧
        LiveMemAt64 R (Extracted.program.contractAddr "runtime.memmove") [(s_c.regs 0).toNat, (s_c.regs 3).toNat,
          (s_c.regs 1).toNat] L b s_c (liveWin64 s_c 4096 3))) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      WitSitesAmd64.noSite R (Extracted.program.contractAddr "runtime.newobject") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧
      WitSitesAmd64.grSite R (Extracted.program.contractAddr "runtime.growslice") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      WitSitesAmd64.clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      WitSitesAmd64.wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 2 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Get") ∧
      WitSitesAmd64.getSite R (Extracted.program.contractAddr "sync.(*Pool).Get") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "sync.(*Pool).Put") ∧
      WitSitesAmd64.putSite R (Extracted.program.contractAddr "sync.(*Pool).Put") L b rs s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier4") ∧
      WitSitesAmd64.wbSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier4") 4 L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (s.setRet ret) fun s' =>
      ABIReturn (s.setRet ret) s' ∧
        ((LengthsPass (bytesAt (s.setRet ret).mem p.toNat len.toNat) ∧ RunAmd64.OkRet (bytesAt (s.setRet ret).mem p.toNat len.toNat) s' ∧
          RunAmd64.FrameW R b (RunAmd64.okBudget (parseLengths (bytesAt (s.setRet ret).mem p.toNat len.toNat))) L W (s.setRet ret) s') ∨
        (LengthsFail (bytesAt (s.setRet ret).mem p.toNat len.toNat) ∧ RunAmd64.ErrRet s' ∧
          RunAmd64.Frame R b (3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16) L (s.setRet ret) s')) := by
  obtain ⟨impl, R, b, L, c, p, len, cp, ret, s, W, hap, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hW, hret, hs,
    hSS, hE, hI, hO, hinv, hR, hG, hN, hP, hC, hB, hL, -,
    x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, hRet⟩ :=
    RunSucc.Witness.nonvacuous
  exact ⟨impl, R, b, L, c, p, len, cp, ret, s, W, hap, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hW, hret, hs,
    ⟨hSS, hE, hI, hO, hinv, hR, hG, hN, hP, hC, fun _ => hB,
      Nat.le_trans (RunGate.errBudget_le_okBudget _) hB⟩,
    x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11,
    hRet.mono fun _ ⟨ha, h1, h2⟩ => ⟨ha, Or.inl ⟨hL, h1, h2⟩⟩⟩

end FvModexp.Amd64.Run.Witness
