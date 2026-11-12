import FvModexp.Proofs.Amd64.Top.RunOk
import FvModexp.Proofs.Amd64.Top.RunErrLib
import FvModexp.Proofs.Common.ComputeBridge

set_option autoImplicit false

/-!
# Row 1, amd64, success path: the library-program theorem behind `Run.correctness_ok` (twin of the arm64 `RunOkLib`)

`ensOkLib`: for every input slice whose length headers pass `checkLengths (parseLengths data)` (EthLib), with the
Osaka receiver, `Run` returns `(out, nil)` with `out = compute data (parseLengths data)`, keeping the Go ABI and the
memory frame (window `W`). Stated with `FvModexp.Spec.RunAmd64` (`EnvW`, `Input`, `OkReqs`, `Globals`, `okBudget`,
`OkRet`, `FrameW`); the big-number callees enter as their interface specs (`RunIface.ModSpec`/`ExpSpec`/`BytesSpec`)
until their machine-code proofs land, the runtime as live contracts.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Amd64.Run

/-- The success budget in Spec terms is the proof-side `okB`. -/
theorem okB_spec (s : State) (p len : BitVec 64) :
    RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) = okB s p len := by
  obtain ⟨e0, e1, e2⟩ := parse_hdr s p len
  simp only [RunAmd64.okBudget, e0, e1, e2, okB, callB, dCost, makeCost, makeCap, RunIface.ModBudget,
    RunIface.ExpBudget, RunIface.BytesBudget, RunIface.opCost, RunIface.maxW, wMax, opW, allocCost,
    RunAmd64.blockBound]
  rfl

theorem pass_hdr {s : State} {p len : BitVec 64} (h : LengthsPass (bytesAt s.mem p.toNat len.toNat)) :
    hdrV s p len 0 ≤ 1024 ∧ hdrV s p len 1 ≤ 1024 ∧ hdrV s p len 2 ≤ 1024 := by
  obtain ⟨e0, e1, e2⟩ := parse_hdr s p len
  rw [lengthsPass_iff, e0, e1, e2] at h
  exact h

/-- The returned bytes are EthLib's `compute`. -/
theorem okRet_spec {s S' : State} {p len : BitVec 64} (h : OkRet S' (resV s p len) (hdrV s p len 2)) :
    RunAmd64.OkRet (bytesAt s.mem p.toNat len.toNat) S' := by
  obtain ⟨h7, h3, hv⟩ := h
  refine ⟨h7, ?_⟩
  obtain ⟨e0, e1, e2⟩ := parse_hdr s p len
  rw [compute_eq, bytesAt_eq_natToBytes, h3, hv]
  simp only [e0, e1, e2, resV, opV, opStart, opLen, show ((2 : Nat) = 0) = False by decide,
    show ((2 : Nat) = 1) = False by decide, show ((1 : Nat) = 0) = False by decide, if_false, if_true, Nat.add_assoc]

set_option maxRecDepth 20000 in
/-- **Success path of `Run` (amd64), library program.** -/
theorem ensOkLib (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hmz : MemmoveZeroLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (stkM aboveM : Nat) (hM : RunIface.ModSpec impl R stkM aboveM) (hE : RunIface.ExpSpec impl R stkM aboveM)
    (hBy : RunIface.BytesSpec impl R stkM aboveM)
    (W : Nat) (hW : 616 + stkM ≤ W) (hW1 : 4800 ≤ W) (hab : aboveM ≤ 144) (ha8 : 8 ≤ aboveM)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (LibRun.program.link impl) (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp]
      (fun s => RunAmd64.EnvW R L s W ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.OkReqs R ∧
        RunAmd64.Globals R s.mem (RunAmd64.windowW s W) ∧ RunAmd64.NatOne R s.mem (RunAmd64.windowW s W) ∧
        RunAmd64.StackPool R s.mem (RunAmd64.windowW s W) ∧
        RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat)) ≤ b ∧
        LengthsPass (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunAmd64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
        RunAmd64.FrameW R b (RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s') := by
  intro ret hret s hs ⟨⟨henvW, hgL, hfL⟩, hin, hrecv, hinv, hsv, hglob, hone, hpool, hbud, hpass⟩
  rw [okB_spec] at hbud
  obtain ⟨n, o, hrun, hQ⟩ := okReach impl hap R hmk hmv hmz hno stkM aboveM hM hE hBy hsv b L c p len cp ret hret s hs
    W henvW hW hW1 hab ha8 hin hinv (osaka_read hrecv) hglob hgL hfL hbud hone hpool (pass_hdr hpass)
    (fun o => ∃ s', o = .returned s' ∧ ABIReturn s s' ∧ RunAmd64.OkRet (bytesAt s.mem p.toNat len.toNat) s' ∧
      RunAmd64.FrameW R b (RunAmd64.okBudget (parseLengths (bytesAt s.mem p.toNat len.toNat))) L W s s')
    (fun S' habi hret' hfr => ⟨S', rfl, habi, okRet_spec hret', by
      obtain ⟨hfs, hdf, L', b', hext, hb', hinv', hheld, hMF, hLF⟩ := hfr
      exact ⟨hfs, hdf, L', b', hext, by rw [okB_spec]; exact hb', hinv', by rw [hret'.2.1]; exact hheld, hMF, hLF⟩⟩)
  obtain ⟨s', rfl, h⟩ := hQ
  exact ⟨n, s', hrun, h⟩

end FvModexp.Amd64.Run
