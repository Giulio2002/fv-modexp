import FvModexp.Proofs.Arm64.Top.RunPre
import FvModexp.Spec.RunArm64
import FvModexp.Proofs.Arm64.Nat.RowLink

/-!
# Row 1, arm64, error path: the library-program theorem behind `Run.correctness`

`correctness`: for every input slice whose length headers fail `checkLengths (parseLengths data)` (EthLib), with the
Osaka receiver, `Run` returns a nil `[]byte` and a non-nil `error`, keeping the Go ABI and the memory frame. The
statement uses only `FvModexp.Spec.*` (the call environment, input, requests and frame of `Spec.RunArm64`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Arm64.Run

/-- The three length headers are the `hdrV` values. -/
theorem parse_hdr (s : State) (p len : BitVec 64) :
    (parseLengths (bytesAt s.mem p.toNat len.toNat)).base = hdrV s p len 0 ∧
    (parseLengths (bytesAt s.mem p.toNat len.toNat)).exponent = hdrV s p len 1 ∧
    (parseLengths (bytesAt s.mem p.toNat len.toNat)).modulus = hdrV s p len 2 := by
  simp only [parseLengths, readNat_eq_padBE, hdrV, LENGTH_HEADER_BYTES]
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem fail_hdr {s : State} {p len : BitVec 64} (h : LengthsFail (bytesAt s.mem p.toNat len.toNat)) :
    ¬(hdrV s p len 0 ≤ 1024 ∧ hdrV s p len 1 ≤ 1024 ∧ hdrV s p len 2 ≤ 1024) := by
  intro ⟨h0, h1, h2⟩
  apply h
  obtain ⟨e0, e1, e2⟩ := parse_hdr s p len
  rw [lengthsPass_iff, e0, e1, e2]
  exact ⟨h0, h1, h2⟩

theorem osaka_read {m : Memory} {c : Nat} (h : OsakaReceiver m c) : m.readLE c 3 = 65793 := by
  obtain ⟨h0, h1, h2⟩ := h
  have e1 := Memory.readLE_add m c 1 2
  have e2 := Memory.readLE_add m (c + 1) 1 1
  rw [Memory.readLE_one] at e1 e2
  rw [Memory.readLE_one] at e2
  rw [e1, e2, h0, h1, show c + 1 + 1 = c + 2 by omega, h2]

theorem frame_spec {R : RtInv} {b B B' : Nat} {L : List (Nat × Nat)} {s s' : State} (hB : B = B')
    (h : RunFrame R b B L s s') : RunArm64.Frame R b B' L s s' := by
  subst hB; exact h

set_option maxRecDepth 20000 in
theorem ensErrLib (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (LibRun.program.link impl) (segAddr Extracted.program RunArm64.fn) [c, p, len, cp]
      (fun s => RunArm64.Env R L s ∧ RunArm64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧ RunArm64.ErrReqs R b len ∧
        LengthsFail (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunArm64.ErrRet s' ∧ RunArm64.Frame R b (3 * RunArm64.blockBound 64 + RunArm64.blockBound 16) L s s') := by
  janus_ensures_old [FvModexp.Spec.RunArm64.Env, FvModexp.Spec.RunArm64.Input, FvModexp.Spec.OsakaReceiver, FvModexp.Spec.RunArm64.ErrReqs, FvModexp.Spec.bytesAt, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Spec.RunArm64.window, FvModexp.Spec.RunArm64.wordT, FvModexp.Arm64.Run.errT, FvModexp.Spec.byteOf]
  intro ret hret s hs ⟨henv, hin, hrecv, hinv, ⟨hok, hokm, hokn, hcost⟩, hfail⟩
  have hfail' := fail_hdr hfail
  have hcm : makeCost 4 = RunArm64.blockBound 64 := rfl
  have hca : allocCost 16 = RunArm64.blockBound 16 := rfl
  have hokr : HdrOkR R b len := ⟨hok, by rw [hcm]; omega, hokm⟩
  obtain ⟨n, o, hrun, hQ⟩ := runPre impl hap R hmk hmv hno b L c p len cp ret hret s hs henv hin hinv hokr
    (osaka_read hrecv) hokn (by rw [hcm, hca]; exact hcost)
    (fun o => ∃ s', o = .returned s' ∧ ABIReturn s s' ∧ RunArm64.ErrRet s' ∧
      RunArm64.Frame R b (3 * RunArm64.blockBound 64 + RunArm64.blockBound 16) L s s')
    (fun S' _ habi herr hfr => ⟨S', rfl, habi, herr, frame_spec (by rw [hcm, hca]) hfr⟩)
    (fun S' h0 h1 h2 _ _ _ _ => absurd ⟨by omega, h1, by omega⟩ hfail')
    (fun _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 _ _ _ _ _ _ _ => absurd ⟨h0, h1, h2⟩ hfail')
  obtain ⟨s', rfl, h⟩ := hQ
  exact ⟨n, s', hrun, h⟩

end FvModexp.Arm64.Run
