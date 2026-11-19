import FvModexp.Proofs.Amd64.Top.RunPre
import FvModexp.Spec.RunAmd64
import FvModexp.Proofs.Amd64.Nat.RowLink

/-!
# Row 1, amd64, error path: the library-program theorem behind `Run.correctness` (twin of the arm64 `RunErrLib`)

`ensErrLib`: for every input slice whose length headers fail `checkLengths (parseLengths data)` (EthLib), with the
Osaka receiver, `Run` returns a nil `[]byte` and a non-nil `error`, keeping the Go ABI and the memory frame. The
statement uses only `FvModexp.Spec.*` (the call environment, input, requests and frame of `Spec.RunAmd64`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Spec EthLib.Execution.Evm.Precompiles.Modexp

namespace FvModexp.Amd64.Run

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

theorem osaka_read {m : Janus.Arm64.Memory} {c : Nat} (h : OsakaReceiver m c) : m.readLE c 3 = 65793 := by
  obtain ⟨h0, h1, h2⟩ := h
  have e1 := Janus.Arm64.Memory.readLE_add m c 1 2
  have e2 := Janus.Arm64.Memory.readLE_add m (c + 1) 1 1
  rw [Janus.Arm64.Memory.readLE_one] at e1 e2
  rw [Janus.Arm64.Memory.readLE_one] at e2
  rw [e1, e2, h0, h1, show c + 1 + 1 = c + 2 by omega, h2]

theorem frame_spec {R : RtInv} {b B B' : Nat} {L : List (Nat × Nat)} {s s' : State} (hB : B = B')
    (h : RunFrame R b B L s s') : RunAmd64.Frame R b B' L s s' := by
  subst hB; exact h

/-- The call data read from memory is unchanged by installing the return address when it is empty or apart from the return slot `[RSP, RSP + 8)`
(`RunAmd64.Input` keeps `[p, p + len)` outside the stack window, which contains the slot, but says nothing about a zero-length slice: the
empty case is a separate disjunct). The conditional rewrite `janus64_pre_setRet` needs for the `LengthsFail (bytesAt s.mem p len)` conjunct. -/
theorem bytesAt_setRet {s : State} {ret p n : Nat}
    (h : n = 0 ∨ p + n ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ p) :
    bytesAt (s.setRet ret).mem p n = bytesAt s.mem p n := by
  rcases h with h | h
  · subst h; rfl
  · unfold bytesAt
    have hl : (List.range n).map (fun i => byteOf (s.setRet ret).mem (p + i)) =
        (List.range n).map (fun i => byteOf s.mem (p + i)) := by
      apply List.map_congr_left
      intro i hi
      have hi' : i < n := List.mem_range.1 hi
      have hb : (s.setRet ret).mem.bytes (p + i) = s.mem.bytes (p + i) :=
        Janus.Amd64.GoABI.bytes_setRet_of_outside (by omega)
      unfold byteOf
      rw [hb]
    rw [hl]

set_option maxRecDepth 20000 in
theorem ensErrLib (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hno : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (c p len cp : BitVec 64) :
    Ensures (LibRun.program.link impl) (segAddr Extracted.program RunAmd64.fn) [c, p, len, cp]
      (fun s => RunAmd64.Env R L s ∧ RunAmd64.Input R L c p len cp s ∧ OsakaReceiver s.mem c.toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ RunAmd64.ErrReqs R b len ∧
        LengthsFail (bytesAt s.mem p.toNat len.toNat))
      (fun s s' => RunAmd64.ErrRet s' ∧ RunAmd64.Frame R b (3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16) L s s') := by
  refine Ensures.of_old (by janus64_pre_setRet [FvModexp.Spec.RunAmd64.Env, FvModexp.Spec.RunAmd64.Input, FvModexp.Spec.OsakaReceiver, FvModexp.Spec.RunAmd64.ErrReqs, FvModexp.Amd64.Run.bytesAt_setRet, FvModexp.Spec.RunAmd64.window, FvModexp.Spec.RunAmd64.wordT, FvModexp.Amd64.Run.errT]) ?_
  intro ret hret s hs ⟨henv, hin, hrecv, hinv, ⟨hok, hokm, hokn, hcost⟩, hfail⟩
  have hfail' := fail_hdr hfail
  have hcm : makeCost 4 = RunAmd64.blockBound 64 := rfl
  have hca : allocCost 16 = RunAmd64.blockBound 16 := rfl
  have hokr : HdrOkR R b len := ⟨hok, by rw [hcm]; omega, hokm⟩
  obtain ⟨n, o, hrun, hQ⟩ := runPre impl hap R hmk hmv hno b L c p len cp ret hret s hs henv hin hinv hokr
    (osaka_read hrecv) hokn (by rw [hcm, hca]; exact hcost)
    (fun o => ∃ s', o = .returned s' ∧ ABIReturn s s' ∧ RunAmd64.ErrRet s' ∧
      RunAmd64.Frame R b (3 * RunAmd64.blockBound 64 + RunAmd64.blockBound 16) L s s')
    (fun S' _ habi herr hfr => ⟨S', rfl, habi, herr, frame_spec (by rw [hcm, hca]) hfr⟩)
    (fun S' h0 h1 h2 _ _ _ _ => absurd ⟨by omega, h1, by omega⟩ hfail')
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 _ _ _ _ _ _ _ => absurd ⟨h0, h1, h2⟩ hfail')
  obtain ⟨s', rfl, h⟩ := hQ
  exact ⟨n, s', hrun, h⟩

end FvModexp.Amd64.Run
