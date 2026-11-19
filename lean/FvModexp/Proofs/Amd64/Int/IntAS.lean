import FvModexp.Proofs.Amd64.Int.IntASA
import FvModexp.Proofs.Amd64.Int.IntASC

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (go-bigmodexpfix int.go:141 / int.go:162), amd64: the summaries

`full`: from the entry (stack check, prologue, `neg := x.neg` at `0x4f(SP)`, the sign test `CMPB 0(CX), DL`) to
`pathA` (`nat.add`) or `pathBC` (`nat.cmp`, then `nat.sub`). `ens sub`: the `Ensures` (`sub = false`: `Add`, `true`:
`Sub`); `sum`: as a callee summary. Twin of the arm64 `IntAS`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.IntAS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : BitVec 64) :
    Summary (LibIntAS.program.link impl) (entry sub)
      (fun s => s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ s.xmm 15 = 0#128 ∧ s.df = false ∧
        s.regs 0 = z ∧ s.regs 3 = x ∧ s.regs 1 = y ∧ Pre R b L z.toNat x.toNat y.toNat s)
      (fun s s' => RegsOK s s' ∧ Post sub R b L z.toNat x.toNat y.toNat s s') := by
  intro s hpc ⟨hra, hx15, hdf, h0, h3, h1, hpre⟩
  have hc : CodeIn64 (Extracted.program.ofImpl impl) (LibIntAS.program.link impl) := by
    rw [LibIntAS.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap names
  have hwb' := WbLiveContract64.of_codeIn hc hwb
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, -, hout, hga, -⟩, -, -, hx, hy, hza, hz48, hzo, -⟩ := hpre'
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  obtain ⟨hnx, hxa, hx48, hxo, -⟩ := hx
  obtain ⟨hny, hya, hy48, hyo, -⟩ := hy
  simp only [win, outside_cons, outside_nil, and_true] at hxo hyo hzo
  unfold Apart at hga
  have hpreB : Box (Pre R b L z.toNat x.toNat y.toNat s) := ⟨hpre⟩
  clear hpre
  have hsp96 : (s.regs 4 - 96#64).toNat = (s.regs 4).toNat - 96 := sp96 hb'
  have hb1 : s.mem.readLE x.toNat 1 < 256 := by have := Arm64.Memory.readLE_lt s.mem x.toNat 1; simpa using this
  cases sub <;> simp only [entry, Bool.false_eq_true, ↓reduceIte] at hpc <;>
    janus64_run until [6182240, 6184128]
  · (
      refine pathA impl hap R hmk hmv hwb' _ b L z.toNat x.toNat y.toNat s hpreB.h hx15 hdf hra (by
          have e1 : hNeg s.mem x.toNat = 0 ∨ hNeg s.mem x.toNat = 1 := by omega
          have e2 : hNeg s.mem y.toNat = 0 ∨ hNeg s.mem y.toNat = 1 := by omega
          simp only [hNeg] at e1 e2 ⊢
          rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2 <;> rw [h1, h2] at hbr ⊢ <;> revert hbr <;> decide) _ rfl
        (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96, Arm64.Memory.readLE_writeLE_self] <;> decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ⟨?_, ?_, rfl, (by first | rfl | exact hdf.symm | simp only [hdf]), rfl, ?_, (by simp only [win]; janus_frame), (by simp only [Arm64.Memory.regions_writeLE]), ?_, ?_, ?_, ?_⟩
      all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      all_goals janus64_simp)
  · (
      refine pathBC impl hap R hmk hmv hwb' _ b L z.toNat x.toNat y.toNat s hpreB.h hx15 hdf hra (by
          have e1 : hNeg s.mem x.toNat = 0 ∨ hNeg s.mem x.toNat = 1 := by omega
          have e2 : hNeg s.mem y.toNat = 0 ∨ hNeg s.mem y.toNat = 1 := by omega
          simp only [hNeg] at e1 e2 ⊢
          rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2 <;> rw [h1, h2] at hbr ⊢ <;> revert hbr <;> decide) _ rfl
        (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96, Arm64.Memory.readLE_writeLE_self] <;> decide) ?_ ?_ ?_ ?_
        ⟨?_, ?_, rfl, (by first | rfl | exact hdf.symm | simp only [hdf]), rfl, ?_, (by simp only [win]; janus_frame), (by simp only [Arm64.Memory.regions_writeLE]), ?_, ?_, ?_, ?_⟩ ?_ ?_
      all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      all_goals janus64_simp)
  · (
      refine pathBC impl hap R hmk hmv hwb' _ b L z.toNat x.toNat y.toNat s hpreB.h hx15 hdf hra (by
          have e1 : hNeg s.mem x.toNat = 0 ∨ hNeg s.mem x.toNat = 1 := by omega
          have e2 : hNeg s.mem y.toNat = 0 ∨ hNeg s.mem y.toNat = 1 := by omega
          simp only [hNeg] at e1 e2 ⊢
          rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2 <;> rw [h1, h2] at hbr ⊢ <;> revert hbr <;> decide) _ rfl
        (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96, Arm64.Memory.readLE_writeLE_self] <;> decide) ?_ ?_ ?_ ?_
        ⟨?_, ?_, rfl, (by first | rfl | exact hdf.symm | simp only [hdf]), rfl, ?_, (by simp only [win]; janus_frame), (by simp only [Arm64.Memory.regions_writeLE]), ?_, ?_, ?_, ?_⟩ ?_ ?_
      all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      all_goals janus64_simp)
  · (
      refine pathA impl hap R hmk hmv hwb' _ b L z.toNat x.toNat y.toNat s hpreB.h hx15 hdf hra (by
          have e1 : hNeg s.mem x.toNat = 0 ∨ hNeg s.mem x.toNat = 1 := by omega
          have e2 : hNeg s.mem y.toNat = 0 ∨ hNeg s.mem y.toNat = 1 := by omega
          simp only [hNeg] at e1 e2 ⊢
          rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2 <;> rw [h1, h2] at hbr ⊢ <;> revert hbr <;> decide) _ rfl
        (by simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, hsp96, Arm64.Memory.readLE_writeLE_self] <;> decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ⟨?_, ?_, rfl, (by first | rfl | exact hdf.symm | simp only [hdf]), rfl, ?_, (by simp only [win]; janus_frame), (by simp only [Arm64.Memory.regions_writeLE]), ?_, ?_, ?_, ?_⟩
      all_goals simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
      all_goals janus64_simp)

/-- **`(*Int).Add` (`sub = false`) / `(*Int).Sub` (`sub = true`)** (amd64): `z.Add(x, y)` / `z.Sub(x, y)` returns `z`
holding `x + y` / `x - y` (signed, canonical sign, normalised `abs` in `z`'s array or a fresh one, `z`'s array written
only in `[0, min(max(len x, len y) + 1, cap z))`); writes only `z`'s header, `z`'s array, `R.rt` and the window;
`fsBase`/DF unchanged; no panic, no fault. -/
theorem ens (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program (fn sub)) [z, x, y]
      (Pre R b L z.toNat x.toNat y.toNat) (Post sub R b L z.toNat x.toNat y.toNat) := by
  janus64_ensures_old [FvModexp.Amd64.IntAS.Pre, FvModexp.Amd64.CallEnv, FvModexp.Amd64.NatAdd.wordT, FvModexp.Amd64.IntAS.OpR, FvModexp.Amd64.win, FvModexp.Amd64.IntAS.wbA, FvModexp.Amd64.IntAS.hC, FvModexp.NatLive, FvModexp.Amd64.IntAS.hP, FvModexp.Amd64.IntAS.hL, FvModexp.Amd64.TlsOK, FvModexp.Amd64.IntAS.hNeg, FvModexp.NatNorm]
  rw [show names = LibIntAS.names from rfl, ← LibIntAS.eq_only, entry_eq]
  cases sub <;> simp only [entry, Bool.false_eq_true, ↓reduceIte] <;> intro ret hret s hs hpre <;> janus64_intro hs
  · refine Summary.returns (full impl hap R hmk hmv hwb false b L z x y) hret (by rw [h_rip]; rfl)
      (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, hpre⟩
      fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
  · refine Summary.returns (full impl hap R hmk hmv hwb true b L z x y) hret (by rw [h_rip]; rfl)
      (by rw [retAddrOf, h_ret]) ⟨by rw [h_ret]; exact hret.user, h_x15, h_df, h_a0, h_a1, h_a2, hpre⟩
      fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hmv hwb sub b L z x y) (A64.noExit_restrict64 hap names)
    (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.IntAS

