import FvModexp.Proofs.Arm64.Int.IntASC

/-!
# `(*Int).Add` / `(*Int).Sub` (go-bigmodexpfix int.go:141 / int.go:162), arm64: the summaries

`full`: from the entry (prologue, `neg := x.neg`, the sign test) to `pathA` (`nat.add`) or `pathBC` (`nat.cmp`, then
`nat.sub`). `ens sub`: the `Ensures` of CONVENTIONS §3 (`sub = false`: `Add`, `true`: `Sub`); `sum`: as a callee summary.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.IntAS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem full (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : BitVec 64) :
    Summary (LibIntAS.program.link impl) (entry sub)
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.regs 0 = z ∧ s.regs 1 = x ∧
        s.regs 2 = y ∧ Pre R b L z.toNat x.toNat y.toNat s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post sub R b L z.toNat x.toNat y.toNat s s') := by
  intro s hpc ⟨hl4, hl48, h0, h1, h2, hpre⟩
  have hwb' := wbIn hap hwb
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩, -, -, hx, hy, hza, hz48, hzo, -⟩ := hpre'
  obtain ⟨hnx, hxa, hx48, hxo, -⟩ := hx
  obtain ⟨hny, hya, hy48, hyo, -⟩ := hy
  simp only [win, outside_cons, outside_nil, and_true] at hxo hyo hzo
  unfold Apart at hga
  have hpreB : Box (Pre R b L z.toNat x.toNat y.toNat s) := ⟨hpre⟩
  clear hpre
  have hsp96 : (s.sp - 96#64).toNat = s.sp.toNat - 96 := sp96 hb'
  have hb1 : s.mem.readLE x.toNat 1 < 256 := by have := Memory.readLE_lt s.mem x.toNat 1; simpa using this
  cases sub <;> simp only [entry, Bool.false_eq_true, ↓reduceIte] at hpc <;>
    janus_run until [1781184, 1782608]
  all_goals first
  | refine pathBC impl hap R hmk hmv hwb' _ b L z.toNat x.toNat y.toNat s hpreB.h hl4 hl48 ?hc _ rfl ?h30 ?_ ?_ ?_ ?_
      ⟨rfl, ?r28, ?r29, ?r18, ?mf, ?reg, ?_, ?_, ?_, ?_⟩ ?_ ?_
    case hc =>
      have e1 : hNeg s.mem x.toNat = 0 ∨ hNeg s.mem x.toNat = 1 := by omega
      have e2 : hNeg s.mem y.toNat = 0 ∨ hNeg s.mem y.toNat = 1 := by omega
      simp only [hNeg] at e1 e2 ⊢
      rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2 <;> rw [h1, h2] at hbr ⊢ <;> revert hbr <;> decide
    case h30 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, entry] <;> decide
    case r28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    case r29 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    case r18 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    case mf => simp only [winA]; janus_frame
    case reg => simp only [Memory.regions_writeLE]
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals (try janus_simp)
    all_goals omega
  | refine pathA impl hap R hmk hmv hwb' _ b L z.toNat x.toNat y.toNat s hpreB.h hl4 hl48 ?hc _ rfl ?h30 ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ⟨rfl, ?r28, ?r29, ?r18, ?mf, ?reg, ?_, ?_, ?_, ?_⟩
    case hc =>
      have e1 : hNeg s.mem x.toNat = 0 ∨ hNeg s.mem x.toNat = 1 := by omega
      have e2 : hNeg s.mem y.toNat = 0 ∨ hNeg s.mem y.toNat = 1 := by omega
      simp only [hNeg] at e1 e2 ⊢
      rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2 <;> rw [h1, h2] at hbr ⊢ <;> revert hbr <;> decide
    case h30 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, entry] <;> decide
    case r28 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    case r29 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    case r18 => simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    case mf => simp only [winA]; janus_frame
    case reg => simp only [Memory.regions_writeLE]
    all_goals (try simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte])
    all_goals (try janus_simp)
    all_goals omega

/-- **`(*Int).Add` (`sub = false`) / `(*Int).Sub` (`sub = true`)** (arm64): `z.Add(x, y)` / `z.Sub(x, y)` returns `z`
holding `x + y` / `x - y` (signed, canonical sign, normalised `abs` in `z`'s array or a fresh one); writes only `z`'s
header, `z`'s array, `R.rt` and the window; no panic, no fault. -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program (fn sub)) [z, x, y]
      (Pre R b L z.toNat x.toNat y.toNat) (Post sub R b L z.toNat x.toNat y.toNat) := by
  janus_ensures_old [FvModexp.Arm64.IntAS.Pre, FvModexp.Arm64.CallEnv, FvModexp.Arm64.NatAdd.wordT, FvModexp.Arm64.IntAS.OpR, FvModexp.Arm64.win, FvModexp.Arm64.IntAS.wbA, FvModexp.Arm64.IntAS.hC, FvModexp.NatLive, FvModexp.Arm64.IntAS.hP, FvModexp.Arm64.IntAS.hL, Janus.Spec.GuardOK, Janus.Spec.StackOK, FvModexp.Arm64.IntAS.hNeg, FvModexp.NatNorm]
  rw [show names = LibIntAS.names from rfl, ← LibIntAS.eq_only, entry_eq]
  cases sub
  · simp only [entry, Bool.false_eq_true, ↓reduceIte]
    intro ret hret s hs hpre
    janus_intro hs
    have hr48 := hret.user
    have hr4 := hret.aligned
    refine Summary.returns (full impl hap R hmk hmv hwb false b L z x y) hret h_pc h_lr
      ⟨?_, ?_, h_x0, h_x1, h_x2, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
    · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
    · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48
  · simp only [entry, Bool.false_eq_true, ↓reduceIte]
    intro ret hret s hs hpre
    janus_intro hs
    have hr48 := hret.user
    have hr4 := hret.aligned
    refine Summary.returns (full impl hap R hmk hmv hwb true b L z x y) hret h_pc h_lr
      ⟨?_, ?_, h_x0, h_x1, h_x2, hpre⟩ fun s' ⟨⟨a, b, c, d⟩, hq⟩ => ⟨⟨a, b, c, d⟩, hq⟩
    · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr4
    · rw [h_lr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]; exact hr48

set_option linter.defProp false in
/-- `ens` as a callee summary in a caller whose program keeps the functions `ms ⊇ names` (CONVENTIONS §4). -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (b : Nat) (L : List (Nat × Nat)) (z x y : BitVec 64) (ms : List String)
    (hsub : ∀ x, names.contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmk hmv hwb sub b L z x y) (noExit_restrict hap names)
    (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.IntAS
