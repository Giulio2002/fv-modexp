import FvModexp.Proofs.Arm64.Nat.DrsCall

/-!
# `divRecursiveStep` (arm64): the epilogues and the post of the paths that write only the frame

`LDP -8(RSP), (R29, R30); ADD $400, RSP, RSP; RET` at `fn + 0x11c` (`m < 0`), `fn + 0x12c` (after `divBasic`),
`fn + 0x144` (after `clear(z)`); `post_frame`: a path that writes only its own frame (`fw s`) and leaves `z = U/V`,
`u = U mod V` already in place satisfies `DrsPostW` (no allocation, same stack, same live set).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- a range outside the window is outside the frame's own writes -/
theorem fw_out {s : State} {W a n : Nat} (hW : 408 ≤ W) (h : Outside a n (win s W 96)) : Outside a n (fw s) := by
  simp only [win, fw, winA, outside_cons, outside_nil, and_true] at h ⊢; omega

set_option maxHeartbeats 4000000 in
/-- **the post of a frame-only path** (pure) -/
theorem post_frame {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c W qp ql qc st up ul uc vp vl vc : Nat}
    {s s' : State} (hpre : DrsPreW R b L c W qp ql qc st up ul uc vp vl vc s) (hW : 408 ≤ W)
    (hF : MemFrame s.mem s'.mem (fw s))
    (hq : natVal s.mem qp ql = natVal s.mem up ul / natVal s.mem vp vl)
    (hu : natVal s.mem up ul = natVal s.mem up ul % natVal s.mem vp vl) :
    DrsPostW R b L c W qp ql st up ul vp vl s s' := by
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, hqo, huo, -, -, -, -, hsti, -, -, -, -, -, -, -, -, -, hinv⟩ := hpre
  have hce' := hce
  obtain ⟨-, ⟨-, hb', -, -⟩, -, hout, -, -, hLs, -⟩ := hce'
  have hst := hsti.2.1
  have e0 : stW s'.mem st = stW s.mem st := hF.readLE _ _ (fw_out hW (hst.of_sub (Nat.le_refl _) (by omega)))
  have e1 : stLen s'.mem st = stLen s.mem st := hF.readLE _ _ (fw_out hW (hst.of_sub (by omega) (by omega)))
  have e2 : stCap s'.mem st = stCap s.mem st := hF.readLE _ _ (fw_out hW (hst.of_sub (by omega) (by omega)))
  have hrt : ∀ r ∈ fw s, Outside r.1 (r.2 - r.1) R.rt ∨ InRanges r.1 (r.2 - r.1) L := by
    intro r hr
    simp only [fw, winA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (left; exact hout.of_sub (by simp only; omega) (by simp only; omega))
  refine ⟨?_, ?_, L, b, ⟨LiveExt.refl R L, Nat.sub_le _ _, RtInv.inv_frame' hF hrt hinv⟩, ?_, ?_, ?_⟩
  · rw [natVal_frame hF (fw_out hW hqo.2.2.2.1)]; exact hq
  · rw [natVal_frame hF (fw_out hW huo.2.2.2.1)]; exact hu
  · obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, -⟩ := hsti
    refine ⟨⟨h1, h2, by rw [hF.accessible]; exact h3, h4, ?_, by rw [e1, e2]; exact h6, by rw [e2]; exact h7⟩,
      e1, Or.inl ⟨e0, e2⟩⟩
    rw [e0, e2]; intro hc; obtain ⟨a1, a2, a3, a4⟩ := h5 hc; exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · refine hF.mono fun a n ho => ?_
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho
    simp only [fw, winA, outside_cons, outside_nil, and_true]
    omega
  · refine ⟨fun a n hin _ => hF.readLE a n ?_⟩
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, fw, winA, outside_cons, outside_nil, and_true] at this ⊢
    omega

/-- the facts at a return of `divRecursiveStep` (entry state `s`, final state `s'`, memory as at the epilogue) -/
@[reducible] def Ret (s : State) (M : Memory) (s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18 ∧ s'.mem = M

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- the epilogue at `fn + 0x11c` -/
theorem epiC (impl : List Segment) (s T : State) (hpc : T.pc = BitVec.ofNat 64 0x1ba4bc) (hsp : T.sp = s.sp - 400#64) (h28 : T.regs 28 = s.regs 28)
    (h18 : T.regs 18 = s.regs 18) (hlr : T.mem.readLE (s.sp.toNat - 400) 8 = (s.regs 30).toNat)
    (hfp : T.mem.readLE (s.sp.toNat - 408) 8 = (s.regs 29).toNat)
    (h0 : 408 ≤ s.sp.toNat) (h48 : s.sp.toNat ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hacc : T.mem.accessible (s.sp.toNat - 408) 16 false = true)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48) (Q : State → Prop) (k : ∀ s', Ret s T.mem s' → Q s') :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hlr' : BitVec.ofNat 64 (T.mem.readLE (s.sp.toNat - 400) 8) = s.regs 30 := by
    rw [hlr]; apply BitVec.eq_of_toNat_eq; simp
  janus_run [hlr']
  refine k _ ⟨rfl, ?_, ?_, ?_, rfl⟩
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hfp]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- the epilogue at `fn + 0x12c (after `divBasic`)` -/
theorem epiB (impl : List Segment) (s T : State) (hpc : T.pc = BitVec.ofNat 64 0x1ba4cc) (hsp : T.sp = s.sp - 400#64) (h28 : T.regs 28 = s.regs 28)
    (h18 : T.regs 18 = s.regs 18) (hlr : T.mem.readLE (s.sp.toNat - 400) 8 = (s.regs 30).toNat)
    (hfp : T.mem.readLE (s.sp.toNat - 408) 8 = (s.regs 29).toNat)
    (h0 : 408 ≤ s.sp.toNat) (h48 : s.sp.toNat ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hacc : T.mem.accessible (s.sp.toNat - 408) 16 false = true)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48) (Q : State → Prop) (k : ∀ s', Ret s T.mem s' → Q s') :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hlr' : BitVec.ofNat 64 (T.mem.readLE (s.sp.toNat - 400) 8) = s.regs 30 := by
    rw [hlr]; apply BitVec.eq_of_toNat_eq; simp
  janus_run [hlr']
  refine k _ ⟨rfl, ?_, ?_, ?_, rfl⟩
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hfp]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- the epilogue at `fn + 0x144 (after `clear(z)`)` -/
theorem epiZ (impl : List Segment) (s T : State) (hpc : T.pc = BitVec.ofNat 64 0x1ba4e4) (hsp : T.sp = s.sp - 400#64) (h28 : T.regs 28 = s.regs 28)
    (h18 : T.regs 18 = s.regs 18) (hlr : T.mem.readLE (s.sp.toNat - 400) 8 = (s.regs 30).toNat)
    (hfp : T.mem.readLE (s.sp.toNat - 408) 8 = (s.regs 29).toNat)
    (h0 : 408 ≤ s.sp.toNat) (h48 : s.sp.toNat ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hacc : T.mem.accessible (s.sp.toNat - 408) 16 false = true)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48) (Q : State → Prop) (k : ∀ s', Ret s T.mem s' → Q s') :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hlr' : BitVec.ofNat 64 (T.mem.readLE (s.sp.toNat - 400) 8) = s.regs 30 := by
    rw [hlr]; apply BitVec.eq_of_toNat_eq; simp
  janus_run [hlr']
  refine k _ ⟨rfl, ?_, ?_, ?_, rfl⟩
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hfp]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- the epilogue at `fn + 0x94c (after the deferred call)` -/
theorem epiF (impl : List Segment) (s T : State) (hpc : T.pc = BitVec.ofNat 64 0x1bacec) (hsp : T.sp = s.sp - 400#64) (h28 : T.regs 28 = s.regs 28)
    (h18 : T.regs 18 = s.regs 18) (hlr : T.mem.readLE (s.sp.toNat - 400) 8 = (s.regs 30).toNat)
    (hfp : T.mem.readLE (s.sp.toNat - 408) 8 = (s.regs 29).toNat)
    (h0 : 408 ≤ s.sp.toNat) (h48 : s.sp.toNat ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hacc : T.mem.accessible (s.sp.toNat - 408) 16 false = true)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48) (Q : State → Prop) (k : ∀ s', Ret s T.mem s' → Q s') :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q := by
  have hal' : (s.sp - 400#64).toNat % 16 = 0 := by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hlr' : BitVec.ofNat 64 (T.mem.readLE (s.sp.toNat - 400) 8) = s.regs 30 := by
    rw [hlr]; apply BitVec.eq_of_toNat_eq; simp
  janus_run [hlr']
  refine k _ ⟨rfl, ?_, ?_, ?_, rfl⟩
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h28]
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hfp]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h18]

end FvModexp.Arm64.DivRec
