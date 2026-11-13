import FvModexp.Proofs.Amd64.Exp.W4Lsh

set_option autoImplicit false

/-!
# window-4 prologue (amd64): `RR = RR.setWord(1)` (inline, cap `2n > 0`) and the call setup of `nat.lsh`,
`sn1Ret → lshE` (nat.go:1397-1398; agent expmc s54; twin of `Arm64.W4LshR`)

At `sn1Ret` (fn+0x4ed) `TESTQ CX; JNE fn+0x50b`: the cap `CX = 2n ≠ 0`, so the frame-buffer path (`0x108`) is not
taken. fn+0x50b: `[0x190] = AX`, `[0xa8] = CX`, `[AX] = 1`; `R9 = [0x3b0] << 7` (= `128 n`), `AX = BX = CX = 0`,
`DI = RR`, `SI = 1`, `R8 = 2n`, `CALL nat.lsh` (return address `lshRet` at `[sp - 8]`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.W4Pro

/-- return of `stk.nat(2n)` #1 (fn+0x4ed) -/
abbrev sn1Ret : Nat := 6206797

/-- the words `toLsh` writes -/
@[reducible] def lshWs (sp rrp : Nat) : List (Nat × Nat) :=
  [(sp - 8, sp), (sp + 0xa8, sp + 0xb0), (sp + 0x190, sp + 0x198), (rrp, rrp + 8)]

theorem shl7 {n : Nat} (hn128 : n ≤ 128) : BitVec.ofNat 64 n <<< 7 = BitVec.ofNat 64 (128 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem toLsh {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    {sp rrp n : Nat} {M : Memory}
    (hal : sp % 16 = 0) (hsp1 : 4296 ≤ sp) (hsp2 : sp + 0x3c0 ≤ 2 ^ 48)
    (hacc : M.accessible (sp - 4296) (4296 + 0x3c0) true = true)
    (hn : 0 < n) (hn128 : n ≤ 128) (r3b0 : M.readLE (sp + 0x3b0) 8 = n)
    (hracc : M.accessible rrp 8 true = true) (hr48 : rrp + 8 ≤ 2 ^ 48)
    (hrw : rrp + 8 ≤ sp - 4296 ∨ sp + 0x3c0 ≤ rrp)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 sn1Ret) (hsp : S.regs 4 = BitVec.ofNat 64 sp) (hmem : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 rrp) (h1 : S.regs 1 = BitVec.ofNat 64 (2 * n))
    (KL : ∀ (S' : State), S'.rip = BitVec.ofNat 64 lshE → S'.regs 4 = BitVec.ofNat 64 (sp - 8) →
      S'.regs 0 = BitVec.ofNat 64 0 → S'.regs 3 = BitVec.ofNat 64 0 → S'.regs 1 = BitVec.ofNat 64 0 →
      S'.regs 7 = BitVec.ofNat 64 rrp → S'.regs 6 = BitVec.ofNat 64 1 → S'.regs 8 = BitVec.ofNat 64 (2 * n) →
      S'.regs 9 = BitVec.ofNat 64 (128 * n) →
      S'.regs 5 = S.regs 5 → S'.regs 14 = S.regs 14 →
      S'.fsBase = S.fsBase → S'.xmm 15 = S.xmm 15 → S'.df = S.df →
      MemFrame M S'.mem (lshWs sp rrp) → S'.mem.regions = M.regions →
      S'.mem.readLE (sp - 8) 8 = lshRet → S'.mem.readLE (sp + 0x190) 8 = rrp →
      S'.mem.readLE (sp + 0xa8) 8 = 2 * n → S'.mem.readLE rrp 8 = 1 →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  have hne : BitVec.ofNat 64 (2 * n) ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [r3b0, hne] until [lshE]
  refine KL _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  all_goals try simp only [setRegF_apply, callRegs64_apply, Nat.reduceEqDiff, ↓reduceIte, true_or, or_true]
  · exact shl7 hn128
  · have i0 : ∀ a, sp - 8 ≤ a → a + 8 ≤ sp → InRanges a 8 (lshWs sp rrp) :=
      fun a h1 h2 => ⟨(sp - 8, sp), by simp only [lshWs, List.mem_cons, true_or], h1, h2⟩
    have i1 : ∀ a, sp + 0xa8 ≤ a → a + 8 ≤ sp + 0xb0 → InRanges a 8 (lshWs sp rrp) :=
      fun a h1 h2 => ⟨(sp + 0xa8, sp + 0xb0), by simp only [lshWs, List.mem_cons, true_or, or_true], h1, h2⟩
    have i2 : ∀ a, sp + 0x190 ≤ a → a + 8 ≤ sp + 0x198 → InRanges a 8 (lshWs sp rrp) :=
      fun a h1 h2 => ⟨(sp + 0x190, sp + 0x198), by simp only [lshWs, List.mem_cons, true_or, or_true], h1, h2⟩
    have i3 : ∀ a, rrp ≤ a → a + 8 ≤ rrp + 8 → InRanges a 8 (lshWs sp rrp) :=
      fun a h1 h2 => ⟨(rrp, rrp + 8), by simp only [lshWs, List.mem_cons, true_or, or_true], h1, h2⟩
    exact ((((MemFrame.refl _ _).writeLE_inRanges _ (i2 _ (by omega) (by omega))).writeLE_inRanges _
      (i1 _ (by omega) (by omega))).writeLE_inRanges _ (i3 _ (by omega) (by omega))).writeLE_inRanges _
      (i0 _ (by omega) (by omega))
  · simp only [Janus.Arm64.Memory.regions_writeLE]
  all_goals
    simp (disch := omega) only [readLE_writeLE_disjoint, readLE_writeLE_same]
  all_goals exact Nat.mod_eq_of_lt (by omega)

end FvModexp.Amd64.W4Pro
