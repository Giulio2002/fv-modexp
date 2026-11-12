import FvModexp.Proofs.Amd64.Int.IntASPost

set_option autoImplicit false

/-!
# `(*Int).Add` / `(*Int).Sub` (amd64): from the return of the `nat` call to `RET`

The three call sites (`+0x56` after `nat.add`, `+0xf4` / `+0x15d` after `nat.sub(x, y)` / `nat.sub(y, x)`; `Sub` =
`Add` + `0x1e0`) continue with the same code: `MOVQ 0x60(SP), DX` (= z), `z.abs.len, cap` stores, the write-barrier
flag test (barrier on: `MOVQ 0x8(DX), CX`, `CALL gcWriteBarrier2`, the buffer stores at `R11`), `z.abs.ptr` store, the
sign byte `0x4f(SP)` (`+0x15d`: `XORL $1`), `z.neg = len ≠ 0 & neg`, `ADDQ $0x50, SP; POPQ BP; RET`. Twin of the arm64
`IntAS.tail`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.IntAS

/-- registers kept by the call (callee-saved part of the Go ABI; as `StackNat.RegsOK`) -/
@[reducible] def RegsOK (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15

/-- the final sign byte (amd64 `SETNE BL; ANDL CX, BX`): `(len ≠ 0) & neg` -/
theorem nbA (l' nx : Nat) (h : nx ≤ 1) :
    ((BitVec.toNat (BitVec.ofNat 64 l' &&& 18446744073709551360#64 |||
        BitVec.setWidth 64 (if l' = 0 then 0#8 else 1#8)) % 4294967296 &&& nx % 4294967296) % 256) =
      if l' = 0 then 0 else nx := by
  have key : ∀ W : BitVec 64, W.toNat % 2 = 1 →
      (W.toNat % 4294967296 &&& 1 % 4294967296) % 256 = 1 := by
    intro W hW
    rw [show (1 : Nat) % 4294967296 = 1 from rfl, Nat.and_one_is_mod]
    omega
  rcases (by omega : nx = 0 ∨ nx = 1) with rfl | rfl
  · simp
  · by_cases hl : l' = 0
    · subst hl; decide
    · simp only [hl, ↓reduceIte]
      refine key _ ?_
      rw [BitVec.toNat_or, BitVec.toNat_and]
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.or_mod_two_eq_one]
      exact Or.inr (by decide)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem tail (impl : List Amd64.Segment) (R : RtInv)
    (hwb : WbLiveContract64 (LibIntAS.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (sub : Bool) (off : Nat) (hoff : off = 0x56 ∨ off = 0xf4 ∨ off = 0x15d)
    (b : Nat) (L : List (Nat × Nat)) (z x y : Nat) (s : State)
    (nb V cost p' l' c' b1 : Nat) (L1 : List (Nat × Nat)) (S : State)
    (h : AtRet sub R b L z x y s nb V cost p' l' c' b1 L1 S) (hpc : S.rip = BitVec.ofNat 64 (entry sub + off))
    (hnb : nb = if off = 0x15d then 1 - hNeg s.mem x else hNeg s.mem x)
    (hra47 : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ReachesRet (LibIntAS.program.link impl) (retAddrOf s) S fun s' => RegsOK s s' ∧ Post sub R b L z x y s s' := by
  have hpre := h.pre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hb', ha, hw⟩, -, -, hout, -, -, hLs, -, -⟩, hsv, -, hx, -, hza, hz48, hzo, hzH, -, -,
    hzwb, -, -, -, -, -, -, hwbf, -, -⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  have hnx : hNeg s.mem x ≤ 1 := hx.1
  clear hx
  have hsp := h.sp; have h14 := h.g; have hfs := h.fs; have hdf := h.df; have hx15 := h.x15; have h5 := h.bp
  have h0 := h.r0; have h3 := h.r3; have h1 := h.r1
  have hc40 := h.c40; have hlc := h.lc; have hp64 := h.p64
  simp only [win, outside_cons, outside_nil, and_true] at hzo
  unfold Apart at hzwb
  have hwbv : wbA = 12283968 := rfl
  rw [hwbv] at hzwb hwbf
  have h88 : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have hzs : S.mem.readLE ((s.regs 4).toNat - 88 + 96) 8 = z := by
    rw [show (s.regs 4).toNat - 88 + 96 = (s.regs 4).toNat + 8 by omega]; exact h.zs
  have hng : S.mem.readLE ((s.regs 4).toNat - 88 + 79) 1 = hNeg s.mem x := by
    rw [show (s.regs 4).toNat - 88 + 79 = (s.regs 4).toNat - 9 by omega]; exact h.ng
  have hmbp : S.mem.readLE ((s.regs 4).toNat - 88 + 80) 8 = (s.regs 5).toNat := by
    rw [show (s.regs 4).toNat - 88 + 80 = (s.regs 4).toNat - 8 by omega]; exact h.mbp
  have hra : S.mem.readLE ((s.regs 4).toNat - 88 + 88) 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [show (s.regs 4).toNat - 88 + 88 = (s.regs 4).toNat by omega]; exact h.ra
  have hzaS : S.mem.accessible z 32 true = true := by rw [h.mf.accessible]; exact hza
  have hwbS : S.mem.accessible 12283968 4 false = true := by rw [h.mf.accessible]; exact hwbf
  have hwS : S.mem.accessible ((s.regs 4).toNat - 4536) (4536 + 32) true = true := by rw [h.mf.accessible]; exact hw
  have hzH1 : Held R L1 z 32 := h.ext.held hzH
  rcases hoff with rfl | rfl | rfl <;> cases sub <;>
    simp only [entry, Bool.false_eq_true, ↓reduceIte, Nat.reduceEqDiff] at hpc hnb <;>
    janus64_run [hsp, h88, hzs, hng, hmbp, hra, h.zs, h.ng, h.mbp, h.ra, hzaS, hwbS] until [cA "runtime.gcWriteBarrier2"]
  -- WIP (divmc s28): close the 6 no-barrier goals with `post_of` (+ `nbA`) and the 6 barrier ones as arm64 `IntAS.tail`
  all_goals sorry

end FvModexp.Amd64.IntAS
