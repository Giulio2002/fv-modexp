import FvModexp.Proofs.Arm64.Nat.MulITail

set_option autoImplicit false

/-!
# `(*Int).mul` (arm64): the inner `z.abs = z.abs.mul(stk, x.abs, y.abs)` call at `0x1b0cfc` (int.go:201) → `IR` → `RET`

`icall`: from the `CALL` (`SP' = SP - 96`, the three header triples in `X0..X2`, `X4..X9`, `stk` in `X3`) via the
induction hypothesis for `nat.mul` (window `W - 96`, measure `μl xl yl + 3 < μl xl yl + 4`), `ir_of` and `itail`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.IntAS (hNeg hP hL hC intZ wbA tN)

theorem rd64 (m : Memory) (a : Nat) : m.readLE a 8 < 2 ^ 64 := Nat.lt_of_lt_of_le (Memory.readLE_lt _ _ _) (by decide)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
set_option janus.callRegions true in
theorem icall (impl : List Segment) (R : RtInv)
    (hwb : WbLiveContract (LibMul.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (n : Nat) (ih : ∀ j, IH impl R n j) {b : Nat} {L : List (Nat × Nat)} {W z : Nat} {stk : BitVec 64} {x y : Nat}
    {s : State} (hpre : IPre R b L W z stk.toNat x y s) (hμ : μl (hL s.mem x) (hL s.mem y) + 3 < n)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1b0cfc) (hsp : S.sp = s.sp - 96#64) (h28 : S.regs 28 = s.regs 28)
    (h29 : S.regs 29 = s.sp - 104#64) (h18 : S.regs 18 = s.regs 18)
    (r0 : S.regs 0 = BitVec.ofNat 64 (hP s.mem z)) (r1 : S.regs 1 = BitVec.ofNat 64 (hL s.mem z))
    (r2 : S.regs 2 = BitVec.ofNat 64 (hC s.mem z)) (r3 : S.regs 3 = stk)
    (r4 : S.regs 4 = BitVec.ofNat 64 (hP s.mem x)) (r5 : S.regs 5 = BitVec.ofNat 64 (hL s.mem x))
    (r6 : S.regs 6 = BitVec.ofNat 64 (hC s.mem x)) (r7 : S.regs 7 = BitVec.ofNat 64 (hP s.mem y))
    (r8 : S.regs 8 = BitVec.ofNat 64 (hL s.mem y)) (r9 : S.regs 9 = BitVec.ofNat 64 (hC s.mem y))
    (hF : MemFrame s.mem S.mem (winA s W 40)) (hreg : S.mem.regions = s.mem.regions)
    (m104 : S.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat)
    (m96 : S.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat)
    (m8 : S.mem.readLE (s.sp.toNat + 8) 8 = z) (m24 : S.mem.readLE (s.sp.toNat + 24) 8 = x)
    (m32 : S.mem.readLE (s.sp.toNat + 32) 8 = y) :
    ReachesRet (LibMul.program.link impl) (s.regs 30) S fun s' =>
      Kept s s' ∧ IPost R b L W z stk.toNat x y s s' := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, -⟩, hiw, -⟩ := hpre'
  have hW4 : 4704 ≤ W := Nat.le_trans (Nat.add_le_add_right (mulW_ge _ _) 96) hiw
  have hsp' : S.sp.toNat = s.sp.toNat - 96 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have e0 := tN (rd64 s.mem (z + 8)); have e2 := tN (rd64 s.mem (z + 24))
  have e4 := tN (rd64 s.mem (x + 8)); have e5 := tN (rd64 s.mem (x + 16)); have e6 := tN (rd64 s.mem (x + 24))
  have e7 := tN (rd64 s.mem (y + 8)); have e8 := tN (rd64 s.mem (y + 16)); have e9 := tN (rd64 s.mem (y + 24))
  have hBS : Summary (LibMul.program.link impl) 0x1bae70 _ _ := Summary.mono
    (ih (.mul, ⟨b, L, W - 96, BitVec.ofNat 64 (hP s.mem z), BitVec.ofNat 64 (hL s.mem z),
      BitVec.ofNat 64 (hC s.mem z), stk, BitVec.ofNat 64 (hP s.mem x), BitVec.ofNat 64 (hL s.mem x),
      BitVec.ofNat 64 (hC s.mem x), BitVec.ofNat 64 (hP s.mem y), BitVec.ofNat 64 (hL s.mem y),
      BitVec.ofNat 64 (hC s.mem y)⟩))
    (pre' := fun s1 => (s1.regs 30).toNat % 4 = 0 ∧ (s1.regs 30).toNat < 2 ^ 48 ∧
      s1.regs 0 = BitVec.ofNat 64 (hP s.mem z) ∧ s1.regs 1 = BitVec.ofNat 64 (hL s.mem z) ∧
      s1.regs 2 = BitVec.ofNat 64 (hC s.mem z) ∧ s1.regs 3 = stk ∧ s1.regs 4 = BitVec.ofNat 64 (hP s.mem x) ∧
      s1.regs 5 = BitVec.ofNat 64 (hL s.mem x) ∧ s1.regs 6 = BitVec.ofNat 64 (hC s.mem x) ∧
      s1.regs 7 = BitVec.ofNat 64 (hP s.mem y) ∧ s1.regs 8 = BitVec.ofNat 64 (hL s.mem y) ∧
      s1.regs 9 = BitVec.ofNat 64 (hC s.mem y) ∧ s1.sp = S.sp ∧ s1.regs 28 = S.regs 28 ∧ s1.mem = S.mem)
    (post' := fun s1 s2 => Kept s1 s2 ∧
      IntAS.Box (∃ S1 : State, S1.mem = S.mem ∧ S1.sp = S.sp ∧ S1.regs 28 = S.regs 28 ∧
        MPost R b L (W - 96) (hP s.mem z) (hC s.mem z) stk.toNat (hP s.mem x) (hL s.mem x) (hC s.mem x)
          (hP s.mem y) (hL s.mem y) (hC s.mem y) S1 s2))
    (fun s1 ⟨hr4, hr48, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, hs, hg, hm⟩ => by
      refine ⟨⟨⟨hr4, hr48, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩, ?_⟩, ?_⟩
      · show MPre R b L (W - 96) (BitVec.ofNat 64 (hP s.mem z)).toNat (BitVec.ofNat 64 (hC s.mem z)).toNat stk.toNat
          (BitVec.ofNat 64 (hP s.mem x)).toNat (BitVec.ofNat 64 (hL s.mem x)).toNat (BitVec.ofNat 64 (hC s.mem x)).toNat
          (BitVec.ofNat 64 (hP s.mem y)).toNat (BitVec.ofNat 64 (hL s.mem y)).toNat (BitVec.ofNat 64 (hC s.mem y)).toNat s1
        rw [e0, e2, e4, e5, e6, e7, e8, e9]
        exact ipre_down hpre (by rw [hs]; exact hsp') (by rw [hg, h28]) (by rw [hm]; exact hF) (by rw [hm]; exact hreg)
      · show μl (BitVec.ofNat 64 (hL s.mem x)).toNat (BitVec.ofNat 64 (hL s.mem y)).toNat + 3 < n
        rw [e5, e8]; exact hμ)
    (fun s1 s2 ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs, hg, hm⟩ ⟨hk, hq⟩ => by
      refine ⟨hk, ⟨⟨s1, hm, hs, hg, ?_⟩⟩⟩
      have hq' : MPost R b L (W - 96) (BitVec.ofNat 64 (hP s.mem z)).toNat (BitVec.ofNat 64 (hC s.mem z)).toNat
          stk.toNat (BitVec.ofNat 64 (hP s.mem x)).toNat (BitVec.ofNat 64 (hL s.mem x)).toNat
          (BitVec.ofNat 64 (hC s.mem x)).toNat (BitVec.ofNat 64 (hP s.mem y)).toNat
          (BitVec.ofNat 64 (hL s.mem y)).toNat (BitVec.ofNat 64 (hC s.mem y)).toNat s1 s2 := hq
      rw [e0, e2, e4, e5, e6, e7, e8, e9] at hq'
      exact hq')
  janus_run until [0x1b0d00] calls [hBS]
  rename_i hpc' ksp k28 k29 k18 hbox
  obtain ⟨⟨S1, hm1, hs1, hg1, hq⟩⟩ := hbox
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, regLR] at hpc' ksp k28 k29 k18
  have hsp1 : S1.sp.toNat = s.sp.toNat - 96 := by rw [hs1, ← hsp]; exact hsp'
  obtain ⟨p', l', c', b1, L1, hIR⟩ := ir_of hpre hl4 hl48 hsp1 hg1 (by rw [hm1]; exact hF) (by rw [hm1]; exact m104)
    (by rw [hm1]; exact m96) (by rw [hm1]; exact m8) (by rw [hm1]; exact m24) (by rw [hm1]; exact m32) hq
    (by rw [ksp]) (by rw [k28, h28]) (by rw [k29, h29]) (by rw [k18, h18])
  exact itail impl R hwb b L W z stk.toNat x y s p' l' c' b1 L1 s' hIR hpc'

end FvModexp.Arm64.NatMul
