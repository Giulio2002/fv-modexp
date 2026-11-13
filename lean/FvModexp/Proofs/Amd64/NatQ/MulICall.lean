import FvModexp.Proofs.Amd64.NatQ.MulITail

set_option autoImplicit false

/-!
# [amd64 port (divmc s54) of the Q-form Arm64/NatQ/MulICall.lean — TIGHT COSTS] `(*Int).mul` (amd64): the inner `z.abs = z.abs.mul(stk, x.abs, y.abs)` call (int.go:201) → `IR` → `RET`

`icall`: at the entry `0x5f0840` of `nat.mul` (after `CALL` at `0x5e2aa1`: callee `RSP₁ = RSP - 96`, return address
`0x5e2aa6` at `RSP₁`; `z.abs` in `AX, BX, CX`, `stk` in `DI`, `x.abs` in `SI, R8, R9`, `y.abs` on the stack at
`RSP₁ + 8 / + 16 / + 24`) via the induction hypothesis for `nat.mul` (`ReachesRet.call_regions`, window `W - 96`,
measure `μl xl yl + 3 < μl xl yl + 4`), then `ir_of` and `itail`. (Pattern: `KMulI.kn_icall`.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.IntAS (hNeg hP hL hC intZ wbA)

theorem tNI {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem rd64 (m : Arm64.Memory) (a : Nat) : m.readLE a 8 < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Arm64.Memory.readLE_lt _ _ _) (by decide)

theorem sp96_8 (a : BitVec 64) : a - 96#64 + 8 = a - 88#64 := by bv_omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem icall (impl : List Amd64.Segment) (R : RtInv)
    (hwb : WbLiveContract64 (LibMul.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (n : Nat) (ih : ∀ j, IH impl R H n j) {b : Nat} {L : List (Nat × Nat)} {W z : Nat} {stk : BitVec 64} {x y : Nat}
    {s : State} (hpre : IPre R b H L W z stk.toNat x y s) (hμ : μl (hL s.mem x) (hL s.mem y) + 3 < n)
    (hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hx0 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 0x5f0840) (hsp : S1.regs 4 = s.regs 4 - 96#64)
    (h14 : S1.regs 14 = s.regs 14) (h5 : S1.regs 5 = s.regs 4 - 8#64) (hfs : S1.fsBase = s.fsBase)
    (hdf : S1.df = s.df) (hx : S1.xmm 15 = s.xmm 15)
    (r0 : S1.regs 0 = BitVec.ofNat 64 (hP s.mem z)) (r3 : S1.regs 3 = BitVec.ofNat 64 (hL s.mem z))
    (r1 : S1.regs 1 = BitVec.ofNat 64 (hC s.mem z)) (r7 : S1.regs 7 = stk)
    (r6 : S1.regs 6 = BitVec.ofNat 64 (hP s.mem x)) (r8 : S1.regs 8 = BitVec.ofNat 64 (hL s.mem x))
    (r9 : S1.regs 9 = BitVec.ofNat 64 (hC s.mem x))
    (hF : MemFrame s.mem S1.mem (win s W 40)) (hreg : S1.mem.regions = s.mem.regions)
    (mra : S1.mem.readLE ((s.regs 4).toNat - 96) 8 = 0x5e2aa6)
    (my8 : S1.mem.readLE ((s.regs 4).toNat - 88) 8 = hP s.mem y)
    (my16 : S1.mem.readLE ((s.regs 4).toNat - 80) 8 = hL s.mem y)
    (my24 : S1.mem.readLE ((s.regs 4).toNat - 72) 8 = hC s.mem y)
    (mbp : S1.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat)
    (m0 : S1.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (m8 : S1.mem.readLE ((s.regs 4).toNat + 8) 8 = z) (m24 : S1.mem.readLE ((s.regs 4).toNat + 24) 8 = x)
    (m32 : S1.mem.readLE ((s.regs 4).toNat + 32) 8 = y) :
    ReachesRet (LibMul.program.link impl) (retAddrOf s) S1 fun s' =>
      Kept s s' ∧ IPost R b H L W z stk.toNat x y s s' := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hb', -, -⟩, -⟩, hiw, -⟩ := hpre'
  simp only [regSP] at hb'
  have hW4 : 4704 ≤ W := Nat.le_trans (Nat.add_le_add_right (mulW64_ge (hL s.mem x) (hL s.mem y)) 96) hiw
  have hsp' : (S1.regs 4).toNat = (s.regs 4).toNat - 96 := by
    rw [hsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
  have e0 := tNI (rd64 s.mem (z + 8)); have e1 := tNI (rd64 s.mem (z + 16)); have e2 := tNI (rd64 s.mem (z + 24))
  have e4 := tNI (rd64 s.mem (x + 8)); have e5 := tNI (rd64 s.mem (x + 16)); have e6 := tNI (rd64 s.mem (x + 24))
  have e7 := tNI (rd64 s.mem (y + 8)); have e8 := tNI (rd64 s.mem (y + 16)); have e9 := tNI (rd64 s.mem (y + 24))
  refine ReachesRet.call_regions (ih (.mul, ⟨b, L, W - 96, BitVec.ofNat 64 (hP s.mem z), BitVec.ofNat 64 (hL s.mem z),
      BitVec.ofNat 64 (hC s.mem z), stk, BitVec.ofNat 64 (hP s.mem x), BitVec.ofNat 64 (hL s.mem x),
      BitVec.ofNat 64 (hC s.mem x), BitVec.ofNat 64 (hP s.mem y), BitVec.ofNat 64 (hL s.mem y),
      BitVec.ofNat 64 (hC s.mem y)⟩))
    (by rw [hpc]; rfl) ⟨⟨⟨?_, by rw [hx, hx0], by rw [hdf, hdf0], r0, r3, r1, r7, r6, r8, r9, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    fun S hr hq hreg2 => ?_
  · rw [hsp', mra]; decide
  · show _ = (BitVec.ofNat 64 (hP s.mem y)).toNat
    rw [e7, hsp', show (s.regs 4).toNat - 96 + 8 = (s.regs 4).toNat - 88 by omega]; exact my8
  · show _ = (BitVec.ofNat 64 (hL s.mem y)).toNat
    rw [e8, hsp', show (s.regs 4).toNat - 96 + 16 = (s.regs 4).toNat - 80 by omega]; exact my16
  · show _ = (BitVec.ofNat 64 (hC s.mem y)).toNat
    rw [e9, hsp', show (s.regs 4).toNat - 96 + 24 = (s.regs 4).toNat - 72 by omega]; exact my24
  · show MPre R b H L (W - 96) (BitVec.ofNat 64 (hP s.mem z)).toNat (BitVec.ofNat 64 (hC s.mem z)).toNat stk.toNat
      (BitVec.ofNat 64 (hP s.mem x)).toNat (BitVec.ofNat 64 (hL s.mem x)).toNat (BitVec.ofNat 64 (hC s.mem x)).toNat
      (BitVec.ofNat 64 (hP s.mem y)).toNat (BitVec.ofNat 64 (hL s.mem y)).toNat (BitVec.ofNat 64 (hC s.mem y)).toNat S1
    rw [e0, e2, e4, e5, e6, e7, e8, e9]
    exact ipre_down hpre hsp' h14 hfs hF hreg
  · show μl (BitVec.ofNat 64 (hL s.mem x)).toNat (BitVec.ofNat 64 (hL s.mem y)).toNat + 3 < n
    rw [e5, e8]; exact hμ
  · obtain ⟨⟨k4, k5, k14, kx⟩, hq⟩ := hq
    have hq' : MPost R b H L (W - 96) (BitVec.ofNat 64 (hP s.mem z)).toNat (BitVec.ofNat 64 (hC s.mem z)).toNat
        stk.toNat (BitVec.ofNat 64 (hP s.mem x)).toNat (BitVec.ofNat 64 (hL s.mem x)).toNat
        (BitVec.ofNat 64 (hC s.mem x)).toNat (BitVec.ofNat 64 (hP s.mem y)).toNat
        (BitVec.ofNat 64 (hL s.mem y)).toNat (BitVec.ofNat 64 (hC s.mem y)).toNat S1 S := hq
    rw [e0, e2, e4, e5, e6, e7, e8, e9] at hq'
    obtain ⟨p', l', c', b1, L1, hIR⟩ := ir_of hpre hra hsp' h14 hfs hdf hF m0 mbp m8 m24 m32 hq'
      (by rw [k4, hsp]; exact sp96_8 _) (k14.trans h14) (k5.trans h5) (kx.trans hx)
    refine itail impl R hwb b L W z stk.toNat x y s p' l' c' b1 L1 S hIR ?_
    rw [hr]; simp only [retAddrOf]; rw [hsp', mra]

end FvModexp.Amd64.Q.NatMul
