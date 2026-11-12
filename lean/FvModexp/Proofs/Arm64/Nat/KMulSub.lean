import FvModexp.Proofs.Arm64.Nat.KMulMath

set_option autoImplicit false

/-!
# `karatsuba` (arm64): `tx.Sub(x0, x1)` and `ty.Sub(y1, y0)` (natmul.go:208-209), `KM1 → KM2 → KM2b`

`kSub1`: from `KM1` (`0x1bc10c`) the argument setup and `CALL (*Int).Sub` (`0x1bc118`); `kSubCall1`: the call
(`kn_intcall`) and `KM2` from its postcondition. `kSub2` / `kSubCall2`: the same for `ty` (`0x1bc11c … 0x1bc128`).
Both results reuse `z`'s array (`asNeed ≤ n2 + 1 ≤ cap`): `tx` in `z[0:ltx]`, `ty` in `z[n2:n2+lty]`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.RunIface (Serves Globals)
open FvModexp.Arm64.NatSqr (StkPre StkSep IntAt apart_of_held tN' natNorm_le asCost_le_asB)

theorem ksp_sub (x : BitVec 64) {k : Nat} (h : k ≤ x.toNat) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem sgnV_lt {ng v a b B : Nat} (h : sgnV ng v = (a : Int) - (b : Int)) (ha : a < B) (hb : b < B) : v < B := by
  unfold sgnV at h; split at h <;> omega

theorem sgnV_of_intZ {M : Memory} {a ng p l c : Nat} (hh : IntAt M a ng p l c) :
    IntAS.intZ M a = sgnV ng (natVal M p l) := by
  obtain ⟨q1, q2, q3, -⟩ := hh
  simp only [IntAS.intZ, IntAS.hNeg, IntAS.hP, IntAS.hL, q1, q2, q3, sgnV]

theorem pow_half {n : Nat} : 2 ^ (64 * (n - kh n)) ≤ 2 ^ (64 * kh n) :=
  Nat.pow_le_pow_right (by decide) (by simp only [kh]; omega)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}

/-- the operand facts and value of a half `x[o:o+l]` held in a frame header `(0, xp + 8o, l, c)` -/
theorem KN.hxop (h : KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {a o l c : Nat}
    (hh : IntAt M a 0 (xp + 8 * o) l c) (hol : o + l ≤ n) (hc : c = xc - o) (hl : l ≤ 2 ^ 16)
    (hnn : NatNorm s.mem (xp + 8 * o) l) :
    KIOp R Lk s W M a ∧ IntAS.intZ M a = (natVal s.mem (xp + 8 * o) l : Int) ∧ IntAS.hP M a = xp + 8 * o ∧
      IntAS.hL M a = l := by
  obtain ⟨hacc, h48, -, -, hw, -, -, hv, hn⟩ := h.halfX hol
  have F := h.F
  have hxc := F.xcn
  have hxh := h.ext.held F.xh
  obtain ⟨q1, q2, q3, q4⟩ := hh
  refine ⟨?_, ?_, q2, q3⟩
  · simp only [KIOp, IntAS.hNeg, IntAS.hP, IntAS.hL, IntAS.hC, q1, q2, q3, q4]
    refine ⟨by omega, by omega, by have := F.xc40; omega, hl, hacc, h48, hxh.sub (by omega) (by omega), hn hnn, hw⟩
  · simp only [IntAS.intZ, IntAS.hNeg, IntAS.hP, IntAS.hL, q1, q2, q3, if_true, hv]

theorem KN.hyop (h : KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {a o l c : Nat}
    (hh : IntAt M a 0 (yp + 8 * o) l c) (hol : o + l ≤ n) (hc : c = yc - o) (hl : l ≤ 2 ^ 16)
    (hnn : NatNorm s.mem (yp + 8 * o) l) :
    KIOp R Lk s W M a ∧ IntAS.intZ M a = (natVal s.mem (yp + 8 * o) l : Int) ∧ IntAS.hP M a = yp + 8 * o ∧
      IntAS.hL M a = l := by
  obtain ⟨hacc, h48, -, -, hw, -, -, hv, hn⟩ := h.halfY hol
  have F := h.F
  have hyc := F.ycn
  have hyh := h.ext.held F.yh
  obtain ⟨q1, q2, q3, q4⟩ := hh
  refine ⟨?_, ?_, q2, q3⟩
  · simp only [KIOp, IntAS.hNeg, IntAS.hP, IntAS.hL, IntAS.hC, q1, q2, q3, q4]
    refine ⟨by omega, by omega, by have := F.yc40; omega, hl, hacc, h48, hyh.sub (by omega) (by omega), hn hnn, hw⟩
  · simp only [IntAS.intZ, IntAS.hNeg, IntAS.hP, IntAS.hL, q1, q2, q3, if_true, hv]

end

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem kSubCall1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} {S : State} (hB : KM1 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk)
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 0x1b0ab0) (hsp : S1.sp = s.sp - 448#64)
    (h28 : S1.regs 28 = s.regs 28) (h29 : S1.regs 29 = s.sp - 456#64) (h18 : S1.regs 18 = s.regs 18)
    (hra : S1.regs 30 = BitVec.ofNat 64 0x1bc11c)
    (r0 : S1.regs 0 = BitVec.ofNat 64 (s.sp.toNat - 296)) (r1 : S1.regs 1 = BitVec.ofNat 64 (s.sp.toNat - 48))
    (r2 : S1.regs 2 = BitVec.ofNat 64 (s.sp.toNat - 80)) (hm : S1.mem = S.mem)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' tng ltx : Nat),
      KM2 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' tng ltx →
      KNGoal impl R b L W st zp xp n yp s S') :
    KNGoal impl R b L W st zp xp n yp s S1 := by
  have hkm := hB.km
  rw [← hm] at hkm
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  have hsp' : S1.sp.toNat = s.sp.toNat - 448 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hl0 := hkm.l0; have hl1 := hkm.l1
  have hkh : kh n = (n + 1) / 2 := rfl
  have hkn : kh n ≤ n := by omega
  obtain ⟨hox0, hv0, hp0, hl0e⟩ := hkm.hxop (a := s.sp.toNat - 48) (o := 0) (l := lx0) (c := xc)
    (by simpa using hkm.x0h) (by omega) (by omega) (by omega) (by simpa using hkm.nn0)
  obtain ⟨hox1, hv1, hp1, hl1e⟩ := hkm.hxop (a := s.sp.toNat - 80) (o := kh n) (l := lx1) (c := xc - kh n)
    hkm.x1h (by omega) rfl (by omega) hkm.nn1
  obtain ⟨-, -, -, -, -, -, hzx0, -, -⟩ := hkm.halfX (o := 0) (l := lx0) (by omega)
  obtain ⟨-, -, -, -, -, -, hzx1, -, -⟩ := hkm.halfX (o := kh n) (l := lx1) (by omega)
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, -, -⟩ := hkm.zops
  have htx := hB.txh; rw [← hm] at htx
  obtain ⟨t1, t2, t3, t4⟩ := htx
  have hcost : IntAS.asCost lx0 lx1 ≤ bk := by
    refine hkm.cost (spent := kc1 (stLen s.mem st) n) ?_
    have h7 := kc7_le (stLen s.mem st) n
    have ha := asCost_le_asB (a := lx0) (b := lx1) (k := kT n) (by simp only [kT]; omega) (by simp only [kT]; omega)
    unfold kc7 kc6 kc5 kc4 kc3 kc2b kc2 at h7; omega
  refine kn_intcall impl hap R hmk hmv hwb hkm true S1 hpc hsp' h28 rfl (i := 171) (by decide) hra r0 r1 r2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by unfold Apart; omega))
    (by unfold Apart; omega) hox0 hox1 ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [IntAS.hC, t4]; exact hzc40
  · simp only [IntAS.hP, IntAS.hC, t2, t4]; exact hzlive
  · simp only [IntAS.hP, IntAS.hC, t2, t4]; exact hzw
  · intro _
    simp only [IntAS.hP, IntAS.hC, IntAS.hL, t2, t4, hp0, hl0e, hp1, hl1e]
    exact ⟨hzg, Or.inr (by simpa using hzx0), Or.inr hzx1⟩
  · simp only [hl0e, hl1e]; exact hcost
  intro s2 hpc2 hreg2 hk hq
  obtain ⟨-, hval, hng, hcan, hnn, -, hlmax, -, L', b', hext, hbud, hinv, -, -, hreuse, hF, hLF⟩ := hq
  simp only [IntAS.hP, IntAS.hC, IntAS.hL, t2, t4, hl0e, hl1e] at hF hLF hreuse hlmax hbud
  have hre := hreuse (by unfold IntAS.asNeed; split <;> omega)
  rw [hv0, hv1] at hval
  rw [h28] at hinv
  have hkm2 := (hkm.intStep (S1 := S1) hsp' (z := s.sp.toNat - 296) (q := zp) (w := min (max lx0 lx1 + 1) zc)
    (Or.inl ⟨by omega, by omega⟩) (Or.inl ⟨Nat.le_refl _, by omega⟩) hF hLF hreg2 hext hbud hinv).weaken
    (spent' := kc2 (stLen s.mem st) n) (by
      have ha := asCost_le_asB (a := lx0) (b := lx1) (k := kT n) (by simp only [kT]; omega)
        (by simp only [kT]; omega)
      unfold kc2; omega)
  have hF' := hF
  simp only [winA, hsp'] at hF'
  have hk1 : ∀ x m, s.sp.toNat - 368 ≤ x → x + m ≤ s.sp.toNat + 72 → (x + m ≤ s.sp.toNat - 296 ∨
      s.sp.toNat - 264 ≤ x) → s2.mem.readLE x m = S1.mem.readLE x m :=
    fun x m h1 h2 h3 => hkm.rdW (k := 4560) (a := 32) (by omega) (by omega) hF' h1 h2
      (by have := hzw; simp only [win, outside_cons, outside_nil, and_true] at this
          simp only [outside_cons, outside_nil, and_true]; omega)
  have hX0 := natVal_lt s.mem (xp + 8 * 0) lx0
  have hX1 := natVal_lt s.mem (xp + 8 * kh n) lx1
  have hp1' : 2 ^ (64 * lx0) ≤ 2 ^ (64 * kh n) := Nat.pow_le_pow_right (by decide) (by omega)
  have hp2' : 2 ^ (64 * lx1) ≤ 2 ^ (64 * kh n) := Nat.pow_le_pow_right (by decide) (by omega)
  have htv : sgnV (IntAS.hNeg s2.mem (s.sp.toNat - 296)) (natVal s2.mem zp (IntAS.hL s2.mem (s.sp.toNat - 296))) =
      (kX0 s xp n : Int) - (kX1 s xp n : Int) := by
    have e := hval; simp only [IntAS.resZ, ↓reduceIte] at e
    have e2 : natVal s.mem (xp + 8 * 0) lx0 = kX0 s xp n := by simpa using hkm.v0
    have e3 : natVal s.mem (xp + 8 * kh n) lx1 = kX1 s xp n := hkm.v1
    rw [e2, e3] at e
    rw [← e]; simp only [IntAS.intZ, sgnV, IntAS.hNeg, IntAS.hP, IntAS.hL, hre.1]
  have hsl : natVal s2.mem zp (IntAS.hL s2.mem (s.sp.toNat - 296)) < 2 ^ (64 * kh n) := by
    refine sgnV_lt (B := 2 ^ (64 * kh n)) htv ?_ ?_
    · have := natVal_lt s.mem xp (kh n); exact this
    · exact Nat.lt_of_lt_of_le (natVal_lt s.mem (xp + 8 * kh n) (n - kh n)) pow_half
  simp only [IntAS.hP, IntAS.hL] at hnn
  rw [hre.1] at hnn
  refine hK s2 L' b' _ _ ⟨⟨by rw [hpc2, hra], by rw [hk.1, hsp], by rw [hk.2.1, h28], by rw [hk.2.2.1, h29],
    by rw [hk.2.2.2, h18]⟩, hkm2, ?_, ⟨rfl, hre.1, rfl, hre.2⟩, hng, hcan, natNorm_le hnn hsl, htv, hnn, ?_, ?_, ?_⟩
  · have := hB.z1h; rw [← hm] at this
    exact this.keep fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))
  · have := hB.tyh; rw [← hm] at this
    exact this.keep fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inl (by omega))
  · have := hB.z0h; rw [← hm] at this
    exact NatSqr.IntAt.keep this fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))
  · have := hB.z2h; rw [← hm] at this
    exact NatSqr.IntAt.keep this fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`KM1 → KM2`**: `R0..R2 = tx, x0, x1` and the `CALL (*Int).Sub` (`0x1bc10c … 0x1bc118`), then `kSubCall1` -/
theorem kSub1 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} (S : State)
    (hB : KM1 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' tng ltx : Nat),
      KM2 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' tng ltx →
      KNGoal impl R b L W st zp xp n yp s S') :
    KNGoal impl R b L W st zp xp n yp s S := by
  have hlay := hB.km.lay
  obtain ⟨hW, hWs, hal, ha48, -⟩ := hlay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  unfold KNGoal
  janus_run until [0x1b0ab0]
  refine kSubCall1 impl hap R hmk hmv hwb hB _ (by rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl hK
  all_goals janus_simp
  all_goals exact ksp_sub _ (by omega)


set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem kSubCall2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk tng ltx : Nat} {S : State}
    (hB : KM2 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk tng ltx)
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 0x1b0ab0) (hsp : S1.sp = s.sp - 448#64)
    (h28 : S1.regs 28 = s.regs 28) (h29 : S1.regs 29 = s.sp - 456#64) (h18 : S1.regs 18 = s.regs 18)
    (hra : S1.regs 30 = BitVec.ofNat 64 0x1bc12c)
    (r0 : S1.regs 0 = BitVec.ofNat 64 (s.sp.toNat - 328)) (r1 : S1.regs 1 = BitVec.ofNat 64 (s.sp.toNat - 144))
    (r2 : S1.regs 2 = BitVec.ofNat 64 (s.sp.toNat - 112)) (hm : S1.mem = S.mem)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' yng lty : Nat),
      KM2b R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' tng ltx yng lty →
      KNGoal impl R b L W st zp xp n yp s S') :
    KNGoal impl R b L W st zp xp n yp s S1 := by
  have hkm := hB.km
  rw [← hm] at hkm
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  have hsp' : S1.sp.toNat = s.sp.toNat - 448 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hl0 := hkm.m0; have hl1 := hkm.m1
  have hkh : kh n = (n + 1) / 2 := rfl
  have hkn : kh n ≤ n := by omega
  have hlx := hB.hltx
  obtain ⟨hox0, hv0, hp0, hl0e⟩ := hkm.hyop (a := s.sp.toNat - 112) (o := 0) (l := ly0) (c := yc)
    (by simpa using hkm.y0h) (by omega) (by omega) (by omega) (by simpa using hkm.mn0)
  obtain ⟨hox1, hv1, hp1, hl1e⟩ := hkm.hyop (a := s.sp.toNat - 144) (o := kh n) (l := ly1) (c := yc - kh n)
    hkm.y1h (by omega) rfl (by omega) hkm.mn1
  obtain ⟨-, -, -, -, -, -, hzx0, -, -⟩ := hkm.halfY (o := 0) (l := ly0) (by omega)
  obtain ⟨-, -, -, -, -, -, hzx1, -, -⟩ := hkm.halfY (o := kh n) (l := ly1) (by omega)
  obtain ⟨-, -, -, -, -, -, hzlive, hzw, hzg, -⟩ := hkm.partZ (o := kh n) (l := kh n) (by omega)
  obtain ⟨-, -, hzw0, -, -, -, -, hzh0, -⟩ := hkm.zops
  have hty := hB.tyh; rw [← hm] at hty
  obtain ⟨t1, t2, t3, t4⟩ := hty
  have hcost : IntAS.asCost ly1 ly0 ≤ bk := by
    refine hkm.cost (spent := kc2 (stLen s.mem st) n) ?_
    have h7 := kc7_le (stLen s.mem st) n
    have ha := asCost_le_asB (a := ly1) (b := ly0) (k := kT n) (by simp only [kT]; omega) (by simp only [kT]; omega)
    unfold kc7 kc6 kc5 kc4 kc3 kc2b at h7; omega
  refine kn_intcall impl hap R hmk hmv hwb hkm true S1 hpc hsp' h28 rfl (i := 175) (by decide) hra r0 r1 r2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by unfold Apart; omega))
    (by unfold Apart; omega) hox1 hox0 ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [IntAS.hC, t4]; omega
  · simp only [IntAS.hP, IntAS.hC, t2, t4]; exact hzlive
  · simp only [IntAS.hP, IntAS.hC, t2, t4]; exact hzw
  · intro _
    simp only [IntAS.hP, IntAS.hC, IntAS.hL, t2, t4, hp0, hl0e, hp1, hl1e]
    refine ⟨hzg, Or.inr ?_, Or.inr ?_⟩
    · unfold Apart at hzx1 ⊢; omega
    · have := hzx0; simp only [Nat.mul_zero, Nat.add_zero] at this; unfold Apart at this ⊢; omega
  · simp only [hl0e, hl1e]; exact hcost
  intro s2 hpc2 hreg2 hk hq
  obtain ⟨-, hval, hng, -, hnn, -, hlmax, -, L', b', hext, hbud, hinv, -, -, hreuse, hF, hLF⟩ := hq
  simp only [IntAS.hP, IntAS.hC, IntAS.hL, t2, t4, hl0e, hl1e] at hF hLF hreuse hlmax hbud
  have hre := hreuse (by unfold IntAS.asNeed; split <;> omega)
  rw [hv0, hv1] at hval
  rw [h28] at hinv
  have hkm2 := (hkm.intStep (S1 := S1) hsp' (z := s.sp.toNat - 328) (q := zp + 8 * kh n)
    (w := min (max ly1 ly0 + 1) (zc - kh n))
    (Or.inl ⟨by omega, by omega⟩) (Or.inl ⟨by omega, by omega⟩) hF hLF hreg2 hext hbud hinv).weaken
    (spent' := kc2b (stLen s.mem st) n) (by
      have ha := asCost_le_asB (a := ly1) (b := ly0) (k := kT n) (by simp only [kT]; omega)
        (by simp only [kT]; omega)
      unfold kc2b; omega)
  have hF' := hF
  simp only [winA, hsp'] at hF'
  have hk1 : ∀ x m, s.sp.toNat - 368 ≤ x → x + m ≤ s.sp.toNat + 72 → (x + m ≤ s.sp.toNat - 328 ∨
      s.sp.toNat - 296 ≤ x) → s2.mem.readLE x m = S1.mem.readLE x m :=
    fun x m h1 h2 h3 => hkm.rdW (k := 4560) (a := 32) (by omega) (by omega) hF' h1 h2
      (by have := hzw0; simp only [win, outside_cons, outside_nil, and_true] at this
          simp only [outside_cons, outside_nil, and_true]; omega)
  have hkz : ∀ a m, zp ≤ a → a + m ≤ zp + 8 * kh n → s2.mem.readLE a m = S1.mem.readLE a m := by
    intro a m h1 h2
    refine hkm.keepH hsp' (k := 4560) (a := 32) (by omega) (by omega) hF hLF (hzh0.sub h1 (by omega))
      (hzw0.of_sub h1 (by omega)) ?_
    have := hzw0; simp only [win, outside_cons, outside_nil, and_true] at this
    simp only [outside_cons, outside_nil, and_true]; omega
  have hp1' : 2 ^ (64 * ly0) ≤ 2 ^ (64 * kh n) := Nat.pow_le_pow_right (by decide) (by omega)
  have hp2' : 2 ^ (64 * ly1) ≤ 2 ^ (64 * kh n) := Nat.pow_le_pow_right (by decide) (by omega)
  have hyv : sgnV (IntAS.hNeg s2.mem (s.sp.toNat - 328))
      (natVal s2.mem (zp + 8 * kh n) (IntAS.hL s2.mem (s.sp.toNat - 328))) =
      (kX1 s yp n : Int) - (kX0 s yp n : Int) := by
    have e := hval; simp only [IntAS.resZ, ↓reduceIte] at e
    have e2 : natVal s.mem (yp + 8 * 0) ly0 = kX0 s yp n := by simpa using hkm.w0
    have e3 : natVal s.mem (yp + 8 * kh n) ly1 = kX1 s yp n := hkm.w1
    rw [e2, e3] at e
    rw [← e]; simp only [IntAS.intZ, sgnV, IntAS.hNeg, IntAS.hP, IntAS.hL, hre.1]
  have hsl : natVal s2.mem (zp + 8 * kh n) (IntAS.hL s2.mem (s.sp.toNat - 328)) < 2 ^ (64 * kh n) := by
    refine sgnV_lt (B := 2 ^ (64 * kh n)) hyv ?_ ?_
    · exact Nat.lt_of_lt_of_le (natVal_lt s.mem (yp + 8 * kh n) (n - kh n)) pow_half
    · exact natVal_lt s.mem yp (kh n)
  simp only [IntAS.hP, IntAS.hL] at hnn
  rw [hre.1] at hnn
  have htv : natVal s2.mem zp ltx = natVal S1.mem zp ltx := by
    unfold natVal; exact hkz _ _ (Nat.le_refl _) (by omega)
  have htn : NatNorm s2.mem zp ltx := by
    have := hB.tnn; rw [← hm] at this
    rcases this with h0 | h0
    · exact Or.inl h0
    · by_cases hl0 : ltx = 0
      · exact Or.inl hl0
      · right; rwa [hkz _ _ (by omega) (by omega)]
  have htv0 := hB.tv; rw [← hm] at htv0
  refine hK s2 L' b' _ _ ⟨⟨by rw [hpc2, hra], by rw [hk.1, hsp], by rw [hk.2.1, h28], by rw [hk.2.2.1, h29],
    by rw [hk.2.2.2, h18]⟩, hkm2, ?_, ?_, hB.htng, hlx, by rw [htv]; exact htv0, htn, ⟨rfl, hre.1, rfl, hre.2⟩, hng,
    natNorm_le hnn hsl, hyv, hnn, ?_, ?_⟩
  · have := hB.z1h; rw [← hm] at this
    exact this.keep fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))
  · have := hB.txh; rw [← hm] at this
    exact this.keep fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))
  · have := hB.z0h; rw [← hm] at this
    exact NatSqr.IntAt.keep this fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))
  · have := hB.z2h; rw [← hm] at this
    exact NatSqr.IntAt.keep this fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`KM2 → KM2b`**: `R0..R2 = ty, y1, y0` and the `CALL (*Int).Sub` (`0x1bc11c … 0x1bc128`), then `kSubCall2` -/
theorem kSub2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk tng ltx : Nat} (S : State)
    (hB : KM2 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk tng ltx)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' yng lty : Nat),
      KM2b R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' tng ltx yng lty →
      KNGoal impl R b L W st zp xp n yp s S') :
    KNGoal impl R b L W st zp xp n yp s S := by
  have hlay := hB.km.lay
  obtain ⟨hW, hWs, hal, ha48, -⟩ := hlay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  unfold KNGoal
  janus_run until [0x1b0ab0]
  refine kSubCall2 impl hap R hmk hmv hwb hB _ (by rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl hK
  all_goals janus_simp
  all_goals exact ksp_sub _ (by omega)

end FvModexp.Arm64.NatMul
