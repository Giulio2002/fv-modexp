import FvModexp.Proofs.Amd64.NatQ.KMulMath
import FvModexp.Proofs.Amd64.NatQ.KMulI

set_option autoImplicit false

/-!
# [amd64 port (divmc s50) of the Q-form Arm64/NatQ/KMulSub.lean — TIGHT COSTS] `karatsuba` (amd64): `tx.Sub(x0, x1)` and `ty.Sub(y1, y0)` (natmul.go:208-209), `KM1 → KM2 → KM2b`

`kSub1`: from `KM1` (`0x5f2149`) `AX, BX, CX = &tx, &x0, &x1` and the `CALL (*Int).Sub` (return `0x5f2166` pushed at
`RSP - 456`), then `kSubCall1` (`kn_intcall`) to `KM2`; `kSub2`: from `KM2` (`0x5f2166`) `&ty, &y1, &y0` and the call
(return `0x5f2185`), then `kSubCall2` to `KM2b`. (Mechanics: this repo's amd64 `KSqrSub`.)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep IntAt apart_of_held tN' natNorm_le asCost_le_asB tls pushRd)

theorem ksp_sub (x : BitVec 64) {k : Nat} (h : k ≤ x.toNat) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem sgnV_lt {ng v a b B : Nat} (h : sgnV ng v = (a : Int) - (b : Int)) (ha : a < B) (hb : b < B) : v < B := by
  unfold sgnV at h; split at h <;> omega

theorem pow_half {n : Nat} : 2 ^ (64 * (n - kh n)) ≤ 2 ^ (64 * kh n) :=
  Nat.pow_le_pow_right (by decide) (by simp only [kh]; omega)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}

/-- the operand facts and value of a half `x[o:o+l]` held in a frame header `(0, xp + 8o, l, c)` -/
theorem KN.hxop (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {a o l c : Nat}
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

theorem KN.hyop (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {a o l c : Nat}
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
theorem kSubCall1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} {S : State} (hB : KM1 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 (IntAS.entry true)) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456)
    (h14 : S1.regs 14 = s.regs 14) (h5 : S1.regs 5 = s.regs 4 - 8#64) (hfs : S1.fsBase = s.fsBase)
    (hdf : S1.df = s.df) (hx15 : S1.xmm 15 = s.xmm 15)
    (hm : S1.mem = S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2166)
    (r0 : S1.regs 0 = BitVec.ofNat 64 ((s.regs 4).toNat - 296)) (r1 : S1.regs 3 = BitVec.ofNat 64 ((s.regs 4).toNat - 48))
    (r2 : S1.regs 1 = BitVec.ofNat 64 ((s.regs 4).toNat - 80))
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' tng ltx : Nat),
      KM2 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' tng ltx →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S1 := by
  have hkm := hB.km.push 0x5f2166
  rw [← hm] at hkm
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  have hl0 := hkm.l0; have hl1 := hkm.l1
  have hkh : kh n = (n + 1) / 2 := rfl
  have hkn : kh n ≤ n := by omega
  obtain ⟨hox0, hv0, hp0, hl0e⟩ := hkm.hxop (a := (s.regs 4).toNat - 48) (o := 0) (l := lx0) (c := xc)
    (by simpa using hkm.x0h) (by omega) (by omega) (by omega) (by simpa using hkm.nn0)
  obtain ⟨hox1, hv1, hp1, hl1e⟩ := hkm.hxop (a := (s.regs 4).toNat - 80) (o := kh n) (l := lx1) (c := xc - kh n)
    hkm.x1h (by omega) rfl (by omega) hkm.nn1
  obtain ⟨-, -, -, -, -, -, hzx0, -, -⟩ := hkm.halfX (o := 0) (l := lx0) (by omega)
  obtain ⟨-, -, -, -, -, -, hzx1, -, -⟩ := hkm.halfX (o := kh n) (l := lx1) (by omega)
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, -, -⟩ := hkm.zops
  obtain ⟨-, hzt⟩ := hkm.ttls
  have htx : IntAt S1.mem ((s.regs 4).toNat - 296) 0 zp (kh n) zc := by
    rw [hm]; exact IntAt.pushK hB.txh (by omega) (by omega)
  obtain ⟨t1, t2, t3, t4⟩ := htx
  have hcs1 : kc1 n + IntAS.asCost lx0 lx1 ≤ KCQ n := by
    have h7 := kc7_le n
    have ha := asCost_le_asB (a := lx0) (b := lx1) (k := kT n) (by simp only [kT]; omega) (by simp only [kT]; omega)
    unfold kc7 kc6 kc5 kc4 kc3 kc2b kc2 at h7; omega
  have hcost : IntAS.asCost lx0 lx1 ≤ bk := hkm.cost hcs1
  have hrd : S1.mem.readLE (S1.regs 4).toNat 8 = 0x5f1da0 + 966 := by
    rw [hm, hsp, Janus.Arm64.Memory.readLE_writeLE_self]
  refine kn_intcall impl hap R hmk hmv hwb hkm true S1 hpc hsp h14 rfl hfs (i := 966) (by decide) hrd
    (hx15.trans hx150) (hdf.trans hdf0) r0 r1 r2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by unfold Apart; omega))
    (by unfold Apart; omega) hox0 hox1 ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [IntAS.hC, t4]; exact hzc40
  · simp only [IntAS.hP, IntAS.hC, t2, t4]; exact hzlive
  · simp only [IntAS.hP, IntAS.hC, t2, t4]; exact hzw
  · intro _
    simp only [IntAS.hP, IntAS.hC, IntAS.hL, t2, t4, hp0, hl0e, hp1, hl1e]
    exact ⟨hzg, hzt, Or.inr (by simpa using hzx0), Or.inr hzx1⟩
  · simp only [hl0e, hl1e]; exact hcost
  intro s2 hpc2 hreg2 hk hq
  obtain ⟨efs, edf, -, hval, hng, hcan, hnn, -, hlmax, -, L', b', hext, hbud, hinv, -, -, hreuse, hF, hLF⟩ := hq
  simp only [IntAS.hP, IntAS.hC, IntAS.hL, t2, t4, hl0e, hl1e] at hF hLF hreuse hlmax hbud
  have hre := hreuse (by unfold IntAS.asNeed; split <;> omega)
  rw [hv0, hv1] at hval
  rw [h14] at hinv
  have hkm2 := (hkm.intStep (S1 := S1) hsp (z := (s.regs 4).toNat - 296) (q := zp) (w := min (max lx0 lx1 + 1) zc)
    (Or.inl ⟨by omega, by omega⟩) (Or.inl ⟨Nat.le_refl _, by omega⟩) hF hLF hreg2 hext hbud hcs1 hinv).weaken
    (spent' := kc2 n) (by
      have ha := asCost_le_asB (a := lx0) (b := lx1) (k := kT n) (by simp only [kT]; omega)
        (by simp only [kT]; omega)
      unfold kc2; omega) (by have h7 := kc7_le n; unfold kc7 kc6 kc5 kc4 kc3 kc2b at h7; omega)
  have hF' := hF
  simp only [win, hsp] at hF'
  have hk1 : ∀ x m, (s.regs 4).toNat - 376 ≤ x → x + m ≤ (s.regs 4).toNat + 72 → (x + m ≤ (s.regs 4).toNat - 296 ∨
      (s.regs 4).toNat - 264 ≤ x) → s2.mem.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 h3 => (hkm.rdW (k := 4536) (a := 32) (by omega) (by omega) hF' h1 h2
      (by have := hzw; simp only [win, outside_cons, outside_nil, and_true] at this
          simp only [outside_cons, outside_nil, and_true]; omega)).trans (by rw [hm]; exact pushRd (by omega))
  have htv : sgnV (IntAS.hNeg s2.mem ((s.regs 4).toNat - 296))
      (natVal s2.mem zp (IntAS.hL s2.mem ((s.regs 4).toNat - 296))) = (kX0 s xp n : Int) - (kX1 s xp n : Int) := by
    have e := hval; simp only [IntAS.resZ, ↓reduceIte] at e
    have e2 : natVal s.mem (xp + 8 * 0) lx0 = kX0 s xp n := by simpa using hkm.v0
    have e3 : natVal s.mem (xp + 8 * kh n) lx1 = kX1 s xp n := hkm.v1
    rw [e2, e3] at e
    rw [← e]; simp only [IntAS.intZ, sgnV, IntAS.hNeg, IntAS.hP, IntAS.hL, hre.1]
  have hsl : natVal s2.mem zp (IntAS.hL s2.mem ((s.regs 4).toNat - 296)) < 2 ^ (64 * kh n) := by
    refine sgnV_lt (B := 2 ^ (64 * kh n)) htv ?_ ?_
    · exact natVal_lt s.mem xp (kh n)
    · exact Nat.lt_of_lt_of_le (natVal_lt s.mem (xp + 8 * kh n) (n - kh n)) pow_half
  simp only [IntAS.hP, IntAS.hL] at hnn
  rw [hre.1] at hnn
  obtain ⟨hpcB, hspB, h14B, h5B, hfsB, hdfB, hx15B⟩ := hB.pos
  refine hK s2 L' b' _ _ ⟨⟨by rw [hpc2], by rw [hk.1]; exact sp_add8K hsp (by omega), hk.2.2.1.trans h14,
    hk.2.1.trans h5, efs.trans hfs, edf.trans hdf, hk.2.2.2.trans hx15⟩, hkm2, ?_, ⟨rfl, hre.1, rfl, hre.2⟩, hng, hcan,
    natNorm_le hnn hsl, htv, hnn, ?_, ?_, ?_⟩
  · exact hB.z1h.keep fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))
  · exact hB.tyh.keep fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inl (by omega))
  · exact NatSqr.IntAt.keep hB.z0h fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))
  · exact NatSqr.IntAt.keep hB.z2h fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`KM1 → KM2`**: `AX, BX, CX = &tx, &x0, &x1` and the `CALL (*Int).Sub` (`0x5f2149 … 0x5f2161`), then `kSubCall1` -/
theorem kSub1 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (S : State)
    (hB : KM1 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' tng ltx : Nat),
      KM2 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' tng ltx →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S := by
  obtain ⟨hW, hWs, hal, ha48, -⟩ := hB.km.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := hB.km.F.env.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 456) 528 true = true := by
    rw [hB.km.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 448 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold KNGoal
  janus64_run [hsp'] until [0x5e2800]
  refine kSubCall1 impl hap R hmk hmv hwb hB hx150 hdf0 _ (by rfl) ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ hK
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega | exact ksp_sub _ (by omega)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem kSubCall2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk tng ltx : Nat} {S : State}
    (hB : KM2 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk tng ltx)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 (IntAS.entry true)) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456)
    (h14 : S1.regs 14 = s.regs 14) (h5 : S1.regs 5 = s.regs 4 - 8#64) (hfs : S1.fsBase = s.fsBase)
    (hdf : S1.df = s.df) (hx15 : S1.xmm 15 = s.xmm 15)
    (hm : S1.mem = S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f2185)
    (r0 : S1.regs 0 = BitVec.ofNat 64 ((s.regs 4).toNat - 328)) (r1 : S1.regs 3 = BitVec.ofNat 64 ((s.regs 4).toNat - 144))
    (r2 : S1.regs 1 = BitVec.ofNat 64 ((s.regs 4).toNat - 112))
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' yng lty : Nat),
      KM2b R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' tng ltx yng lty →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S1 := by
  have hkm := hB.km.push 0x5f2185
  rw [← hm] at hkm
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  have hl0 := hkm.m0; have hl1 := hkm.m1
  have hkh : kh n = (n + 1) / 2 := rfl
  have hkn : kh n ≤ n := by omega
  have hlx := hB.hltx
  obtain ⟨hox0, hv0, hp0, hl0e⟩ := hkm.hyop (a := (s.regs 4).toNat - 112) (o := 0) (l := ly0) (c := yc)
    (by simpa using hkm.y0h) (by omega) (by omega) (by omega) (by simpa using hkm.mn0)
  obtain ⟨hox1, hv1, hp1, hl1e⟩ := hkm.hyop (a := (s.regs 4).toNat - 144) (o := kh n) (l := ly1) (c := yc - kh n)
    hkm.y1h (by omega) rfl (by omega) hkm.mn1
  obtain ⟨-, -, -, -, -, -, hzx0, -, -⟩ := hkm.halfY (o := 0) (l := ly0) (by omega)
  obtain ⟨-, -, -, -, -, -, hzx1, -, -⟩ := hkm.halfY (o := kh n) (l := ly1) (by omega)
  obtain ⟨-, -, -, -, -, -, hzlive, hzw, hzg, -⟩ := hkm.partZ (o := kh n) (l := kh n) (by omega)
  obtain ⟨-, -, hzw0, -, -, -, -, hzh0, -⟩ := hkm.zops
  obtain ⟨-, hzt0⟩ := hkm.ttls
  have hty : IntAt S1.mem ((s.regs 4).toNat - 328) 0 (zp + 8 * kh n) (kh n) (zc - kh n) := by
    rw [hm]; exact IntAt.pushK hB.tyh (by omega) (by omega)
  obtain ⟨t1, t2, t3, t4⟩ := hty
  have hcs2 : kc2 n + IntAS.asCost ly1 ly0 ≤ KCQ n := by
    have h7 := kc7_le n
    have ha := asCost_le_asB (a := ly1) (b := ly0) (k := kT n) (by simp only [kT]; omega) (by simp only [kT]; omega)
    unfold kc7 kc6 kc5 kc4 kc3 kc2b at h7; omega
  have hcost : IntAS.asCost ly1 ly0 ≤ bk := hkm.cost hcs2
  have hrd : S1.mem.readLE (S1.regs 4).toNat 8 = 0x5f1da0 + 997 := by
    rw [hm, hsp, Janus.Arm64.Memory.readLE_writeLE_self]
  refine kn_intcall impl hap R hmk hmv hwb hkm true S1 hpc hsp h14 rfl hfs (i := 997) (by decide) hrd
    (hx15.trans hx150) (hdf.trans hdf0) r0 r1 r2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by unfold Apart; omega))
    (by unfold Apart; omega) hox1 hox0 ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [IntAS.hC, t4]; omega
  · simp only [IntAS.hP, IntAS.hC, t2, t4]; exact hzlive
  · simp only [IntAS.hP, IntAS.hC, t2, t4]; exact hzw
  · intro _
    simp only [IntAS.hP, IntAS.hC, IntAS.hL, t2, t4, hp0, hl0e, hp1, hl1e]
    refine ⟨hzg, ?_, Or.inr ?_, Or.inr ?_⟩
    · unfold Apart at hzt0 ⊢; omega
    · unfold Apart at hzx1 ⊢; omega
    · have := hzx0; simp only [Nat.mul_zero, Nat.add_zero] at this; unfold Apart at this ⊢; omega
  · simp only [hl0e, hl1e]; exact hcost
  intro s2 hpc2 hreg2 hk hq
  obtain ⟨efs, edf, -, hval, hng, -, hnn, -, hlmax, -, L', b', hext, hbud, hinv, -, -, hreuse, hF, hLF⟩ := hq
  simp only [IntAS.hP, IntAS.hC, IntAS.hL, t2, t4, hl0e, hl1e] at hF hLF hreuse hlmax hbud
  have hre := hreuse (by unfold IntAS.asNeed; split <;> omega)
  rw [hv0, hv1] at hval
  rw [h14] at hinv
  have hkm2 := (hkm.intStep (S1 := S1) hsp (z := (s.regs 4).toNat - 328) (q := zp + 8 * kh n)
    (w := min (max ly1 ly0 + 1) (zc - kh n))
    (Or.inl ⟨by omega, by omega⟩) (Or.inl ⟨by omega, by omega⟩) hF hLF hreg2 hext hbud hcs2 hinv).weaken
    (spent' := kc2b n) (by
      have ha := asCost_le_asB (a := ly1) (b := ly0) (k := kT n) (by simp only [kT]; omega)
        (by simp only [kT]; omega)
      unfold kc2b; omega) (by have h7 := kc7_le n; unfold kc7 kc6 kc5 kc4 kc3 at h7; omega)
  have hF' := hF
  simp only [win, hsp] at hF'
  have hk1 : ∀ x m, (s.regs 4).toNat - 376 ≤ x → x + m ≤ (s.regs 4).toNat + 72 → (x + m ≤ (s.regs 4).toNat - 328 ∨
      (s.regs 4).toNat - 296 ≤ x) → s2.mem.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 h3 => (hkm.rdW (k := 4536) (a := 32) (by omega) (by omega) hF' h1 h2
      (by have := hzw0; simp only [win, outside_cons, outside_nil, and_true] at this
          simp only [outside_cons, outside_nil, and_true]; omega)).trans (by rw [hm]; exact pushRd (by omega))
  have hkz : ∀ a m, zp ≤ a → a + m ≤ zp + 8 * kh n → s2.mem.readLE a m = S.mem.readLE a m := by
    intro a m h1 h2
    refine (hkm.keepH hsp (k := 4536) (a := 32) (by omega) (by omega) hF hLF (hzh0.sub h1 (by omega))
      (hzw0.of_sub h1 (by omega)) ?_).trans (by
        rw [hm]; have := hzw0; simp only [win, outside_cons, outside_nil, and_true] at this
        exact pushRd (by omega))
    have := hzw0; simp only [win, outside_cons, outside_nil, and_true] at this
    simp only [outside_cons, outside_nil, and_true]; omega
  have hyv : sgnV (IntAS.hNeg s2.mem ((s.regs 4).toNat - 328))
      (natVal s2.mem (zp + 8 * kh n) (IntAS.hL s2.mem ((s.regs 4).toNat - 328))) =
      (kX1 s yp n : Int) - (kX0 s yp n : Int) := by
    have e := hval; simp only [IntAS.resZ, ↓reduceIte] at e
    have e2 : natVal s.mem (yp + 8 * 0) ly0 = kX0 s yp n := by simpa using hkm.w0
    have e3 : natVal s.mem (yp + 8 * kh n) ly1 = kX1 s yp n := hkm.w1
    rw [e2, e3] at e
    rw [← e]; simp only [IntAS.intZ, sgnV, IntAS.hNeg, IntAS.hP, IntAS.hL, hre.1]
  have hsl : natVal s2.mem (zp + 8 * kh n) (IntAS.hL s2.mem ((s.regs 4).toNat - 328)) < 2 ^ (64 * kh n) := by
    refine sgnV_lt (B := 2 ^ (64 * kh n)) hyv ?_ ?_
    · exact Nat.lt_of_lt_of_le (natVal_lt s.mem (yp + 8 * kh n) (n - kh n)) pow_half
    · exact natVal_lt s.mem yp (kh n)
  simp only [IntAS.hP, IntAS.hL] at hnn
  rw [hre.1] at hnn
  have htv : natVal s2.mem zp ltx = natVal S.mem zp ltx := by
    unfold natVal; exact hkz _ _ (Nat.le_refl _) (by omega)
  have htn : NatNorm s2.mem zp ltx := by
    rcases hB.tnn with h0 | h0
    · exact Or.inl h0
    · by_cases hl0 : ltx = 0
      · exact Or.inl hl0
      · right; rwa [hkz _ _ (by omega) (by omega)]
  refine hK s2 L' b' _ _ ⟨⟨by rw [hpc2], by rw [hk.1]; exact sp_add8K hsp (by omega), hk.2.2.1.trans h14,
    hk.2.1.trans h5, efs.trans hfs, edf.trans hdf, hk.2.2.2.trans hx15⟩, hkm2, ?_, ?_, hB.htng, hlx,
    by rw [htv]; exact hB.tv, htn, ⟨rfl, hre.1, rfl, hre.2⟩, hng, natNorm_le hnn hsl, hyv, hnn, ?_, ?_⟩
  · exact hB.z1h.keep fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))
  · exact hB.txh.keep fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))
  · exact NatSqr.IntAt.keep hB.z0h fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))
  · exact NatSqr.IntAt.keep hB.z2h fun x m h1 h2 => hk1 x m (by omega) (by omega) (Or.inr (by omega))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`KM2 → KM2b`**: `AX, BX, CX = &ty, &y1, &y0` and the `CALL (*Int).Sub` (`0x5f2166 … 0x5f2180`), then `kSubCall2` -/
theorem kSub2 (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk tng ltx : Nat} (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (S : State)
    (hB : KM2 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk tng ltx)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' yng lty : Nat),
      KM2b R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S' Lk' bk' tng ltx yng lty →
      KNGoal impl R H b L W st zp xp n yp s S') :
    KNGoal impl R H b L W st zp xp n yp s S := by
  obtain ⟨hW, hWs, hal, ha48, -⟩ := hB.km.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := hB.km.F.env.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 456) 528 true = true := by
    rw [hB.km.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 448 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold KNGoal
  janus64_run [hsp'] until [0x5e2800]
  refine kSubCall2 impl hap R hmk hmv hwb hB hx150 hdf0 _ (by rfl) ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ hK
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega | exact ksp_sub _ (by omega)

end FvModexp.Amd64.Q.NatMul
