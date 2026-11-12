import FvModexp.Proofs.Arm64.Exp.SlowKE

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the two loop exits into the word test `IT` (agent expmc)

* `exitU`: `T1` with `j = w` (`CMP R14, R13; BGE` → `fnE + 0x358`: `SUB $2, R8` (`R8 = len y`), `JMP` → `IT`):
  `IT` with `t = len y - 1` (nat.go:749, 766);
* `exitL`: `T2` with `j = 64` (`CMP $64, R13; BGE` → `fnE + 0x360`: `SUB $1, R8` (`R8 = i`) → `IT`): `IT` with `t = i`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

theorem sub2 (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 2#64 = BitVec.ofNat 64 (n - 1) - 1#64 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the upper loop's exit** -/
theorem exitU {impl : List Segment} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : BitVec 64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KT1 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 w w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc)
    (KXE : ∀ S' : State, yl - 1 = 0 →
      KE R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 z zl zc' Zv zz zzl zzc r rl rc q ql qc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KX2 : ∀ (S' : State) (i : Nat) (v : BitVec 64), yl - 1 = i + 1 → v.toNat = Exp.wd (natVal s.mem yp yl) i →
      KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 0 i v z zl zc' Zv zz zzl zzc
        r rl rc q ql qc → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hyl : yl ≤ 2 ^ 9 := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyl0 : 0 < yl := hP.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := hk.w63
  have hjc := hk.jc; have hB := hk.bb; have hzl := hk.zl128
  have epc := hk.pc; have e0 := hk.e0; have e5 := hk.e5; have e2 := hk.e2; have e24 := hk.e24; have e23 := hk.e23
  have e22 := hk.e22; have e20 := hk.e20; have e15 := hk.e15; have e19 := hk.e19; have e21 := hk.e21
  have e17 := hk.e17; have e16 := hk.e16; have e13 := hk.e13; have e14 := hk.e14; have e3 := hk.e3
  have e7 := hk.e7; have e8 := hk.e8
  have esp := hjc.esp; have e28 := hjc.e28; have e29 := hjc.e29; have e18 := hjc.e18
  clear hk
  janus_run [] until [1789220]
  refine itS (t := yl - 1) hP (by janus_simp) (JC.frameW hP hjc (ws := []) (fun r hr => absurd hr List.not_mem_nil)
    (MemFrame.refl _ _) rfl (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)) hB hzl (by omega)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ KXE KX2
  all_goals first | (janus_simp; done) | (janus_simp; exact sub2 yl hyl0 (by omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the lower loop's exit** -/
theorem exitL {impl : List Segment} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : BitVec 64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 64 w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc)
    (KXE : ∀ S' : State, w = 0 →
      KE R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 z zl zc' Zv zz zzl zzc r rl rc q ql qc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KX2 : ∀ (S' : State) (i : Nat) (v : BitVec 64), w = i + 1 → v.toNat = Exp.wd (natVal s.mem yp yl) i →
      KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 0 i v z zl zc' Zv zz zzl zzc
        r rl rc q ql qc → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hyl : yl ≤ 2 ^ 9 := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := hk.w63
  have hjc := hk.jc; have hB := hk.bb; have hzl := hk.zl128
  have epc := hk.pc; have e0 := hk.e0; have e5 := hk.e5; have e2 := hk.e2; have e24 := hk.e24; have e23 := hk.e23
  have e22 := hk.e22; have e20 := hk.e20; have e15 := hk.e15; have e19 := hk.e19; have e21 := hk.e21
  have e17 := hk.e17; have e16 := hk.e16; have e13 := hk.e13; have e3 := hk.e3
  have e7 := hk.e7; have e8 := hk.e8
  have esp := hjc.esp; have e28 := hjc.e28; have e29 := hjc.e29; have e18 := hjc.e18
  clear hk
  janus_run [] until [1789220]
  refine itS (t := w) hP (by janus_simp) (JC.frameW hP hjc (ws := []) (fun r hr => absurd hr List.not_mem_nil)
    (MemFrame.refl _ _) rfl (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)) hB hzl (by omega)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ KXE KX2
  all_goals first | (janus_simp; done) | skip

end

end FvModexp.Arm64.ExpSlow
