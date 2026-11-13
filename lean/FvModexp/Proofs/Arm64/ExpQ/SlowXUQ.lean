import FvModexp.Proofs.Arm64.ExpQ.SlowSqQ
import FvModexp.Proofs.Arm64.Exp.SlowXU

set_option autoImplicit false

/-! (Q-form copy of Exp/SlowXU.lean, TIGHT COSTS, agent expmc s43)
# `nat.expNNSlow` (arm64): the two loop exits into the word test `IT` (agent expmc)

* `exitU`: `T1` with `j = w` (`CMP R14, R13; BGE` → `fnE + 0x358`: `SUB $2, R8` (`R8 = len y`), `JMP` → `IT`):
  `IT` with `t = len y - 1` (nat.go:749, 766);
* `exitL`: `T2` with `j = 64` (`CMP $64, R13; BGE` → `fnE + 0x360`: `SUB $1, R8` (`R8 = i`) → `IT`): `IT` with `t = i`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.Q.ExpSlow

open FvModexp.Arm64.ExpSlow

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the word test `IT`** (see the module doc) -/
theorem itSQ {impl : List Segment} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : BitVec 64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 t : Nat}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hpc : S.pc = BitVec.ofNat 64 (fnE + 0x364))
    (hj : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S S.mem L1 b1)
    (hB : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc) (hzl : zl ≤ max xl ml) (ht : t < yl)
    (e0 : S.regs 0 = BitVec.ofNat 64 z) (e5 : S.regs 5 = BitVec.ofNat 64 zl) (e2 : S.regs 2 = BitVec.ofNat 64 zc')
    (e24 : S.regs 24 = BitVec.ofNat 64 zz) (e23 : S.regs 23 = BitVec.ofNat 64 zzl)
    (e22 : S.regs 22 = BitVec.ofNat 64 zzc) (e20 : S.regs 20 = BitVec.ofNat 64 r)
    (e15 : S.regs 15 = BitVec.ofNat 64 rl) (e19 : S.regs 19 = BitVec.ofNat 64 rc)
    (e21 : S.regs 21 = BitVec.ofNat 64 q) (e17 : S.regs 17 = BitVec.ofNat 64 ql)
    (e16 : S.regs 16 = BitVec.ofNat 64 qc) (e3 : S.regs 3 = BitVec.ofNat 64 st)
    (e7 : S.regs 7 = BitVec.ofNat 64 yp) (e8 : S.regs 8 = BitVec.ofNat 64 t - 1#64)
    (KXE : ∀ S' : State, t = 0 → stCap S'.mem st = stCap S.mem st →
      KE R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 z zl zc' Zv zz zzl zzc r rl rc q ql qc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KX2 : ∀ (S' : State) (i : Nat) (v : BitVec 64), t = i + 1 → v.toNat = Exp.wd (natVal s.mem yp yl) i →
      stCap S'.mem st = stCap S.mem st →
      KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 0 i v z zl zc' Zv zz zzl zzc
        r rl rc q ql qc → ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hyl : yl ≤ 2 ^ 9 := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have esp := hj.esp; have e28 := hj.e28; have e29 := hj.e29; have e18 := hj.e18
  rcases t with _ | i
  · rw [show BitVec.ofNat 64 0 = BitVec.ofNat 64 0 from rfl] at e8
    clear KX2
    janus_run [m1_63] until [1789672]
    exact KXE _ rfl rfl ⟨by janus_simp, JC.frameW hP hj (ws := []) (fun r hr => absurd hr List.not_mem_nil)
      (MemFrame.refl _ _) rfl (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp), hB, hzl,
      by janus_simp, by janus_simp, by janus_simp⟩
  · rw [sub1 i (by omega)] at e8
    have hyw := y_words hP hj.wc i (by omega)
    have hmacc : S.mem.accessible (sp - K) (K + 544) true = true := by
      rw [hj.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
    have hya : S.mem.accessible yp (8 * yl) false = true := by
      rw [hj.wc.fr.accessible]; exact hP.2.2.2.2.2.2.2.2.1
    have hy48 : yp + 8 * yl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.2.1
    have ya1 : S.mem.accessible (yp + 8 * i) 8 false = true :=
      Memory.accessible_mono _ hya (by omega) (by omega)
    have hyA : Apart yp (8 * yl) (sp - K) (K + 544) := hP.2.2.2.2.2.2.2.1.2.1
    unfold Apart at hyA
    have hyw' : S.mem.readLE (yp + i * 8) 8 = Exp.wd (natVal s.mem yp yl) i := by rw [Nat.mul_comm]; exact hyw
    have hlt := Exp.wd_lt (natVal s.mem yp yl) i
    simp only [Exp.B] at hlt
    have hi8 : ¬ (BitVec.ofNat 64 i).getLsbD 63 = true := by
      rw [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit_eq_decide_div_mod_eq]
      simp only [decide_eq_true_eq]; rw [Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]; decide
    clear KXE
    janus_run [hi8, hyw, ya1, hmacc] until [1789336]
    refine KX2 _ i (BitVec.ofNat 64 (S.mem.readLE (yp + i * 8) 8)) rfl ?vv (capW hP ?ws ?F) (mkKT2w (j := 0) (w := i) hP hj hB hzl (by omega) (by omega) _ (ws := [(sp + 216, sp + 224)]) ?ws ?F ?rg ?r216
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    case ws => intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; omega
    case F => janus_frame
    case rg => simp only [Memory.regions_writeLE]
    case r216 => rw [Memory.readLE_writeLE_self] <;> omega
    case vv => rw [BitVec.toNat_ofNat, hyw', Nat.mod_eq_of_lt hlt]
    all_goals first | (janus_simp [hyw']; done) | (janus_simp <;> omega) | skip


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the upper loop's exit** -/
theorem exitUQ {impl : List Segment} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : BitVec 64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KT1 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 w w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc)
    (KXE : ∀ S' : State, yl - 1 = 0 → stCap S'.mem st = stCap S.mem st →
      KE R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 z zl zc' Zv zz zzl zzc r rl rc q ql qc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KX2 : ∀ (S' : State) (i : Nat) (v : BitVec 64), yl - 1 = i + 1 → v.toNat = Exp.wd (natVal s.mem yp yl) i →
      stCap S'.mem st = stCap S.mem st →
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
  refine itSQ (t := yl - 1) hP (by janus_simp) (JC.frameW hP hjc (ws := []) (fun r hr => absurd hr List.not_mem_nil)
    (MemFrame.refl _ _) rfl (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)) hB hzl (by omega)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ KXE KX2
  all_goals first | (janus_simp; done) | (janus_simp; exact sub2 yl hyl0 (by omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the lower loop's exit** -/
theorem exitLQ {impl : List Segment} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : BitVec 64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hk : KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 64 w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc)
    (KXE : ∀ S' : State, w = 0 → stCap S'.mem st = stCap S.mem st →
      KE R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 z zl zc' Zv zz zzl zzc r rl rc q ql qc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KX2 : ∀ (S' : State) (i : Nat) (v : BitVec 64), w = i + 1 → v.toNat = Exp.wd (natVal s.mem yp yl) i →
      stCap S'.mem st = stCap S.mem st →
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
  refine itSQ (t := w) hP (by janus_simp) (JC.frameW hP hjc (ws := []) (fun r hr => absurd hr List.not_mem_nil)
    (MemFrame.refl _ _) rfl (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)) hB hzl (by omega)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ KXE KX2
  all_goals first | (janus_simp; done) | skip


end

end FvModexp.Arm64.Q.ExpSlow
