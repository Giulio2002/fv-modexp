import FvModexp.Proofs.Arm64.Exp.SlowK2
import FvModexp.Proofs.Arm64.Exp.SlowMod
import FvModexp.Proofs.Common.ExpmcWin

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): the word step `IT` and the exit join `KE` (agent expmc)

* `y_words`: `y`'s words are unchanged at every loop state (port of infra's `P2W4.y_words`);
* `KE`: at the exit `EX` (`fnE + 0x528`, `return z.norm()`): `z` in `(X0, X5, X2)`;
* `mkKT2w`: `KT2` at a state whose memory is a slot store away from the context's;
* `itS`: the word test `IT` (`fnE + 0x364`, `TBNZ $63, R8`, `R8 = t - 1`): `t = 0` → `EX` (`KE`); `t = i + 1` →
  `216 := i`, `R9 := y[i]`, `R13 := 0`, `JMP` → `T2` (`KT2` at `j = 0`, word `i`, `v = y[i]`) (nat.go:766-769).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

/-- at the exit `EX` (`fnE + 0x528`): `z` in `(X0, X5, X2)` -/
structure KE (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (r18 : BitVec 64) (r29 ret : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 : Nat)
    (z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 (fnE + 0x528)
  jc : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S S.mem L1 b1
  bb : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc
  zl128 : zl ≤ max xl ml
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e5 : S.regs 5 = BitVec.ofNat 64 zl
  e2 : S.regs 2 = BitVec.ofNat 64 zc'

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

theorem m1_63 : (BitVec.ofNat 64 0 - 1#64).getLsbD 63 = true := by decide

theorem sub1 (i : Nat) (_h : i + 1 < 2 ^ 64) : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- `y`'s words at a loop state (port of infra's `P2W4.y_words`) -/
theorem y_words (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s) {M : Memory}
    {L1 : List (Nat × Nat)} {b1 ℓ : Nat} (h : WC R L K g sp st zp zc s.mem M L1 b1 ℓ) :
    ∀ j, j < yl → M.readLE (yp + 8 * j) 8 = Exp.wd (natVal s.mem yp yl) j := by
  intro j hj
  have hyO : OE R L sp K st s.mem yp (8 * yl) := hP.2.2.2.2.2.2.2.1
  have hb := oe_bytes hP hyO (fun hc => (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hc).2.2.2.2.2.2.1)
  rw [h.readB (hyO.1.imp (fun q => q.sub (by omega) (by omega)) (fun q => q.of_sub (by omega) (by omega)))
    fun i hi => by rw [Nat.add_assoc]; exact hb (8 * j + i) (by omega)]
  exact Expmc.readLE_wd s.mem yp j yl hj

set_option maxRecDepth 20000 in
/-- `KT2` at a state `T` whose memory is a slot-store frame of the context's (pure) -/
theorem mkKT2w {S : State} {L1 : List (Nat × Nat)} {b1 j w : Nat} {v : BitVec 64}
    {z zl zc' Zv zz zzl zzc r rl rc q ql qc : Nat}
    (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    (hj : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S S.mem L1 b1)
    (hB : BB R L st zp zc S.mem L1 z zl zc' Zv zz zzl zzc r rl rc q ql qc) (hzl : zl ≤ max xl ml) (hj64 : j ≤ 64)
    (hw : w + 2 ≤ yl) (T : State) {ws : List (Nat × Nat)} (hws : InSlots sp ws) (hF : MemFrame S.mem T.mem ws)
    (hrg : T.mem.regions = S.mem.regions) (s216 : T.mem.readLE (sp + 216) 8 = w)
    (hpc : T.pc = BitVec.ofNat 64 (fnE + 0x3d8)) (hsp : T.sp = BitVec.ofNat 64 sp)
    (h28 : T.regs 28 = BitVec.ofNat 64 g) (h29 : T.regs 29 = BitVec.ofNat 64 (sp - 8)) (h18 : T.regs 18 = r18)
    (e0 : T.regs 0 = BitVec.ofNat 64 z) (e5 : T.regs 5 = BitVec.ofNat 64 zl) (e2 : T.regs 2 = BitVec.ofNat 64 zc')
    (e24 : T.regs 24 = BitVec.ofNat 64 zz) (e23 : T.regs 23 = BitVec.ofNat 64 zzl)
    (e22 : T.regs 22 = BitVec.ofNat 64 zzc) (e20 : T.regs 20 = BitVec.ofNat 64 r)
    (e15 : T.regs 15 = BitVec.ofNat 64 rl) (e19 : T.regs 19 = BitVec.ofNat 64 rc)
    (e21 : T.regs 21 = BitVec.ofNat 64 q) (e17 : T.regs 17 = BitVec.ofNat 64 ql)
    (e16 : T.regs 16 = BitVec.ofNat 64 qc) (e13 : T.regs 13 = BitVec.ofNat 64 j) (e9 : T.regs 9 = v)
    (e3 : T.regs 3 = BitVec.ofNat 64 st) (e7 : T.regs 7 = BitVec.ofNat 64 yp) (e8 : T.regs 8 = BitVec.ofNat 64 w) :
    KT2 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret T L1 b1 j w v z zl zc' Zv zz zzl zzc
      r rl rc q ql qc :=
  ⟨hpc, JC.frameW hP hj hws hF hrg hsp h28 h29 h18, BB.frameW hP hws hF hB, hzl, hj64, hw, s216, e0, e5, e2, e24,
    e23, e22, e20, e15, e19, e21, e17, e16, e13, e9, e3, e7, e8⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **the word test `IT`** (see the module doc) -/
theorem itS {impl : List Segment} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
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
    (KXE : ∀ S' : State, t = 0 →
      KE R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 z zl zc' Zv zz zzl zzc r rl rc q ql qc →
      ReachesRet (LibW.program.link impl) ret0 S' Q)
    (KX2 : ∀ (S' : State) (i : Nat) (v : BitVec 64), t = i + 1 → v.toNat = Exp.wd (natVal s.mem yp yl) i →
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
    exact KXE _ rfl ⟨by janus_simp, JC.frameW hP hj (ws := []) (fun r hr => absurd hr List.not_mem_nil)
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
    refine KX2 _ i (BitVec.ofNat 64 (S.mem.readLE (yp + i * 8) 8)) rfl ?vv (mkKT2w (j := 0) (w := i) hP hj hB hzl (by omega) (by omega) _ (ws := [(sp + 216, sp + 224)]) ?ws ?F ?rg ?r216
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    case ws => intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; omega
    case F => janus_frame
    case rg => simp only [Memory.regions_writeLE]
    case r216 => rw [Memory.readLE_writeLE_self] <;> omega
    case vv => rw [BitVec.toNat_ofNat, hyw', Nat.mod_eq_of_lt hlt]
    all_goals first | (janus_simp [hyw']; done) | (janus_simp <;> omega) | skip

end

end FvModexp.Arm64.ExpSlow
