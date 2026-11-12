import FvModexp.Proofs.Arm64.Exp.SlowKE
import FvModexp.Proofs.Common.SubMod2NMath
import FvModexp.Proofs.Common.Util

set_option autoImplicit false

/-!
# `nat.expNNSlow` (arm64): after `z.set(x)` → the upper test `T1` (agent expmc)

At `PV` (`fnE + 0x144`, nat.go:734-749): `SUB $1, R8, R9; CMP R9, R8; BLS panic` (`len y ≥ 1`), `v = y[len y - 1]`,
`shift = CLZ v + 1`, `v <<= shift` (`CSEL LO`: `0` when `shift = 64`), `w = 64 - shift` (slot 152), `j, zz, r, q := 0`,
`JMP` → `T1`. `KV`: the state at `PV` (`z` = a copy of `x` in `(X0, X5, X2)`). `segV`: `KV` → `KT1` at `j = 0`
with the model invariant `outerLoop 1 (stepM X M) Y 64 (len y - 1) v w X = expNNSlow X Y M` (`expNNSlow_eq`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpSlow

/-- at `PV` (`fnE + 0x144`): `z` (a copy of `x`) in `(X0, X5, X2)`, the arguments reloaded -/
structure KV (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat)
    (s : State) (r18 : BitVec 64) (r29 ret : Nat) (S : State) (L1 : List (Nat × Nat)) (b1 : Nat) (z zc' : Nat) :
    Prop where
  pc : S.pc = BitVec.ofNat 64 (fnE + 0x144)
  jc : JC R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S S.mem L1 b1
  bz : LN R L st zp zc S.mem L1 z xl zc' (natVal s.mem xp xl)
  e0 : S.regs 0 = BitVec.ofNat 64 z
  e5 : S.regs 5 = BitVec.ofNat 64 xl
  e2 : S.regs 2 = BitVec.ofNat 64 zc'
  e3 : S.regs 3 = BitVec.ofNat 64 st
  e7 : S.regs 7 = BitVec.ofNat 64 yp
  e8 : S.regs 8 = BitVec.ofNat 64 yl

theorem dl_nil {R : RtInv} {L : List (Nat × Nat)} {st zp zc : Nat} {M : Memory} {L1 : List (Nat × Nat)} :
    DL R L st zp zc M L1 0 0 :=
  ⟨by decide, fun h => absurd h (by decide), Or.inr (Or.inr ⟨rfl, rfl⟩), fun h => absurd h (by decide), fun _ => rfl⟩

/-- the initial digit word as the run computes it: `top << (clz + 1)` (`0` when the shift is `64`) -/
theorem v_init (t : Nat) (ht : t < 2 ^ 64) (ht0 : t ≠ 0) :
    (if (clzNat 64 t + 1) % 18446744073709551616 < 64 then
        BitVec.ofNat 64 (t * 2 ^ ((clzNat 64 t + 1) % 18446744073709551616 % 64)) else 0#64).toNat =
      t * 2 ^ ((64 - Exp.bitLen t) + 1) % Exp.B := by
  have hc := Util.clz_bl 64 t ht
  have eb : Exp.bitLen t = Aux.bitLen t := by unfold Exp.bitLen Aux.bitLen; rfl
  have hb : 1 ≤ Aux.bitLen t := by unfold Aux.bitLen; rw [if_neg ht0]; omega
  rw [eb, show 64 - Aux.bitLen t + 1 = clzNat 64 t + 1 by omega, Exp.B_def,
    Nat.mod_eq_of_lt (show clzNat 64 t + 1 < 18446744073709551616 by omega)]
  split
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show clzNat 64 t + 1 < 64 by omega)]
  · have e : clzNat 64 t + 1 = 64 := by omega
    rw [e, Nat.mul_mod_left]; rfl

theorem w_init (t : Nat) (ht : t < 2 ^ 64) (ht0 : t ≠ 0) :
    (18446744073709551616 - (clzNat 64 t + 1) % 18446744073709551616 + 64) % 2 ^ 64 =
      64 - ((64 - Exp.bitLen t) + 1) := by
  have hc := Util.clz_bl 64 t ht
  have eb : Exp.bitLen t = Aux.bitLen t := by unfold Exp.bitLen Aux.bitLen; rfl
  have hb : 1 ≤ Aux.bitLen t := by unfold Aux.bitLen; rw [if_neg ht0]; omega
  rw [eb]; omega

theorem w_reg (t : Nat) (ht : t < 2 ^ 64) (ht0 : t ≠ 0) :
    64#64 - (BitVec.ofNat 64 (clzNat 64 t) + 1#64) = BitVec.ofNat 64 (64 - ((64 - Exp.bitLen t) + 1)) := by
  have hc := Util.clz_bl 64 t ht
  have eb : Exp.bitLen t = Aux.bitLen t := by unfold Exp.bitLen Aux.bitLen; rfl
  have hb : 1 ≤ Aux.bitLen t := by unfold Aux.bitLen; rw [if_neg ht0]; omega
  rw [eb]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl yc mp ml mc : Nat}
    {s : State} {r18 : BitVec 64} {r29 ret : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`PV` → `T1`** (see the module doc) -/
theorem segV {impl : List Segment} (hP : EPre R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s)
    {ret0 : BitVec 64} {Q : State → Prop} {S : State} {L1 : List (Nat × Nat)} {b1 z zc' : Nat}
    (hk : KV R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S L1 b1 z zc')
    (KT : ∀ (S' : State) (v : BitVec 64) (w : Nat),
      KT1 R b L K g sp st zp zc xp xl xc yp yl yc mp ml mc s r18 r29 ret S' L1 b1 0 w v z xl zc'
        (natVal s.mem xp xl) 0 0 0 0 0 0 0 0 0 →
      Exp.outerLoop 1 (stepM (natVal s.mem xp xl) (natVal s.mem mp ml)) (natVal s.mem yp yl) 64 (yl - 1) v.toNat w
        (natVal s.mem xp xl) = Exp.expNNSlow (natVal s.mem xp xl) (natVal s.mem yp yl) (natVal s.mem mp ml) →
      ReachesRet (LibW.program.link impl) ret0 S' Q) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hyl : yl ≤ 2 ^ 9 := hP.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hyl0 : 0 < yl := hP.2.2.2.2.2.2.2.2.2.2.2.1
  have hyN : NatNorm s.mem yp yl := hP.2.2.2.2.2.2.2.2.2.2.1
  have hxl := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hjc := hk.jc
  have hz := hk.bz
  have epc := hk.pc; have e0 := hk.e0; have e5 := hk.e5; have e2 := hk.e2; have e3 := hk.e3
  have e7 := hk.e7; have e8 := hk.e8
  have esp := hjc.esp; have e28 := hjc.e28; have e29 := hjc.e29; have e18 := hjc.e18
  clear hk
  have hyw := y_words hP hjc.wc (yl - 1) (by omega)
  have hmacc : S.mem.accessible (sp - K) (K + 544) true = true := by
    rw [hjc.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  have hya : S.mem.accessible yp (8 * yl) false = true := by
    rw [hjc.wc.fr.accessible]; exact hP.2.2.2.2.2.2.2.2.1
  have hy48 : yp + 8 * yl ≤ 2 ^ 48 := hP.2.2.2.2.2.2.2.2.2.1
  have ya1 : S.mem.accessible (yp + (yl - 1) * 8) 8 false = true :=
    Memory.accessible_mono _ hya (by omega) (by omega)
  have hyA : Apart yp (8 * yl) (sp - K) (K + 544) := hP.2.2.2.2.2.2.2.1.2.1
  unfold Apart at hyA
  have hyw' : S.mem.readLE (yp + (yl - 1) * 8) 8 = Exp.wd (natVal s.mem yp yl) (yl - 1) := by
    rw [Nat.mul_comm]; exact hyw
  have hsub : BitVec.ofNat 64 yl - 1#64 = BitVec.ofNat 64 (yl - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hyN' := hyN
  rcases hyN' with h0 | htop
  · omega
  have ht0 : S.mem.readLE (yp + (yl - 1) * 8) 8 ≠ 0 := by
    rw [hyw', ← Expmc.readLE_wd s.mem yp (yl - 1) yl (by omega)]; exact htop
  have htl : S.mem.readLE (yp + (yl - 1) * 8) 8 < 2 ^ 64 := by
    have := Expmc.readLE_lt_B S.mem (yp + (yl - 1) * 8) 1; rw [Nat.mul_one, Nat.pow_one, Exp.B_def] at this; exact this
  have hwr := w_reg _ htl ht0
  have hw63 : 64 - ((64 - Exp.bitLen (S.mem.readLE (yp + (yl - 1) * 8) 8)) + 1) ≤ 63 := by omega
  janus_run [hmacc, hsub, ya1] until [1788872]
  rw [hwr]
  have hB : BB R L st zp zc S.mem L1 z xl zc' (natVal s.mem xp xl) 0 0 0 0 0 0 0 0 0 :=
    ⟨hz, dl_nil, Nat.le_refl _, dl_nil, Nat.le_refl _, dl_nil, Nat.le_refl _, fun _ h => absurd h (by decide),
      fun _ h => absurd h (by decide), fun _ h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  refine KT _ _ _ ⟨rfl, JC.frameW hP hjc (ws := [(sp + 152, sp + 160)]) ?ws ?F ?rg (by janus_simp) (by janus_simp)
    (by janus_simp) (by janus_simp), BB.frameW hP ?ws ?F hB, hxl, Nat.zero_le _, hw63, ?r152, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩ ?model
  case ws => intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; omega
  case F => janus_frame
  case rg => simp only [Memory.regions_writeLE]
  case r152 => rw [Memory.readLE_writeLE_self, w_init _ htl ht0]
  case model =>
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte]
    rw [expNNSlow_eq, SubMod2N.norm_nlen _ _ _ hyN, ← hyw', ← v_init _ htl ht0]
  all_goals first | (janus_simp; done) | (janus_simp <;> omega) | skip

end

end FvModexp.Arm64.ExpSlow
