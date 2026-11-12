import FvModexp.Proofs.Arm64.Exp.P2W2Cp2

/-!
# `expNNPowerOfTwoWindowSize2` (arm64): the copy point `CP = 0x1b67fc` (agent infra)

`CPF`: the frame facts carried from the table to the copy point (`WC`, `ESl`, `TZ`, `zz`'s slots); transport
through the function's own slot stores (`CPF.st`) and a live allocation (`CPF.alloc`); `CPF.ofAT`.
`cpC`: from `CP` (`R0 = R1 = n`, `R3 = dp`, `R14 = dc`, `R9 = powers[d]`): `min`, the `dp == src` test (refuted),
the spills `152/136/296`, `memmove` → `cpM`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2W2

/-- the copy point -/
abbrev CP : Nat := 1796092

/-- the frame facts from the table to the copy point -/
structure CPF (R : RtInv) (L : List (Nat × Nat)) (K g sp st zp zc xp xl xc yp yl lm ret : Nat) (s : State)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 zzp bp : Nat) : Prop where
  wc : WC R L K g sp st zp zc s.mem M L1 b1 (ℓL (stLen s.mem st) lm)
  esl : ESl M sp st (s.regs 29) ret zp zc xp xl xc yp yl lm (stLen s.mem st)
  tz : TZ R L s.mem M L1 st sp zzp bp lm (natVal s.mem xp xl)
  z280 : M.readLE (sp + 280) 8 = zzp
  z112 : M.readLE (sp + 112) 8 = 2 * W lm
  z120 : M.readLE (sp + 120) 8 = 2 * W lm

/-- the store slots of the bitLen / make segment (outside `ESl`, `zz`'s slots and the table headers) -/
@[reducible] def StS (sp : Nat) (r : Nat × Nat) : Prop :=
  (sp + 96 ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ sp + 112) ∨ (sp + 128 ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ sp + 256) ∨
    (sp + 288 ≤ r.1 ∧ r.1 ≤ r.2 ∧ r.2 ≤ sp + 320)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g sp st zp zc xp xl xc yp yl lm : Nat} {s : State}
    {ret : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 zzp bp : Nat}

theorem CPF.ofAT (h : AT R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) :
    CPF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp :=
  ⟨h.wc, h.esl, ⟨h.pw, h.bscr, h.bbu, h.zscr, h.zbu, h.zb⟩, h.z280, h.z112, h.z120⟩

set_option maxRecDepth 20000 in
/-- `CPF` through own stores into `StS` slots -/
theorem CPF.stores (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (h : CPF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {M' : Memory} {ws : List (Nat × Nat)}
    (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions) (hws : ∀ r ∈ ws, StS sp r) :
    CPF R L K g sp st zp zc xp xl xc yp yl lm ret s M' L1 b1 zzp bp := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 560) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hbW := scr_win hP h.tz.bscr
  unfold Apart at hbW
  have kO : ∀ a k, (a + k ≤ sp + 96 ∨ (sp + 112 ≤ a ∧ a + k ≤ sp + 128) ∨ (sp + 256 ≤ a ∧ a + k ≤ sp + 288) ∨
      sp + 320 ≤ a) → M'.readLE a k = M.readLE a k := fun a k ha =>
    hF.readLE a k (outside_of_forall fun r hr => by have := hws r hr; simp only [StS] at this; omega)
  have kB : ∀ a k, bp ≤ a → a + k ≤ bp + 8 * P2Pre.NB 4 lm → M'.readLE a k = M.readLE a k := fun a k h1 h2 =>
    hF.readLE a k (outside_of_forall fun r hr => by have := hws r hr; simp only [StS] at this; omega)
  obtain ⟨e0, e1, e2⟩ := hdr3 (M := M) (M' := M') (st := st) fun j hj =>
    hF.readLE _ _ (outside_of_forall fun r hr => by have := hws r hr; simp only [StS] at this; omega)
  refine ⟨WC.win hP h.wc hF hrg fun r hr => ?_, ESl.keep h.esl (fun a k ha => kO a k (by omega)) (by omega),
    h.tz.keep hF.accessible (LiveExt.refl R L1) e0 e1 e2 fun a k ha => ?_, by rw [kO _ _ (by omega)]; exact h.z280,
    by rw [kO _ _ (by omega)]; exact h.z112, by rw [kO _ _ (by omega)]; exact h.z120⟩
  · have := hws r hr; simp only [StS] at this; omega
  · rcases ha with ha | ha
    · exact kO a k (by omega)
    · exact kB a k ha.1 ha.2

set_option maxRecDepth 20000 in
/-- `CPF` through a live allocation -/
theorem CPF.alloc (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    (h : CPF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {m : Memory} {p r n : Nat}
    (hA : AllocR R L K g sp st zp zc s.mem M L1 b1 (ℓL (stLen s.mem st) lm) m p r n) :
    CPF R L K g sp st zp zc xp xl xc yp yl lm ret s m (L1 ++ [(p, p + r)]) (b1 - r) zzp bp := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hstw : Apart st 24 (sp - K) (K + 560) := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Apart at hstw
  have hbW := scr_win hP h.tz.bscr
  unfold Apart at hbW
  have hsok := h.wc.sok
  obtain ⟨e0, e1, e2⟩ := hdr3 (M := M) (M' := m) (st := st) fun j hj =>
    hA.rdH _ _ (hsok.2.1.sub (by omega) (by omega)) (by unfold Apart; omega)
  have hx : LiveExt R L1 (L1 ++ [(p, p + r)]) :=
    LiveExt.single (by rw [show p + r - p = r by omega]; exact hA.rin)
      (by rw [show p + r - p = r by omega]; exact hA.rap)
  refine ⟨hA.wc, ESl.keep h.esl (fun a k ha => hA.keep a k (by omega)) (by omega),
    h.tz.keep hA.macc hx e0 e1 e2 fun a k ha => ?_, by rw [hA.keep _ _ (by omega)]; exact h.z280,
    by rw [hA.keep _ _ (by omega)]; exact h.z112, by rw [hA.keep _ _ (by omega)]; exact h.z120⟩
  rcases ha with ha | ha
  · exact hA.keep a k (by omega)
  · exact hA.rdH a k (h.tz.bscr.held.sub ha.1 ha.2) (by unfold Apart; omega)

/-- (copied from expmc's `W2Pro.lsl3`) -/
theorem lsl3 (x : BitVec 64) :
    x.rotateRight 61 &&& 18446744073709551608#64 &&& 18446744073709551615#64 = x <<< 3 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (18446744073709551608#64)[i] = decide (3 ≤ i) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_shiftLeft, c1 i hi, c2 i hi]
  by_cases h : i < 3
  · simp [h]
  · simp [h]; omega

/-- (copied from expmc's `W2Pro.e8n`) -/
theorem e8n (n : Nat) (hn : n ≤ 2 ^ 16) : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the copy point to the loop test** -/
theorem cpC {impl : List Segment} (hmv : MemmoveLive (LibExp.program.link impl) P2Pre.mvE 4096 R)
    (ret0 : BitVec 64) (Q : State → Prop) (hP : EPre R b L K g sp st zp zc xp xl xc yp yl lm s)
    {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat} {kk cst FV : Nat} {r29 : BitVec 64}
    (KL : KL impl ret0 Q R b L K g sp st zp zc xp xl xc yp yl lm ret s r29 sqC mlC zzp bp kk cst FV)
    (hc : CPF R L K g sp st zp zc xp xl xc yp yl lm ret s M L1 b1 zzp bp) {dp dc n d i yi : Nat}
    (hub : UB R L K g sp st zp zc M L1 zzp bp lm dp dc) (hnd : n ≤ dc) (hn1 : 0 < n) (hd : d < 4) (hZo : Exp.p2Pow lm (natVal s.mem xp xl) d % 2 = 1)
    (hlen : M.readLE (sp + 320 + 24 * d + 8) 8 = n)
    (s160 : M.readLE (sp + 160) 8 = yi) (s200 : M.readLE (sp + 200) 8 = kk) (s240 : M.readLE (sp + 240) 8 = kk - 1)
    (s208 : M.readLE (sp + 208) 8 = i) (hkk1 : 1 ≤ kk) (hkk : kk ≤ 32) (hi : i < yl) (hyi : yi < 2 ^ 64)
    (hbud : b + (kk - 1 + 32 * i) * bc sqC mlC (ℓL (stLen s.mem st) lm) lm + P2Pre.tC lm ≤ b1 + cst)
    (hFV : Exp.outerLoop 2 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 32 i
      (yi * 2 ^ (64 - (kk - 1) * 2) % 2 ^ 64) (kk - 1) (Exp.p2Pow lm (natVal s.mem xp xl) d) = FV)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 CP) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 n) (h1 : S.regs 1 = BitVec.ofNat 64 n) (h3 : S.regs 3 = BitVec.ofNat 64 dp)
    (h14 : S.regs 14 = BitVec.ofNat 64 dc) (h9 : S.regs 9 = BitVec.ofNat 64 (bp + 8 * (d * W lm))) :
    ReachesRet (LibExp.program.link impl) ret0 S Q := by
  have hK := hP.1.2.2.2.2.2.2.2.1
  have hK1 := hP.1.2.2.2.2.2.2.2.2.1
  have hsp2 := hP.1.2.2.2.2.2.2.2.2.2.1
  have hal : sp % 16 = 0 := hP.1.2.2.2.2.2.2.1
  have hlm := hP.2.2.2.2.2.2.1
  have hdc0 : 0 < dc := by omega
  obtain ⟨-, -, -, hd48⟩ := hub.live hdc0
  obtain ⟨-, -, -, -, -, -, hdB⟩ := hub.ap hdc0
  obtain ⟨-, -, d2, -, -⟩ := hc.tz.pw d hd
  rw [hlen] at d2
  have eW : P2Pre.W lm = W lm := rfl
  rw [eW] at d2
  have hjW : (d + 1) * W lm ≤ P2Pre.NB 4 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : d * W lm + W lm ≤ P2Pre.NB 4 lm := by rw [← Nat.succ_mul]; exact hjW
  have hW128 : W lm ≤ 128 := by simp only [W]; omega
  have hb48 := hc.tz.bscr.b48
  unfold Apart at hdB
  have hne : dp ≠ bp + 8 * (d * W lm) := by intro e; rw [e] at hdB; omega
  have hlt : ((n : Int) > (n : Int)) = False := by simp
  have hmacc : M.accessible (sp - K) (K + 560) true = true := by
    rw [hc.wc.fr.accessible]; exact hP.1.2.2.2.2.2.2.2.2.2.2.1
  subst hm
  janus_run [hne, hlt, lsl3, e8n n (by omega), hmacc] until [P2Pre.mvE]
  refine cpM hmv ret0 Q hP KL hc.wc hc.esl hc.tz hc.z280 hc.z112 hc.z120 hub hnd hn1 hd hZo hlen s160 s200 s240 s208
    hkk1 hkk hi hyi hbud hFV ?F1 ?rg1 ?r136 ?r152 ?r296 _ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_
  case F1 => janus_frame
  case rg1 => simp only [Memory.regions_writeLE]
  all_goals first | (janus_simp; done) | skip

end

end FvModexp.Arm64.P2W2
