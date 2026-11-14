import FvModexp.Proofs.Amd64.Exp.P2W4Cp1

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the copy point `CP` (fn+0x571) → the loop test `LT` (agent divmc s77, port of divmc s71; amd64
twin of agent infra's `Arm64.P2W4Cp3` + `Arm64.P2W4Cp2`)

`CPF`: the frame facts carried from the table to the copy point (`WC`, `ESl`, `TZ`, `zz`'s slots); transport through
the function's own slot stores (`CPF.stores`) and a live allocation (`CPF.alloc`); `CPF.ofAT`.
`cpC`: from `CP` (`SI = R8 = n`, `R9 = dp`, `R13 = dc`, `R15 = powers[d]`): spill `0x80 := n`, `min`, the
`dp == src` test (refuted), spills `0x90 := dc`, `0x130 := dp`, `memmove(dp, powers[d], 8n)` (CALL +0x5a2, return
+0x5a7), the reloads, `yi <<= 64 - 4k` (`NEGQ`/`SHLQ`/`SBBQ` mask; `k = kk - 1`), `0xc8 := kk - 2`, `0xd0 := i`
(+0x647) and `KL` at `LT` with `li_first`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- the copy point (fn+0x571) -/
abbrev CP : Nat := 6199345

/-- the frame facts from the table to the copy point -/
structure CPF (R : RtInv) (L : List (Nat × Nat)) (K g sp st bp r zp zc xp xl xc yp yl lm : Nat) (s : State)
    (M : Memory) (L1 : List (Nat × Nat)) (b1 zzp tp : Nat) : Prop where
  wc : WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 (lvlL (stLen s.mem st) lm)
  esl : ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)
  tz : TZ R L s.mem M L1 st sp zzp tp lm (natVal s.mem xp xl)
  z118 : M.readLE (sp + 0x120) 8 = zzp
  z68 : M.readLE (sp + 0x68) 8 = 2 * W lm
  z70 : M.readLE (sp + 0x70) 8 = 2 * W lm

/-- the store slots of the bitLen / make / copy segment (outside `ESl`, `zz`'s slots and the table headers):
the return-address slot, `0x60`, `[0x78, 0x100)` and `[0x120, 0x140)` -/
@[reducible] def StS (sp : Nat) (q : Nat × Nat) : Prop :=
  (sp - 0x8 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ sp) ∨ (sp + 0x60 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ sp + 0x68) ∨
    (sp + 0x78 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ sp + 0x108) ∨ (sp + 0x128 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ sp + 0x148)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K g fs sp st bp r zp zc xp xl xc yp yl lm : Nat} {s : State}
    {M : Memory} {L1 : List (Nat × Nat)} {b1 zzp tp : Nat}

theorem CPF.ofAT (h : AT R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) :
    CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp :=
  ⟨h.wc, h.esl, ⟨h.pw, h.bscr, h.bbu, h.zscr, h.zbu, h.zb⟩, h.z118, h.z68, h.z70⟩

set_option maxRecDepth 20000 in
/-- `CPF` through own stores into `StS` slots -/
theorem CPF.stores (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) {M' : Memory} {ws : List (Nat × Nat)}
    (hF : MemFrame M M' ws) (hrg : M'.regions = M.regions) (hws : ∀ q ∈ ws, StS sp q) :
    CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s M' L1 b1 zzp tp := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  unfold Apart at hstw
  have hbW := scr_win hP h.tz.bscr
  unfold Apart at hbW
  have kO : ∀ a k, (a + k ≤ sp - 0x8 ∨ (sp ≤ a ∧ a + k ≤ sp + 0x60) ∨ (sp + 0x68 ≤ a ∧ a + k ≤ sp + 0x78) ∨
      (sp + 0x108 ≤ a ∧ a + k ≤ sp + 0x128) ∨ sp + 0x148 ≤ a) → M'.readLE a k = M.readLE a k := fun a k ha =>
    hF.readLE a k (outside_of_forall fun q hq => by have := hws q hq; simp only [StS] at this; omega)
  have kB : ∀ a k, tp ≤ a → a + k ≤ tp + 8 * P2Pre.NB 16 lm → M'.readLE a k = M.readLE a k := fun a k h1 h2 =>
    hF.readLE a k (outside_of_forall fun q hq => by have := hws q hq; simp only [StS] at this; omega)
  obtain ⟨e0, e1, e2⟩ := hdr3 (M := M) (M' := M') (st := st) fun j hj =>
    hF.readLE _ _ (outside_of_forall fun q hq => by have := hws q hq; simp only [StS] at this; omega)
  refine ⟨WC.win hP h.wc hF hrg fun q hq => ?_, ESl.keep h.esl (fun a k ha => kO a k (by omega)),
    h.tz.keep hF.accessible (LiveExt.refl R L1) e0 e1 e2 fun a k ha => ?_, by rw [kO _ _ (by omega)]; exact h.z118,
    by rw [kO _ _ (by omega)]; exact h.z68, by rw [kO _ _ (by omega)]; exact h.z70⟩
  · have := hws q hq; simp only [StS] at this; simp only [InWN]; omega
  · rcases ha with ha | ha
    · exact kO a k (by omega)
    · exact kB a k ha.1 ha.2

set_option maxRecDepth 20000 in
/-- `CPF` through a live allocation -/
theorem CPF.alloc (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    (h : CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) {m : Memory} {p rr n : Nat}
    (hA : AllocR R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 (lvlL (stLen s.mem st) lm) m p rr n) :
    CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s m (L1 ++ [(p, p + rr)]) (b1 - rr) zzp tp := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstw, -⟩ := hP'
  unfold Apart at hstw
  have hbW := scr_win hP h.tz.bscr
  unfold Apart at hbW
  have hsok := h.wc.sok
  obtain ⟨e0, e1, e2⟩ := hdr3 (M := M) (M' := m) (st := st) fun j hj =>
    hA.rdH _ _ (hsok.2.1.sub (by omega) (by omega)) (by unfold Apart; omega)
  have hx : LiveExt R L1 (L1 ++ [(p, p + rr)]) :=
    LiveExt.single (by rw [show p + rr - p = rr by omega]; exact hA.rin)
      (by rw [show p + rr - p = rr by omega]; exact hA.rap)
  refine ⟨hA.wc, ESl.keep h.esl (fun a k ha => hA.keep a k (by omega)),
    h.tz.keep hA.macc hx e0 e1 e2 fun a k ha => ?_, by rw [hA.keep _ _ (by omega)]; exact h.z118,
    by rw [hA.keep _ _ (by omega)]; exact h.z68, by rw [hA.keep _ _ (by omega)]; exact h.z70⟩
  rcases ha with ha | ha
  · exact hA.keep a k (by omega)
  · exact hA.rdH a k (h.tz.bscr.held.sub ha.1 ha.2) (by unfold Apart; omega)

theorem e8n (n : Nat) (hn : n ≤ 2 ^ 16) : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  omega

/-- `yi <<= 64 - 2k` with the `SBBQ` mask (`k = kk - 1 > 0`) -/
theorem eBX (yi kk : Nat) (h1 : 1 ≤ kk) (h2 : kk ≤ 16) (hyi : yi < 2 ^ 64) :
    (BitVec.ofNat 64 yi <<< ((18446744073709551616 - (kk - 1) * 4) % 64) &&&
      if 18446744073709551616 - (18446744073709551552 + (kk - 1) * 4) < 64 then 18446744073709551615#64 else 0#64) =
      BitVec.ofNat 64 (yi * 2 ^ (64 - (kk - 1) * 4) % 2 ^ 64) := by
  by_cases hk : kk = 1
  · subst hk
    simp
  · rw [if_pos (by omega), show (18446744073709551616 - (kk - 1) * 4) % 64 = 64 - (kk - 1) * 4 by omega]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt hyi, Nat.and_comm]
    rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by rfl,
      show ((2 : Nat) ^ 64 - 1) % 2 ^ 64 = 2 ^ 64 - 1 by decide, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod]

/-- the same with the shift count `0` (`k = 0`): the mask clears `yi` -/
theorem eBX0 (yi kk : Nat) (h2 : kk ≤ 16) (h0 : (18446744073709551616 - (kk - 1) * 4) % 64 = 0) :
    (BitVec.ofNat 64 yi &&&
      if 18446744073709551616 - (18446744073709551552 + (kk - 1) * 4) < 64 then 18446744073709551615#64 else 0#64) =
      BitVec.ofNat 64 (yi * 2 ^ (64 - (kk - 1) * 4) % 2 ^ 64) := by
  have hk : kk - 1 = 0 := by omega
  rw [if_neg (by omega), hk]
  simp

theorem kk2 (kk : Nat) (h1 : 1 ≤ kk) (h : kk ≤ 16) : BitVec.ofNat 64 kk - 2#64 = BitVec.ofNat 64 (kk - 1) - 1#64 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **from the copy point to the loop test** -/
theorem cpC {impl : List Amd64.Segment} (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (ret0 : W64) (Q : State → Prop) (hP : EPre R b L K g fs sp st bp r zp zc xp xl xc yp yl lm s)
    {kk cst FV : Nat} {r5 : W64}
    (KL : KL impl ret0 Q R b L K g sp st bp r zp zc xp xl xc yp yl lm s r5 zzp tp kk cst FV)
    (hc : CPF R L K g sp st bp r zp zc xp xl xc yp yl lm s M L1 b1 zzp tp) {dp dc n d i yi : Nat}
    (hub : UB R L K g sp st zp zc M L1 zzp tp lm dp dc) (hnd : n ≤ dc) (hn1 : 0 < n) (hd : d < 16)
    (hZo : Exp.p2Pow lm (natVal s.mem xp xl) d % 2 = 1)
    (hlen : M.readLE (sp + 0x148 + 24 * d + 8) 8 = n)
    (s0e8 : M.readLE (sp + 0xf8) 8 = yi) (s0c0 : M.readLE (sp + 0xf0) 8 = kk)
    (s0f0 : M.readLE (sp + 0xe8) 8 = (kk - 1) * 4) (s0c8 : M.readLE (sp + 0xd0) 8 = i)
    (hkk1 : 1 ≤ kk) (hkk : kk ≤ 16) (hi : i < yl) (hyi : yi < 2 ^ 64)
    (hbud : b + (kk - 1 + 16 * i) * bc lm + P2Pre.tC lm ≤ b1 + cst)
    (hFV : Exp.outerLoop 4 (stp lm (natVal s.mem xp xl)) (natVal s.mem yp yl) 16 i
      (yi * 2 ^ (64 - (kk - 1) * 4) % 2 ^ 64) (kk - 1) (Exp.p2Pow lm (natVal s.mem xp xl) d) = FV)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 CP) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (h5 : S.regs 5 = r5) (hfs : S.fsBase = s.fsBase) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false) (hm : S.mem = M)
    (h6 : S.regs 6 = BitVec.ofNat 64 n) (h8 : S.regs 8 = BitVec.ofNat 64 n) (h9 : S.regs 9 = BitVec.ofNat 64 dp)
    (h13 : S.regs 13 = BitVec.ofNat 64 dc) (h15 : S.regs 15 = BitVec.ofNat 64 (tp + 8 * (d * W lm))) :
    ReachesRet (LibW.program.link impl) ret0 S Q := by
  have hK : 41512 ≤ K := hP.1.2.2.2.2.2.2.1
  have hK0 : K ≤ sp - 0x8 := hP.cenv0.2.1
  have hlm := hP.2.2.2.2.2.1
  have hdc0 : 0 < dc := by omega
  obtain ⟨-, hdH, hdacc, hd48⟩ := hub.live hdc0
  obtain ⟨hdW, -, -, -, -, -, hdB⟩ := hub.ap hdc0
  have hc40 := hub.c40
  obtain ⟨-, -, d2, -, -⟩ := hc.tz.pw d hd
  rw [hlen] at d2
  have eW : P2Pre.W lm = W lm := rfl
  rw [eW] at d2
  have hjW : (d + 1) * W lm ≤ P2Pre.NB 16 lm := by
    simp only [P2Pre.NB]; exact Nat.mul_le_mul_right _ (by omega)
  have hjj : d * W lm + W lm ≤ P2Pre.NB 16 lm := by rw [← Nat.succ_mul]; exact hjW
  have hW128 : W lm ≤ 128 := by simp only [W]; omega
  have hbs := hc.tz.bscr
  have hb48 := hbs.b48
  have hbacc := hbs.acc
  have hbW := scr_win hP hbs
  unfold Apart at hdW hbW hdB
  have hne : (BitVec.ofNat 64 dp = BitVec.ofNat 64 (tp + 8 * (d * W lm))) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hwacc : M.accessible (sp - 0x8 - K) (K + 0x360) true = true := (hc.wc.cenv hP).2.2.2.1
  have hwaccF : M.accessible (sp - 0x8 - K) (K + 0x360) false = true := Janus.Arm64.Memory.accessible_weaken _ hwacc
  have hw0 := hc.wc
  have hsl0 := hc.esl
  have htz0 := hc.tz
  have z118 := hc.z118
  have z68 := hc.z68
  have z70 := hc.z70
  have hwH : HdM (WC R (HW (stLen s.mem st) lm) L K g sp st zp zc s.mem M L1 b1 (lvlL (stLen s.mem st) lm)) := ⟨hw0⟩
  have hslH : HdM (ESl M sp st bp r zp zc xp xl xc yp yl lm (stLen s.mem st)) := ⟨hsl0⟩
  have htzH : HdM (TZ R L s.mem M L1 st sp zzp tp lm (natVal s.mem xp xl)) := ⟨htz0⟩
  have hubH : HdM (UB R L K g sp st zp zc M L1 zzp tp lm dp dc) := ⟨hub⟩
  clear hc hw0 hsl0 htz0 hub hbs
  subst hm
  janus64_run [hne, e8n n (by omega), hwacc, hwaccF] until [mvE]
  have hF1 : MemFrame S.mem ((((S.mem.writeLE (sp + 0x80) 8 n).writeLE (sp + 0x90) 8 dc).writeLE (sp + 0x130) 8 dp).writeLE
      (sp - 0x8) 8 6199399) [(sp + 0x80, sp + 0x88), (sp + 0x90, sp + 0x98), (sp + 0x130, sp + 0x138), (sp - 0x8, sp)] := by
    janus_frame
  have hrg1 : ((((S.mem.writeLE (sp + 0x80) 8 n).writeLE (sp + 0x90) 8 dc).writeLE (sp + 0x130) 8 dp).writeLE
      (sp - 0x8) 8 6199399).regions = S.mem.regions := by simp only [Janus.Arm64.Memory.regions_writeLE]
  have rpu : ((((S.mem.writeLE (sp + 0x80) 8 n).writeLE (sp + 0x90) 8 dc).writeLE (sp + 0x130) 8 dp).writeLE
      (sp - 0x8) 8 6199399).readLE (sp - 0x8) 8 = 6199399 := Janus.Arm64.Memory.readLE_writeLE_self ..
  have r80 : ((((S.mem.writeLE (sp + 0x80) 8 n).writeLE (sp + 0x90) 8 dc).writeLE (sp + 0x130) 8 dp).writeLE
      (sp - 0x8) 8 6199399).readLE (sp + 0x80) 8 = n := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have r90 : ((((S.mem.writeLE (sp + 0x80) 8 n).writeLE (sp + 0x90) 8 dc).writeLE (sp + 0x130) 8 dp).writeLE
      (sp - 0x8) 8 6199399).readLE (sp + 0x90) 8 = dc := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have r128 : ((((S.mem.writeLE (sp + 0x80) 8 n).writeLE (sp + 0x90) 8 dc).writeLE (sp + 0x130) 8 dp).writeLE
      (sp - 0x8) 8 6199399).readLE (sp + 0x130) 8 = dp := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]; omega
  have hw1 := WC.win hP hwH.h hF1 hrg1 (by
    intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp only [InWN] <;> omega)
  have hra : ((((S.mem.writeLE (sp + 0x80) 8 n).writeLE (sp + 0x90) 8 dc).writeLE (sp + 0x130) 8 dp).writeLE
      (sp - 0x8) 8 6199399).readLE (sp - 0x8) 8 < 2 ^ 47 := by rw [rpu]; decide
  generalize hM1 : (((S.mem.writeLE (sp + 0x80) 8 n).writeLE (sp + 0x90) 8 dc).writeLE (sp + 0x130) 8 dp).writeLE
      (sp - 0x8) 8 6199399 = M1 at hF1 hrg1 rpu r80 r90 r128 hw1 hra ⊢
  have k1 : ∀ a k, (a + k ≤ sp - 0x8 ∨ (sp ≤ a ∧ a + k ≤ sp + 0x80) ∨ (sp + 0x88 ≤ a ∧ a + k ≤ sp + 0x90) ∨
      (sp + 0x98 ≤ a ∧ a + k ≤ sp + 0x130) ∨ sp + 0x138 ≤ a) → M1.readLE a k = S.mem.readLE a k := fun a k ha =>
    hF1.readLE a k (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hsacc : S.mem.accessible (tp + 8 * (d * W lm)) (8 * n) false = true :=
    Janus.Arm64.Memory.accessible_weaken _ (Janus.Arm64.Memory.accessible_mono _ hbacc (by omega) (by omega))
  refine mvCallW hmv hP hw1 (d := dp) (src := tp + 8 * (d * W lm)) (n := 8 * n) (by omega) (by omega) (by omega)
    (by omega) (by rw [hF1.accessible]; exact hsacc)
    (by unfold Apart; omega) (by omega)
    (by rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hdacc (Nat.le_refl _) (by omega))
    (hdH.sub (Nat.le_refl _) (by omega)) (by unfold Apart; omega) _ ?_ ?_ ?_ rfl hra ?_ ?_ ?_ ?_ ?_
    (fun junk f x yh m zh kr hF2 hLF2 hinv2 hcp hrg2 => ?_)
  all_goals first | (janus64_simp; done) | skip
  case refine_2 =>
    simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  -- after the copy: the reloads
  have hsl1 := hslH.h
  obtain ⟨-, -, -, -, -, -, -, -, r208, -, -, -, r1d8, r1e0, r228, -⟩ := hsl1
  have km : ∀ a, sp + 0x18 ≤ a → a + 8 ≤ sp + 0x358 → m.readLE a 8 = M1.readLE a 8 := fun a h1 h2 =>
    mv_rdW hP hF2 (Or.inr ⟨h1, h2⟩) (by unfold Apart; omega)
  have q228 : m.readLE (sp + 0x350) 8 = lm := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact r228
  have q0f0 : m.readLE (sp + 0xe8) 8 = (kk - 1) * 4 := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact s0f0
  have q1d8 : m.readLE (sp + 0x300) 8 = yp := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact r1d8
  have q0e8 : m.readLE (sp + 0xf8) 8 = yi := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact s0e8
  have q1e0 : m.readLE (sp + 0x308) 8 = yl := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact r1e0
  have q128 : m.readLE (sp + 0x130) 8 = dp := by rw [km _ (by omega) (by omega)]; exact r128
  have q0c0 : m.readLE (sp + 0xf0) 8 = kk := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact s0c0
  have q0c8 : m.readLE (sp + 0xd0) 8 = i := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact s0c8
  have q090 : m.readLE (sp + 0x90) 8 = dc := by rw [km _ (by omega) (by omega)]; exact r90
  have q208 : m.readLE (sp + 0x330) 8 = st := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact r208
  have q070 : m.readLE (sp + 0x70) 8 = 2 * W lm := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact z70
  have q068 : m.readLE (sp + 0x68) 8 = 2 * W lm := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact z68
  have q080 : m.readLE (sp + 0x80) 8 = n := by rw [km _ (by omega) (by omega)]; exact r80
  have q118 : m.readLE (sp + 0x120) 8 = zzp := by rw [km _ (by omega) (by omega), k1 _ _ (by omega)]; exact z118
  have hwacc2 : m.accessible (sp - 0x8 - K) (K + 0x360) true = true := by rw [hF2.accessible, hF1.accessible]; exact hwacc
  have hwaccF2 : m.accessible (sp - 0x8 - K) (K + 0x360) false = true :=
    Janus.Arm64.Memory.accessible_weaken _ hwacc2
  have hWl : 2 * W lm < 2 ^ 64 := by omega
  have hFH : HdM (MemFrame M1 m (R.rt ++ [(sp - 0x8 - 4096, sp - 0x8), (sp, sp + 0x18)] ++ [(dp, dp + 8 * n)])) := ⟨hF2⟩
  have hLFH : HdM (LiveFrame M1 m L1 [(dp, dp + 8 * n)]) := ⟨hLF2⟩
  have hiH : HdM (R.inv (b1 + stkR (HW (stLen s.mem st) lm) M1 st) L1 g (view R.rt L1 m)) := ⟨hinv2⟩
  have hcpH : HdM (Mem.Copied M1 m dp (tp + 8 * (d * W lm)) (8 * n)) := ⟨hcp⟩
  have hF1H : HdM (MemFrame S.mem M1 [(sp + 0x80, sp + 0x88), (sp + 0x90, sp + 0x98), (sp + 0x130, sp + 0x138),
    (sp - 0x8, sp)]) := ⟨hF1⟩
  clear hF2 hLF2 hinv2 hcp hF1 km k1 hw1
  janus64_run [q228, q0f0, q1d8, q0e8, q1e0, q128, q0c0, q0c8, q090, q208, q070, q068, q080, q118, hwacc2,
    hwaccF2] until [LT]
  all_goals
    refine KL _ _ L1 b1 i (kk - 1) (yi * 2 ^ (64 - (kk - 1) * 4) % 2 ^ 64) (Exp.p2Pow lm (natVal s.mem xp xl) d)
      dp n dc zzp (2 * W lm) (2 * W lm) true ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (li_first hP hwH.h hslH.h htzH.h hubH.h hnd hn1 hd hZo hlen hF1H.h hrg1 hFH.h hLFH.h hiH.h hcpH.h hrg2
        (by janus_frame) (by simp only [Janus.Arm64.Memory.regions_writeLE])
        (by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
            simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega)
        (by rw [Janus.Arm64.Memory.readLE_writeLE_self]; omega))
      hi (Nat.mod_lt _ (by decide)) (by omega) (by simp only [true_iff]; omega) hbud hFV
  all_goals first | (janus64_simp [eBX yi kk hkk1 hkk hyi, kk2 kk hkk1 hkk, hfs]; done) | skip
  all_goals first | (janus64_simp [eBX0 yi kk hkk hbr, kk2 kk hkk1 hkk, hfs]; done) | skip

end

end FvModexp.Amd64.P2W4
