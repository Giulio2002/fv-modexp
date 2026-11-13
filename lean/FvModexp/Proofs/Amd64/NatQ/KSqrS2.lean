import FvModexp.Proofs.Amd64.NatQ.KSqrB

/-!
# [amd64 port (divmc s38) of the Q-form Arm64/NatQ/KSqrS2.lean — TIGHT COSTS] `karatsubaSqr` (arm64): `z0.abs = z0.abs.sqr(stk, x0.abs)` (natmul.go:300), `0x5f2649` → `0x5f269e`

From the boundary after `clear(z)` (`z[0:2n] = 0`): the call (`ks_sqcall`; `z0 = z[0:2·n2]` reused, exactly
`z[0:2·len x0]` written, holding `x0²`), then the stores of the result into `z0`'s header.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

/-- `natVal` of `x[:len x0]` at a `KM` memory is `X0` -/
theorem KM.x0val {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) : natVal M xp lx0 = kX0 s xp n := by
  have hl := h.l0; simp only [kn2] at hl
  show natVal M xp lx0 = natVal s.mem xp (kn2 n)
  rw [← h.v0]; unfold natVal; exact h.xrd (Nat.le_refl _) (by omega)

/-- **`KB4`** at the state after the header stores (`0x5f269e`), from `KB3` (memory `S3.mem`), the inner square's
facts (memory `Q`) and the frame of the stores -/
theorem kS2fin (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk3 : List (Nat × Nat)} {bk3 l1 : Nat} {S3 : State}
    (hB : KB3 R b H L W st zp zc xp n xc s lx0 lx1 t S3 Lk3 bk3 l1) {Lk : List (Nat × Nat)} {bk l0 : Nat}
    {Q : Memory} (hkmQ : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc4 n) Q)
    (hF : MemFrame S3.mem Q (R.rt ++ [((s.regs 4).toNat - 320 - (W - 320), (s.regs 4).toNat - 320 + 64)] ++ [(zp, zp + 8 * (2 * lx0))] ++ stkWs S3.mem st))
    (hLF : LiveFrame S3.mem Q Lk3 ([(zp, zp + 8 * (2 * lx0))] ++ stkWs S3.mem st))
    (hv2 : natVal Q zp (2 * lx0) = natVal S3.mem xp lx0 * natVal S3.mem xp lx0)
    (hval : natVal Q zp l0 = natVal S3.mem xp lx0 * natVal S3.mem xp lx0) (hnn : NatNorm Q zp l0)
    (hl2 : l0 ≤ 2 * lx0)
    (S : State) (hA : KAt s S 0x5f269e)
    (hfr : MemFrame Q S.mem [((s.regs 4).toNat - 104, (s.regs 4).toNat - 80)]) (hreg : S.mem.regions = Q.regions)
    (q0 : S.mem.readLE ((s.regs 4).toNat - 104) 8 = zp) (q1 : S.mem.readLE ((s.regs 4).toNat - 96) 8 = l0)
    (q2 : S.mem.readLE ((s.regs 4).toNat - 88) 8 = zc)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 : Nat),
      KB4 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s S := by
  have hkm3 := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkm3.lay
  obtain ⟨-, htw, -, htz, -, -⟩ := hkm3.tops
  obtain ⟨-, -, hzw, -, -, -, -, -, -, -⟩ := hkm3.zops
  simp only [win, outside_cons, outside_nil, and_true] at htw hzw
  unfold Apart at htz
  have hl0 := hkm3.l0; simp only [kn2] at hl0
  have hl1 := hB.hl1; simp only [kn2] at hl1
  -- through the store frame and the call
  have hk : ∀ x m, (x + m ≤ (s.regs 4).toNat - 104 ∨ (s.regs 4).toNat - 80 ≤ x) → S.mem.readLE x m = Q.readLE x m :=
    fun x m h => hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hfrm : ∀ x m, (s.regs 4).toNat - 256 ≤ x → x + m ≤ (s.regs 4).toNat + 48 → Q.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => hkm3.sqRd hF (by omega) h1 h2
  have hzt : ∀ x m, ((zp ≤ x ∧ x + m ≤ zp + 8 * zc) ∨ (t ≤ x ∧ x + m ≤ t + 8 * kT n)) →
      (x + m ≤ zp ∨ zp + 8 * (2 * lx0) ≤ x) → Q.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => hkm3.sqKeep hF hLF h1 h2
  have hx0 := hkm3.x0val
  rw [hx0] at hv2 hval
  have hzz := hB.zz
  have hzero : ∀ i k, 2 * lx0 ≤ i → i + k ≤ 2 * n → natVal S.mem (zp + 8 * i) k = 0 := by
    intro i k h1 h2
    rw [← natVal_zero_part hzz h2]; unfold natVal
    rw [hk _ _ (by omega), hzt _ _ (Or.inl ⟨by omega, by omega⟩) (Or.inr (by omega))]
  have hzlo : natVal S.mem zp (2 * kn2 n) = kX0 s xp n * kX0 s xp n := by
    have e := natVal_add S.mem zp (2 * lx0) (2 * kn2 n - 2 * lx0)
    rw [show 2 * lx0 + (2 * kn2 n - 2 * lx0) = 2 * kn2 n by simp only [kn2]; omega] at e
    rw [e, hzero _ _ (Nat.le_refl _) (by simp only [kn2]; omega), Nat.mul_zero, Nat.add_zero, ← hv2]
    unfold natVal; exact hk _ _ (by omega)
  have hzhi : natVal S.mem (zp + 16 * kn2 n) (2 * n - 2 * kn2 n) = 0 := by
    rw [show zp + 16 * kn2 n = zp + 8 * (2 * kn2 n) by omega]
    exact hzero _ _ (by simp only [kn2]; omega) (by simp only [kn2]; omega)
  have hkS := hkmQ.store (ws := [((s.regs 4).toNat - 104, (s.regs 4).toNat - 80)])
    (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
                    exact ⟨by simp only; omega, Or.inr ⟨by simp only; omega, by simp only; omega⟩⟩) hfr hreg
  have hkf : ∀ x m, (s.regs 4).toNat - 256 ≤ x → x + m ≤ (s.regs 4).toNat - 104 → S.mem.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => (hk x m (by omega)).trans (hfrm x m h1 (by omega))
  have hkt : ∀ x m, t ≤ x → x + m ≤ t + 8 * kT n → S.mem.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => (hk x m (by omega)).trans (hzt x m (Or.inr ⟨h1, h2⟩) (by omega))
  obtain ⟨n0, -, -, -⟩ := hB.z0h
  refine hK S Lk bk l1 l0 ⟨hA, hkS, hB.z1h.keep fun x m h1 h2 => hkf x m (by omega) (by omega),
    hB.hl1, ?_, ?_, ⟨(hkf _ _ (by omega) (by omega)).trans n0, by rw [show (s.regs 4).toNat - 112 + 8 = (s.regs 4).toNat - 104 by omega]; exact q0,
      by rw [show (s.regs 4).toNat - 112 + 16 = (s.regs 4).toNat - 96 by omega]; exact q1,
      by rw [show (s.regs 4).toNat - 112 + 24 = (s.regs 4).toNat - 88 by omega]; exact q2⟩,
    by simp only [kn2]; omega, ?_, ?_, hB.z2h.keep fun x m h1 h2 => hkf x m (by omega) (by omega), hzlo, hzhi⟩
  · rw [← hB.z1v]; unfold natVal; exact hkt _ _ (Nat.le_refl _) (by simp only [kT, kn2]; omega)
  · rcases hB.z1n with h0 | h0
    · exact Or.inl h0
    · right; rwa [hkt _ _ (by omega) (by simp only [kT, kn2]; omega)]
  · rw [← hval]; unfold natVal; exact hk _ _ (by omega)
  · rcases hnn with h0 | h0
    · exact Or.inl h0
    · right; rwa [hk _ _ (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the stores of `z0`'s new header (`0x5f2686 → 0x5f269e`), then `kS2fin` -/
theorem kS2st (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk3 : List (Nat × Nat)} {bk3 l1 : Nat} {S3 : State}
    (hB : KB3 R b H L W st zp zc xp n xc s lx0 lx1 t S3 Lk3 bk3 l1) {Lk : List (Nat × Nat)} {bk l0 : Nat}
    (Q : State)
    (hkmQ : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc4 n) Q.mem)
    (hF : MemFrame S3.mem Q.mem (R.rt ++ [((s.regs 4).toNat - 320 - (W - 320), (s.regs 4).toNat - 320 + 64)] ++ [(zp, zp + 8 * (2 * lx0))] ++ stkWs S3.mem st))
    (hLF : LiveFrame S3.mem Q.mem Lk3 ([(zp, zp + 8 * (2 * lx0))] ++ stkWs S3.mem st))
    (hv2 : natVal Q.mem zp (2 * lx0) = natVal S3.mem xp lx0 * natVal S3.mem xp lx0)
    (hval : natVal Q.mem zp l0 = natVal S3.mem xp lx0 * natVal S3.mem xp lx0) (hnn : NatNorm Q.mem zp l0)
    (hl2 : l0 ≤ 2 * lx0) (hA : KAt s Q 0x5f2686)
    (r0 : Q.regs 0 = BitVec.ofNat 64 zp) (r1 : Q.regs 3 = BitVec.ofNat 64 l0) (r2 : Q.regs 1 = BitVec.ofNat 64 zc)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 : Nat),
      KB4 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s Q := by
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hA
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkmQ.lay
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := hkmQ.pre.1.2.1.2.2
  have hsacc : Q.mem.accessible ((s.regs 4).toNat - 320) 368 true = true := by
    rw [hkmQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := hkmQ.zops.2.2.2.2.2.2.2.2.2
  have hl0' : l0 < 2 ^ 64 := by have := hkmQ.l0; simp only [kn2] at this; omega
  have hsp' : (Q.regs 4).toNat = (s.regs 4).toNat - 312 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold KGoal
  janus64_run [hsp'] until [0x5f269e]
  refine kS2fin impl R hB hkmQ hF hLF hv2 hval hnn hl2 _ ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?fr ?reg ?q0 ?q1 ?q2 hK
  case fr => janus_frame
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KB3 → KB4`**: the loads and the inner `nat.sqr(z0 ← x0)` (`0x5f2681`, return `0x5f2686` pushed;
`ks_sqcallR`, `z[0:2·n2]` reused), then `kS2st` -/
theorem kS2 (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} (ih : ∀ a, IH impl R H (2 * n) (false, a)) (hx150 : s.xmm 15 = 0#128)
    (hdf0 : s.df = false)
    {Lk : List (Nat × Nat)} {bk l1 : Nat} (S : State) (hB : KB3 R b H L W st zp zc xp n xc s lx0 lx1 t S Lk bk l1)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 : Nat),
      KB4 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  obtain ⟨-, z0b, z0c, z0d⟩ := hB.z0h
  obtain ⟨-, x0b, x0c, x0d⟩ := hkm.x0h
  have q104 : S.mem.readLE ((s.regs 4).toNat - 104) 8 = zp := by
    rw [show (s.regs 4).toNat - 104 = (s.regs 4).toNat - 112 + 8 by omega]; exact z0b
  have q96 : S.mem.readLE ((s.regs 4).toNat - 96) 8 = 2 * kn2 n := by
    rw [show (s.regs 4).toNat - 96 = (s.regs 4).toNat - 112 + 16 by omega]; exact z0c
  have q88 : S.mem.readLE ((s.regs 4).toNat - 88) 8 = zc := by
    rw [show (s.regs 4).toNat - 88 = (s.regs 4).toNat - 112 + 24 by omega]; exact z0d
  have q40 : S.mem.readLE ((s.regs 4).toNat - 40) 8 = xp := by
    rw [show (s.regs 4).toNat - 40 = (s.regs 4).toNat - 48 + 8 by omega]; exact x0b
  have q32 : S.mem.readLE ((s.regs 4).toNat - 32) 8 = lx0 := by
    rw [show (s.regs 4).toNat - 32 = (s.regs 4).toNat - 48 + 16 by omega]; exact x0c
  have q24 : S.mem.readLE ((s.regs 4).toNat - 24) 8 = xc := by
    rw [show (s.regs 4).toNat - 24 = (s.regs 4).toNat - 48 + 24 by omega]; exact x0d
  have q8 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = st := hkm.s1
  clear z0b z0c z0d x0b x0c x0d
  have hst : st + 24 ≤ 2 ^ 48 := hkm.sok.2.2.2.1
  obtain ⟨-, hzlive, hzw, hzg, hzs, hne, -, -, -, hz48⟩ := hkm.zops
  obtain ⟨-, hzt⟩ := hkm.ttls
  obtain ⟨hl0x, -, hxacc, hxh, hxw, hxs, hzx⟩ := hkm.x0ops
  have hx48 : xp + 8 * xc ≤ 2 ^ 48 := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.1
  have hl0 := hkm.l0
  have hsc : kc3 n + kcS n ≤ ksqrCQ n := by
    have := kc7_le h80; unfold kc7 kc6 kc5 kc4 at this; omega
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 320) 368 true = true := by
    rw [hkm.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 312 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  -- the facts at the call memory (return address `0x5f2686` pushed at `SP - 320`)
  have hkmP := hkm.push 0x5f2686
  have hxw' : 0 < lx0 → xp + 8 * lx0 ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 48 ≤ xp := fun h0 => by
    have := hxw h0; simp only [win, outside_cons, outside_nil, and_true] at this; omega
  have hxaccP : (S.mem.writeLE ((s.regs 4).toNat - 320) 8 0x5f2686).accessible xp (8 * lx0) false = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]; exact hxacc
  have hzlP := pushLive (q := (s.regs 4).toNat - 320) (v := 0x5f2686) hzlive
  have hzsP := hkm.pushSep 0x5f2686 hzs
  have hxsP : 0 < lx0 → StkSep (S.mem.writeLE ((s.regs 4).toNat - 320) 8 0x5f2686) st xp (8 * lx0) :=
    fun h0 => hkm.pushSep 0x5f2686 (hxs h0)
  have hxvP : natVal (S.mem.writeLE ((s.regs 4).toNat - 320) 8 0x5f2686) xp lx0 = natVal S.mem xp lx0 := by
    rcases Nat.eq_zero_or_pos lx0 with h0 | h0
    · subst h0; simp [natVal]
    · unfold natVal; exact pushRd (by have := hxw' h0; omega)
  have hzw' : zp + 8 * zc ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 48 ≤ zp := by
    simp only [win, outside_cons, outside_nil, and_true] at hzw; omega
  obtain ⟨e1, e2, e3⟩ := hkm.pushHdr 0x5f2686
  have hLs := hkm.lsep
  unfold KGoal
  janus64_run [q104, q96, q88, q40, q32, q24, q8, hsp'] until [0x5f0fe0]
  refine ks_sqcallR impl R hkmP ih _ ?pcS ?sp ?g ?hm ?fs (ra := 0x5f2686) ?rv (by decide) ?x15 ?df ?h5 hx150 hdf0
    (zp' := zp) (zl' := 2 * kn2 n) (zc' := zc) (xp' := xp)
    (xl' := lx0) (xc' := xc) (by omega) (by simp only [kn2]; omega) (by omega) (by omega)
    (by omega) (by simp only [kn2] at hl0; omega) (by omega) ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 hl0 hl0x hxc40 hxaccP hxh hxw
    hzc40 hzlP hzw (fun _ => ⟨hzg, hzt, hzsP⟩) (fun _ _ => hzx) hxsP (by simp only [kn2] at hl0; omega) hne
    (Or.inl ⟨Nat.le_refl _, by simp only [kn2] at hl0; omega⟩) hsc ?cont
  case cont =>
    intro s2 Lk' bk' l' hA2 hreg hkm' e0 e1' e2' hval hnn hl2 hv2 hF hLF
    rw [hxvP] at hval hv2
    have hF' : MemFrame S.mem s2.mem (R.rt ++ [((s.regs 4).toNat - 320 - (W - 320), (s.regs 4).toNat - 320 + 64)] ++ [(zp, zp + 8 * (2 * lx0))] ++ stkWs S.mem st) := by
      have := pushFrame (rt := R.rt) (w := [((s.regs 4).toNat - 320 - (W - 320), (s.regs 4).toNat - 320 + 64)]) (ws := [(zp, zp + 8 * (2 * lx0))] ++ stkWs S.mem st)
        (q := (s.regs 4).toNat - 320) (v := 0x5f2686) (M := S.mem) (M' := s2.mem)
        (fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega)
      simp only [stkWs, BasicSqr.freeP, BasicSqr.freeN, e1, e2, e3, List.append_assoc] at hF this ⊢
      exact this hF
    have hLF' : LiveFrame S.mem s2.mem Lk ([(zp, zp + 8 * (2 * lx0))] ++ stkWs S.mem st) := by
      have := pushLF (M := S.mem) (M' := s2.mem) (q := (s.regs 4).toNat - 320) (v := 0x5f2686) (Lk := Lk)
        (ws := [(zp, zp + 8 * (2 * lx0))] ++ stkWs S.mem st)
        (fun r hr => by have := hLs r hr; simp only [outside_cons, outside_nil, and_true]; omega)
      simp only [stkWs, BasicSqr.freeP, BasicSqr.freeN, e1, e2, e3] at hLF this ⊢
      exact this hLF
    exact kS2st impl R hB s2 hkm' hF' hLF' hv2 hval hnn hl2 hA2 e0 e1' e2' hK
  case pcS => rfl
  case hm => rfl
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega

end FvModexp.Amd64.Q.NatSqr
