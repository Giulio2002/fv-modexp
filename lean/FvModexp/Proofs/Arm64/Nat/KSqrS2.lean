import FvModexp.Proofs.Arm64.Nat.KSqrB

/-!
# `karatsubaSqr` (arm64): `z0.abs = z0.abs.sqr(stk, x0.abs)` (natmul.go:300), `0x1bc4ac` → `0x1bc4d0`

From the boundary after `clear(z)` (`z[0:2n] = 0`): the call (`ks_sqcall`; `z0 = z[0:2·n2]` reused, exactly
`z[0:2·len x0]` written, holding `x0²`), then the stores of the result into `z0`'s header.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- `natVal` of `x[:len x0]` at a `KM` memory is `X0` -/
theorem KM.x0val {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) : natVal M xp lx0 = kX0 s xp n := by
  have hl := h.l0; simp only [kn2] at hl
  show natVal M xp lx0 = natVal s.mem xp (kn2 n)
  rw [← h.v0]; unfold natVal; exact h.xrd (Nat.le_refl _) (by omega)

/-- **`KB4`** at the state after the header stores (`0x1bc4d0`), from `KB3` (memory `S3.mem`), the inner square's
facts (memory `Q`) and the frame of the stores -/
theorem kS2fin (impl : List Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk3 : List (Nat × Nat)} {bk3 l1 : Nat} {S3 : State}
    (hB : KB3 R b L W st zp zc xp n xc s lx0 lx1 t S3 Lk3 bk3 l1) {Lk : List (Nat × Nat)} {bk l0 : Nat}
    {Q : Memory} (hkmQ : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc4 (stLen s.mem st) n) Q)
    {S1 : State} (hsp1 : S1.sp.toNat = s.sp.toNat - 320)
    (hF : MemFrame S3.mem Q (R.rt ++ winA S1 (W - 320) 64 ++ [(zp, zp + 8 * (2 * lx0))] ++ stkWs S3.mem st))
    (hLF : LiveFrame S3.mem Q Lk3 ([(zp, zp + 8 * (2 * lx0))] ++ stkWs S3.mem st))
    (hv2 : natVal Q zp (2 * lx0) = natVal S3.mem xp lx0 * natVal S3.mem xp lx0)
    (hval : natVal Q zp l0 = natVal S3.mem xp lx0 * natVal S3.mem xp lx0) (hnn : NatNorm Q zp l0)
    (hl2 : l0 ≤ 2 * lx0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bc4d0) (hsp : S.sp = s.sp - 320#64)
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 328#64) (h18 : S.regs 18 = s.regs 18)
    (hfr : MemFrame Q S.mem [(s.sp.toNat - 104, s.sp.toNat - 80)]) (hreg : S.mem.regions = Q.regions)
    (q0 : S.mem.readLE (s.sp.toNat - 104) 8 = zp) (q1 : S.mem.readLE (s.sp.toNat - 96) 8 = l0)
    (q2 : S.mem.readLE (s.sp.toNat - 88) 8 = zc)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 : Nat),
      KB4 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S := by
  have hkm3 := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkm3.lay
  obtain ⟨-, htw, -, htz, -, -⟩ := hkm3.tops
  obtain ⟨-, -, hzw, -, -, -, -, -, -, -⟩ := hkm3.zops
  simp only [win, outside_cons, outside_nil, and_true] at htw hzw
  unfold Apart at htz
  have hl0 := hkm3.l0; simp only [kn2] at hl0
  have hl1 := hB.hl1; simp only [kn2] at hl1
  -- through the store frame and the call
  have hk : ∀ x m, (x + m ≤ s.sp.toNat - 104 ∨ s.sp.toNat - 80 ≤ x) → S.mem.readLE x m = Q.readLE x m :=
    fun x m h => hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hfrm : ∀ x m, s.sp.toNat - 256 ≤ x → x + m ≤ s.sp.toNat + 48 → Q.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => hkm3.sqRd hsp1 hF (by omega) h1 h2
  have hzt : ∀ x m, ((zp ≤ x ∧ x + m ≤ zp + 8 * zc) ∨ (t ≤ x ∧ x + m ≤ t + 8 * kT n)) →
      (x + m ≤ zp ∨ zp + 8 * (2 * lx0) ≤ x) → Q.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => hkm3.sqKeep hsp1 hF hLF h1 h2
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
  have hkS := hkmQ.store (ws := [(s.sp.toNat - 104, s.sp.toNat - 80)])
    (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
                    exact ⟨by simp only; omega, Or.inr ⟨by simp only; omega, by simp only; omega⟩⟩) hfr hreg
  have hkf : ∀ x m, s.sp.toNat - 256 ≤ x → x + m ≤ s.sp.toNat - 104 → S.mem.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => (hk x m (by omega)).trans (hfrm x m h1 (by omega))
  have hkt : ∀ x m, t ≤ x → x + m ≤ t + 8 * kT n → S.mem.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => (hk x m (by omega)).trans (hzt x m (Or.inr ⟨h1, h2⟩) (by omega))
  obtain ⟨n0, -, -, -⟩ := hB.z0h
  refine hK S Lk bk l1 l0 ⟨⟨hpc, hsp, h28, h29, h18⟩, hkS, hB.z1h.keep fun x m h1 h2 => hkf x m (by omega) (by omega),
    hB.hl1, ?_, ?_, ⟨(hkf _ _ (by omega) (by omega)).trans n0, by rw [show s.sp.toNat - 112 + 8 = s.sp.toNat - 104 by omega]; exact q0,
      by rw [show s.sp.toNat - 112 + 16 = s.sp.toNat - 96 by omega]; exact q1,
      by rw [show s.sp.toNat - 112 + 24 = s.sp.toNat - 88 by omega]; exact q2⟩,
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
/-- the stores of `z0`'s new header (`0x1bc4c4 → 0x1bc4d0`), then `kS2fin` -/
theorem kS2st (impl : List Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk3 : List (Nat × Nat)} {bk3 l1 : Nat} {S3 : State}
    (hB : KB3 R b L W st zp zc xp n xc s lx0 lx1 t S3 Lk3 bk3 l1) {Lk : List (Nat × Nat)} {bk l0 : Nat}
    {S1 : State} (hsp1 : S1.sp.toNat = s.sp.toNat - 320) (Q : State)
    (hkmQ : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc4 (stLen s.mem st) n) Q.mem)
    (hF : MemFrame S3.mem Q.mem (R.rt ++ winA S1 (W - 320) 64 ++ [(zp, zp + 8 * (2 * lx0))] ++ stkWs S3.mem st))
    (hLF : LiveFrame S3.mem Q.mem Lk3 ([(zp, zp + 8 * (2 * lx0))] ++ stkWs S3.mem st))
    (hv2 : natVal Q.mem zp (2 * lx0) = natVal S3.mem xp lx0 * natVal S3.mem xp lx0)
    (hval : natVal Q.mem zp l0 = natVal S3.mem xp lx0 * natVal S3.mem xp lx0) (hnn : NatNorm Q.mem zp l0)
    (hl2 : l0 ≤ 2 * lx0)
    (hpc : Q.pc = BitVec.ofNat 64 0x1bc4c4) (hsp : Q.sp = s.sp - 320#64)
    (h28 : Q.regs 28 = s.regs 28) (h29 : Q.regs 29 = s.sp - 328#64) (h18 : Q.regs 18 = s.regs 18)
    (r0 : Q.regs 0 = BitVec.ofNat 64 zp) (r1 : Q.regs 1 = BitVec.ofNat 64 l0) (r2 : Q.regs 2 = BitVec.ofNat 64 zc)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 : Nat),
      KB4 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s Q := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkmQ.lay
  have hw0 : s.mem.accessible (s.sp.toNat - W) (W + 48) true = true := hkmQ.pre.1.2.1.2.2.2
  have hsacc : Q.mem.accessible (s.sp.toNat - 328) 376 true = true := by
    rw [hkmQ.fr.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := hkmQ.zops.2.2.2.2.2.2.2.2.2
  have hl0' : l0 < 2 ^ 64 := by have := hkmQ.l0; simp only [kn2] at this; omega
  unfold KGoal
  janus_run until [0x1bc4d0]
  refine kS2fin impl R hB hkmQ hsp1 hF hLF hv2 hval hnn hl2 _ rfl rfl ?_ ?_ ?_ ?fr ?reg ?q0 ?q1 ?q2 hK
  case fr => janus_frame
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KB3 → KB4`**: the loads and the inner `nat.sqr(z0 ← x0)` (`ks_sqcallR`, `z[0:2·n2]` reused), then `kS2st` -/
theorem kS2 (impl : List Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} (ih : ∀ a, IH impl R (2 * n) (false, a))
    {Lk : List (Nat × Nat)} {bk l1 : Nat} (S : State) (hB : KB3 R b L W st zp zc xp n xc s lx0 lx1 t S Lk bk l1)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 : Nat),
      KB4 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  obtain ⟨-, z0b, z0c, z0d⟩ := hB.z0h
  obtain ⟨-, x0b, x0c, x0d⟩ := hkm.x0h
  have q104 : S.mem.readLE (s.sp.toNat - 104) 8 = zp := by rw [show s.sp.toNat - 104 = s.sp.toNat - 112 + 8 by omega]; exact z0b
  have q96 : S.mem.readLE (s.sp.toNat - 96) 8 = 2 * kn2 n := by rw [show s.sp.toNat - 96 = s.sp.toNat - 112 + 16 by omega]; exact z0c
  have q88 : S.mem.readLE (s.sp.toNat - 88) 8 = zc := by rw [show s.sp.toNat - 88 = s.sp.toNat - 112 + 24 by omega]; exact z0d
  have q40 : S.mem.readLE (s.sp.toNat - 40) 8 = xp := by rw [show s.sp.toNat - 40 = s.sp.toNat - 48 + 8 by omega]; exact x0b
  have q32 : S.mem.readLE (s.sp.toNat - 32) 8 = lx0 := by rw [show s.sp.toNat - 32 = s.sp.toNat - 48 + 16 by omega]; exact x0c
  have q24 : S.mem.readLE (s.sp.toNat - 24) 8 = xc := by rw [show s.sp.toNat - 24 = s.sp.toNat - 48 + 24 by omega]; exact x0d
  have q328 : S.mem.readLE (s.sp.toNat + 8) 8 = st := hkm.s1
  clear z0b z0c z0d x0b x0c x0d
  have hst : st + 24 ≤ 2 ^ 48 := hkm.sok.2.2.2.1
  obtain ⟨-, hzlive, hzw, hzg, hzs, hne, -, -, -, hz48⟩ := hkm.zops
  obtain ⟨hl0x, -, hxacc, hxh, hxw, hxs, hzx⟩ := hkm.x0ops
  have hx48 : xp + 8 * xc ≤ 2 ^ 48 := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.1
  have hl0 := hkm.l0
  have hsc : kc3 (stLen s.mem st) n + kcS (stLen s.mem st) n ≤ ksqrC (stLen s.mem st) n := by
    have := kc7_le (ℓ := stLen s.mem st) h80; unfold kc7 kc6 kc5 kc4 at this; omega
  have hw0 : s.mem.accessible (s.sp.toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2.2
  have hsacc : S.mem.accessible (s.sp.toNat - 328) 376 false = true := by
    rw [hkm.fr.accessible]; exact Memory.accessible_sub _ hw0 (Or.inl rfl) (by omega) (by omega)
  clear hw0
  unfold KGoal
  janus_run [q104, q96, q88, q40, q32, q24, q328] until [0x1bb420]
  refine ks_sqcallR impl R hkm ih _ ?pcS ?sp ?g ?hm ?l4 ?l48 (zp' := zp) (zl' := 2 * kn2 n) (zc' := zc) (xp' := xp)
    (xl' := lx0) (xc' := xc) (by omega) (by simp only [kn2]; omega) (by omega) (by omega)
    (by omega) (by simp only [kn2] at hl0; omega) (by omega) ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 hl0 hl0x hxc40 hxacc hxh hxw
    hzc40 hzlive hzw (fun _ => ⟨hzg, hzs⟩) (fun _ _ => hzx) hxs (by simp only [kn2] at hl0; omega) hne
    (Or.inl ⟨Nat.le_refl _, by simp only [kn2] at hl0; omega⟩) hsc ?cont
  case cont =>
    intro s2 Lk' bk' l' hr hreg hk hkm' e0 e1 e2 hval hnn hl2 hv2 hF hLF
    have e320 : (s.sp - 320#64).toNat = s.sp.toNat - 320 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    refine kS2st impl R hB e320 s2 hkm' hF hLF hv2 hval hnn hl2 ?pc2 ?sp2 ?g2 ?f2 ?x2 e0 e1 e2 hK
    case pc2 => rw [hr]; rfl
    case sp2 => rw [hk.1]
    case g2 => rw [hk.2.1]; janus_simp
    case f2 => rw [hk.2.2.1]; janus_simp
    case x2 => rw [hk.2.2.2]; janus_simp
  case pcS => rfl
  case hm => rfl
  all_goals janus_simp

end FvModexp.Arm64.NatSqr
