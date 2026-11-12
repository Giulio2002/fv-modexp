import FvModexp.Proofs.Arm64.Nat.KSqrB

/-!
# `karatsubaSqr` (arm64): `z2.abs = z2.abs.sqr(stk, x1.abs)` (natmul.go:301), `0x1bc4d0` → `0x1bc4f4`

From `KB4`: the call (`ks_sqcallR`; `z2 = z[2·n2:]` reused, exactly `z[2n2:2n2 + 2·len x1]` written, holding `x1²`),
then the stores of the result into `z2`'s header.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

theorem StkSep.shift {m : Memory} {st p k p' k' : Nat} (h : StkSep m st p k) (h1 : p ≤ p') (h2 : p' + k' ≤ p + k) :
    StkSep m st p' k' := by
  obtain ⟨a, b, c⟩ := h; unfold Apart at a b c
  exact ⟨by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega⟩

/-- `natVal` of `x[n2:][:len x1]` at a `KM` memory is `X1` -/
theorem KM.x1val {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    natVal M (xp + 8 * kn2 n) lx1 = kX1 s xp n := by
  have hl := h.l1; simp only [kn2] at hl
  show natVal M (xp + 8 * kn2 n) lx1 = natVal s.mem (xp + 8 * kn2 n) (n - kn2 n)
  rw [← h.v1]; unfold natVal; exact h.xrd (by omega) (by simp only [kn2]; omega)

/-- the written part of `z2`: `[zp + 16·n2, zp + 16·n2 + 16·lx1)` -/
@[reducible] def kq2 (zp n : Nat) : Nat := zp + 16 * kn2 n

/-- **`KB5`** at the state after the header stores (`0x1bc4f4`), from `KB4` (memory `S3.mem`), the inner square's
facts (memory `Q`) and the frame of the stores -/
theorem kS3fin (impl : List Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk3 : List (Nat × Nat)} {bk3 l1 l0 : Nat} {S3 : State}
    (hB : KB4 R b L W st zp zc xp n xc s lx0 lx1 t S3 Lk3 bk3 l1 l0) {Lk : List (Nat × Nat)} {bk l2 : Nat}
    {Q : Memory} (hkmQ : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc5 (stLen s.mem st) n) Q)
    {S1 : State} (hsp1 : S1.sp.toNat = s.sp.toNat - 320)
    (hF : MemFrame S3.mem Q (R.rt ++ winA S1 (W - 320) 64 ++ [(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++
      stkWs S3.mem st))
    (hLF : LiveFrame S3.mem Q Lk3 ([(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++ stkWs S3.mem st))
    (hv2 : natVal Q (kq2 zp n) (2 * lx1) = natVal S3.mem (xp + 8 * kn2 n) lx1 * natVal S3.mem (xp + 8 * kn2 n) lx1)
    (hval : natVal Q (kq2 zp n) l2 = natVal S3.mem (xp + 8 * kn2 n) lx1 * natVal S3.mem (xp + 8 * kn2 n) lx1)
    (hnn : NatNorm Q (kq2 zp n) l2) (hl2 : l2 ≤ 2 * lx1)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 0x1bc4f4) (hsp : S.sp = s.sp - 320#64)
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 328#64) (h18 : S.regs 18 = s.regs 18)
    (hfr : MemFrame Q S.mem [(s.sp.toNat - 136, s.sp.toNat - 112)]) (hreg : S.mem.regions = Q.regions)
    (q0 : S.mem.readLE (s.sp.toNat - 136) 8 = kq2 zp n) (q1 : S.mem.readLE (s.sp.toNat - 128) 8 = l2)
    (q2 : S.mem.readLE (s.sp.toNat - 120) 8 = zc - 2 * kn2 n)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 l2 : Nat),
      KB5 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 l2 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S := by
  have hkm3 := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkm3.lay
  obtain ⟨-, htw, -, htz, -, -⟩ := hkm3.tops
  obtain ⟨-, -, hzw, -, -, -, -, -, -, -⟩ := hkm3.zops
  simp only [win, outside_cons, outside_nil, and_true] at htw hzw
  unfold Apart at htz
  have hl1x := hkm3.l1
  have hl1 := hB.hl1
  have hl0 := hB.hl0
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  have hkT : kT n = 2 * kn2 n + 1 := rfl
  simp only [kq2] at hF hLF hv2 hval hnn q0
  have hk : ∀ x m, (x + m ≤ s.sp.toNat - 136 ∨ s.sp.toNat - 112 ≤ x) → S.mem.readLE x m = Q.readLE x m :=
    fun x m h => hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hfrm : ∀ x m, s.sp.toNat - 256 ≤ x → x + m ≤ s.sp.toNat + 48 → Q.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => hkm3.sqRd hsp1 hF (by omega) h1 h2
  have hzt : ∀ x m, ((zp ≤ x ∧ x + m ≤ zp + 8 * zc) ∨ (t ≤ x ∧ x + m ≤ t + 8 * kT n)) →
      (x + m ≤ zp + 16 * kn2 n ∨ zp + 16 * kn2 n + 8 * (2 * lx1) ≤ x) → Q.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => hkm3.sqKeep hsp1 hF hLF h1 h2
  have hx1 := hkm3.x1val
  rw [hx1] at hv2 hval
  -- reads of `z` outside the write: through the call and the stores
  have hkz : ∀ x m, zp ≤ x → x + m ≤ zp + 8 * zc → (x + m ≤ zp + 16 * kn2 n ∨ zp + 16 * kn2 n + 8 * (2 * lx1) ≤ x) →
      S.mem.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 h3 => (hk x m (by omega)).trans (hzt x m (Or.inl ⟨h1, h2⟩) h3)
  have hkf : ∀ x m, s.sp.toNat - 256 ≤ x → x + m ≤ s.sp.toNat + 48 → (x + m ≤ s.sp.toNat - 136 ∨ s.sp.toNat - 112 ≤ x) →
      S.mem.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 h3 => (hk x m h3).trans (hfrm x m h1 h2)
  have hkt : ∀ x m, t ≤ x → x + m ≤ t + 8 * kT n → S.mem.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => (hk x m (by omega)).trans (hzt x m (Or.inr ⟨h1, h2⟩) (by omega))
  have hzhi : natVal S.mem (zp + 16 * kn2 n) (2 * n - 2 * kn2 n) = kX1 s xp n * kX1 s xp n := by
    have e := natVal_add S.mem (zp + 16 * kn2 n) (2 * lx1) (2 * n - 2 * kn2 n - 2 * lx1)
    rw [show 2 * lx1 + (2 * n - 2 * kn2 n - 2 * lx1) = 2 * n - 2 * kn2 n by omega] at e
    have hz0 : natVal S.mem (zp + 16 * kn2 n + 8 * (2 * lx1)) (2 * n - 2 * kn2 n - 2 * lx1) = 0 := by
      rw [← natVal_zero_part hB.zhi (i := 2 * lx1) (k := 2 * n - 2 * kn2 n - 2 * lx1) (by omega)]
      unfold natVal; exact hkz _ _ (by omega) (by omega) (Or.inr (by omega))
    rw [e, hz0, Nat.mul_zero, Nat.add_zero, ← hv2]
    unfold natVal; exact hk _ _ (by omega)
  have hzlo : natVal S.mem zp (2 * kn2 n) = kX0 s xp n * kX0 s xp n := by
    rw [← hB.zlo]; unfold natVal; exact hkz _ _ (Nat.le_refl _) (by omega) (Or.inl (by omega))
  have hkS := hkmQ.store (ws := [(s.sp.toNat - 136, s.sp.toNat - 112)])
    (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
                    exact ⟨by simp only; omega, Or.inr ⟨by simp only; omega, by simp only; omega⟩⟩) hfr hreg
  obtain ⟨n2b, -, -, -⟩ := hB.z2h
  refine hK S Lk bk l1 l0 l2 ⟨⟨hpc, hsp, h28, h29, h18⟩, hkS,
    hB.z1h.keep fun x m h1 h2 => hkf x m (by omega) (by omega) (Or.inl (by omega)), hB.hl1, ?_, ?_,
    hB.z0h.keep fun x m h1 h2 => hkf x m (by omega) (by omega) (Or.inr (by omega)), hB.hl0, ?_, ?_,
    ⟨(hkf _ _ (by omega) (by omega) (Or.inl (by omega))).trans n2b,
      by rw [show s.sp.toNat - 144 + 8 = s.sp.toNat - 136 by omega]; exact q0,
      by rw [show s.sp.toNat - 144 + 16 = s.sp.toNat - 128 by omega]; exact q1,
      by rw [show s.sp.toNat - 144 + 24 = s.sp.toNat - 120 by omega]; exact q2⟩,
    by omega, ?_, ?_, hzlo, hzhi⟩
  · rw [← hB.z1v]; unfold natVal; exact hkt _ _ (Nat.le_refl _) (by omega)
  · rcases hB.z1n with h0 | h0
    · exact Or.inl h0
    · right; rwa [hkt _ _ (by omega) (by omega)]
  · rw [← hB.z0v]; unfold natVal; exact hkz _ _ (Nat.le_refl _) (by omega) (Or.inl (by omega))
  · rcases hB.z0n with h0 | h0
    · exact Or.inl h0
    · right; rwa [hkz _ _ (by omega) (by omega) (Or.inl (by omega))]
  · rw [← hval]; unfold natVal; exact hk _ _ (by omega)
  · rcases hnn with h0 | h0
    · exact Or.inl h0
    · right; rwa [hk _ _ (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- the stores of `z2`'s new header (`0x1bc4e8 → 0x1bc4f4`), then `kS3fin` -/
theorem kS3st (impl : List Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk3 : List (Nat × Nat)} {bk3 l1 l0 : Nat} {S3 : State}
    (hB : KB4 R b L W st zp zc xp n xc s lx0 lx1 t S3 Lk3 bk3 l1 l0) {Lk : List (Nat × Nat)} {bk l2 : Nat}
    {S1 : State} (hsp1 : S1.sp.toNat = s.sp.toNat - 320) (Q : State)
    (hkmQ : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc5 (stLen s.mem st) n) Q.mem)
    (hF : MemFrame S3.mem Q.mem (R.rt ++ winA S1 (W - 320) 64 ++ [(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++
      stkWs S3.mem st))
    (hLF : LiveFrame S3.mem Q.mem Lk3 ([(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++ stkWs S3.mem st))
    (hv2 : natVal Q.mem (kq2 zp n) (2 * lx1) = natVal S3.mem (xp + 8 * kn2 n) lx1 * natVal S3.mem (xp + 8 * kn2 n) lx1)
    (hval : natVal Q.mem (kq2 zp n) l2 = natVal S3.mem (xp + 8 * kn2 n) lx1 * natVal S3.mem (xp + 8 * kn2 n) lx1)
    (hnn : NatNorm Q.mem (kq2 zp n) l2) (hl2 : l2 ≤ 2 * lx1)
    (hpc : Q.pc = BitVec.ofNat 64 0x1bc4e8) (hsp : Q.sp = s.sp - 320#64)
    (h28 : Q.regs 28 = s.regs 28) (h29 : Q.regs 29 = s.sp - 328#64) (h18 : Q.regs 18 = s.regs 18)
    (r0 : Q.regs 0 = BitVec.ofNat 64 (kq2 zp n)) (r1 : Q.regs 1 = BitVec.ofNat 64 l2)
    (r2 : Q.regs 2 = BitVec.ofNat 64 (zc - 2 * kn2 n))
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 l2 : Nat),
      KB5 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 l2 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s Q := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkmQ.lay
  have hw0 : s.mem.accessible (s.sp.toNat - W) (W + 48) true = true := hkmQ.pre.1.2.1.2.2.2
  have hsacc : Q.mem.accessible (s.sp.toNat - 328) 376 true = true := by
    rw [hkmQ.fr.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := hkmQ.zops.2.2.2.2.2.2.2.2.2
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  have hl2' : l2 < 2 ^ 64 := by have := hkmQ.l1; omega
  have hq2 : kq2 zp n < 2 ^ 64 := by simp only [kq2]; omega
  unfold KGoal
  janus_run until [0x1bc4f4]
  refine kS3fin impl R hB hkmQ hsp1 hF hLF hv2 hval hnn hl2 _ rfl rfl ?_ ?_ ?_ ?fr ?reg ?q0 ?q1 ?q2 hK
  case fr => janus_frame
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KB4 → KB5`**: the loads and the inner `nat.sqr(z2 ← x1)` (`ks_sqcallR`, `z[2n2:]` reused), then `kS3st` -/
theorem kS3 (impl : List Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} (ih : ∀ a, IH impl R (2 * n) (false, a))
    {Lk : List (Nat × Nat)} {bk l1 l0 : Nat} (S : State)
    (hB : KB4 R b L W st zp zc xp n xc s lx0 lx1 t S Lk bk l1 l0)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 l2 : Nat),
      KB5 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 l2 → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  obtain ⟨-, z2b, z2c, z2d⟩ := hB.z2h
  obtain ⟨-, x1b, x1c, x1d⟩ := hkm.x1h
  have q136 : S.mem.readLE (s.sp.toNat - 136) 8 = kq2 zp n := by rw [show s.sp.toNat - 136 = s.sp.toNat - 144 + 8 by omega]; exact z2b
  have q128 : S.mem.readLE (s.sp.toNat - 128) 8 = 2 * n - 2 * kn2 n := by rw [show s.sp.toNat - 128 = s.sp.toNat - 144 + 16 by omega]; exact z2c
  have q120 : S.mem.readLE (s.sp.toNat - 120) 8 = zc - 2 * kn2 n := by rw [show s.sp.toNat - 120 = s.sp.toNat - 144 + 24 by omega]; exact z2d
  have q72 : S.mem.readLE (s.sp.toNat - 72) 8 = xp + 8 * kn2 n := by rw [show s.sp.toNat - 72 = s.sp.toNat - 80 + 8 by omega]; exact x1b
  have q64 : S.mem.readLE (s.sp.toNat - 64) 8 = lx1 := by rw [show s.sp.toNat - 64 = s.sp.toNat - 80 + 16 by omega]; exact x1c
  have q56 : S.mem.readLE (s.sp.toNat - 56) 8 = xc - kn2 n := by rw [show s.sp.toNat - 56 = s.sp.toNat - 80 + 24 by omega]; exact x1d
  have q328 : S.mem.readLE (s.sp.toNat + 8) 8 = st := hkm.s1
  clear z2b z2c z2d x1b x1c x1d
  have hst : st + 24 ≤ 2 ^ 48 := hkm.sok.2.2.2.1
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  obtain ⟨-, hzlive, hzw, hzg, hzs, hne, -, hzal, hzh, hz48⟩ := hkm.zops
  have hl1 := hkm.l1
  have hxacc0 : s.mem.accessible xp (8 * n) false = true := hkm.pre.2.2.2.2.2.2.2.2.2.1
  have hxh0 : Held R L xp (8 * xc) := hkm.pre.2.2.2.2.2.2.2.2.2.2.1
  have hx48 : xp + 8 * xc ≤ 2 ^ 48 := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.1
  have hxw0 : Outside xp (8 * n) (win s W 48) := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzx0 : Apart zp (8 * zc) xp (8 * n) := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxs0 : StkSep S.mem st xp (8 * n) :=
    hkm.sepOf (hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hxh0.sub (by omega) (by omega))
  have hxacc : S.mem.accessible (xp + 8 * kn2 n) (8 * lx1) false = true := by
    rw [hkm.fr.accessible]; exact Memory.accessible_sub _ hxacc0 (Or.inl rfl) (by omega) (by omega)
  obtain ⟨-, -, hzacc, -⟩ := hzlive (by omega)
  have hsc : kc4 (stLen s.mem st) n + kcS (stLen s.mem st) n ≤ ksqrC (stLen s.mem st) n := by
    have := kc7_le (ℓ := stLen s.mem st) h80; unfold kc7 kc6 kc5 at this; omega
  have hw0 : s.mem.accessible (s.sp.toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2.2
  have hsacc : S.mem.accessible (s.sp.toNat - 328) 376 false = true := by
    rw [hkm.fr.accessible]; exact Memory.accessible_sub _ hw0 (Or.inl rfl) (by omega) (by omega)
  clear hw0
  unfold KGoal
  janus_run [q136, q128, q120, q72, q64, q56, q328] until [0x1bb420]
  refine ks_sqcallR impl R hkm ih _ ?pcS ?sp ?g ?hm ?l4 ?l48 (zp' := kq2 zp n) (zl' := 2 * n - 2 * kn2 n)
    (zc' := zc - 2 * kn2 n) (xp' := xp + 8 * kn2 n) (xl' := lx1) (xc' := xc - kn2 n) (by simp only [kq2]; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 (by omega)
    (by omega) (by omega) hxacc (fun _ => ⟨(hkm.ext.held hxh0).sub (by omega) (by omega), by omega⟩)
    (fun _ => hxw0.of_sub (by omega) (by omega)) (by omega)
    (fun _ => ⟨by simp only [kq2]; omega, hzh.sub (by simp only [kq2]; omega) (by simp only [kq2]; omega),
      Memory.accessible_sub _ hzacc (Or.inr rfl) (by simp only [kq2]; omega) (by simp only [kq2]; omega),
      by simp only [kq2]; omega⟩)
    (hzw.of_sub (by simp only [kq2]; omega) (by simp only [kq2]; omega))
    (fun _ => ⟨by simp only [guard] at hzg ⊢; unfold Apart at hzg ⊢; simp only [kq2]; omega,
      hzs.shift (by simp only [kq2]; omega) (by simp only [kq2]; omega)⟩)
    (fun _ _ => by unfold Apart at hzx0 ⊢; simp only [kq2]; omega)
    (fun _ => hxs0.shift (by omega) (by omega)) (by omega) (by simp only [kq2]; omega)
    (Or.inl ⟨by simp only [kq2]; omega, by simp only [kq2]; omega⟩) hsc ?cont
  case cont =>
    intro s2 Lk' bk' l' hr hreg hk hkm' e0 e1 e2 hval hnn hl2 hv2 hF hLF
    have e320 : (s.sp - 320#64).toNat = s.sp.toNat - 320 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    refine kS3st impl R hB e320 s2 hkm' hF hLF hv2 hval hnn hl2 ?pc2 ?sp2 ?g2 ?f2 ?x2 e0 e1 e2 hK
    case pc2 => rw [hr]; rfl
    case sp2 => rw [hk.1]
    case g2 => rw [hk.2.1]; janus_simp
    case f2 => rw [hk.2.2.1]; janus_simp
    case x2 => rw [hk.2.2.2]; janus_simp
  case pcS => rfl
  case hm => rfl
  all_goals janus_simp

end FvModexp.Arm64.NatSqr
