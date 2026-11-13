import FvModexp.Proofs.Amd64.NatQ.KSqrB

/-!
# [amd64 port (divmc s38) of the Q-form Arm64/NatQ/KSqrS3.lean — TIGHT COSTS] `karatsubaSqr` (arm64): `z2.abs = z2.abs.sqr(stk, x1.abs)` (natmul.go:301), `0x5f269e` → `0x5f26f3`

From `KB4`: the call (`ks_sqcallR`; `z2 = z[2·n2:]` reused, exactly `z[2n2:2n2 + 2·len x1]` written, holding `x1²`),
then the stores of the result into `z2`'s header.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

theorem StkSep.shift {m : Memory} {st p k p' k' : Nat} (h : StkSep m st p k) (h1 : p ≤ p') (h2 : p' + k' ≤ p + k) :
    StkSep m st p' k' := by
  obtain ⟨a, b, c⟩ := h; unfold Apart at a b c
  exact ⟨by unfold Apart; omega, by unfold Apart; omega, by unfold Apart; omega⟩

/-- `natVal` of `x[n2:][:len x1]` at a `KM` memory is `X1` -/
theorem KM.x1val {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    natVal M (xp + 8 * kn2 n) lx1 = kX1 s xp n := by
  have hl := h.l1; simp only [kn2] at hl
  show natVal M (xp + 8 * kn2 n) lx1 = natVal s.mem (xp + 8 * kn2 n) (n - kn2 n)
  rw [← h.v1]; unfold natVal; exact h.xrd (by omega) (by simp only [kn2]; omega)

/-- the written part of `z2`: `[zp + 16·n2, zp + 16·n2 + 16·lx1)` -/
@[reducible] def kq2 (zp n : Nat) : Nat := zp + 16 * kn2 n

/-- **`KB5`** at the state after the header stores (`0x5f26f3`), from `KB4` (memory `S3.mem`), the inner square's
facts (memory `Q`) and the frame of the stores -/
theorem kS3fin (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk3 : List (Nat × Nat)} {bk3 l1 l0 : Nat} {S3 : State}
    (hB : KB4 R b H L W st zp zc xp n xc s lx0 lx1 t S3 Lk3 bk3 l1 l0) {Lk : List (Nat × Nat)} {bk l2 : Nat}
    {Q : Memory} (hkmQ : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc5 n) Q)
    (hF : MemFrame S3.mem Q (R.rt ++ [((s.regs 4).toNat - 320 - (W - 320), (s.regs 4).toNat - 320 + 64)] ++ [(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++
      stkWs S3.mem st))
    (hLF : LiveFrame S3.mem Q Lk3 ([(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++ stkWs S3.mem st))
    (hv2 : natVal Q (kq2 zp n) (2 * lx1) = natVal S3.mem (xp + 8 * kn2 n) lx1 * natVal S3.mem (xp + 8 * kn2 n) lx1)
    (hval : natVal Q (kq2 zp n) l2 = natVal S3.mem (xp + 8 * kn2 n) lx1 * natVal S3.mem (xp + 8 * kn2 n) lx1)
    (hnn : NatNorm Q (kq2 zp n) l2) (hl2 : l2 ≤ 2 * lx1)
    (S : State) (hA : KAt s S 0x5f26f3)
    (hfr : MemFrame Q S.mem [((s.regs 4).toNat - 136, (s.regs 4).toNat - 112)]) (hreg : S.mem.regions = Q.regions)
    (q0 : S.mem.readLE ((s.regs 4).toNat - 136) 8 = kq2 zp n) (q1 : S.mem.readLE ((s.regs 4).toNat - 128) 8 = l2)
    (q2 : S.mem.readLE ((s.regs 4).toNat - 120) 8 = zc - 2 * kn2 n)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 l2 : Nat),
      KB5 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 l2 → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s S := by
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
  have hk : ∀ x m, (x + m ≤ (s.regs 4).toNat - 136 ∨ (s.regs 4).toNat - 112 ≤ x) → S.mem.readLE x m = Q.readLE x m :=
    fun x m h => hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hfrm : ∀ x m, (s.regs 4).toNat - 256 ≤ x → x + m ≤ (s.regs 4).toNat + 48 → Q.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => hkm3.sqRd hF (by omega) h1 h2
  have hzt : ∀ x m, ((zp ≤ x ∧ x + m ≤ zp + 8 * zc) ∨ (t ≤ x ∧ x + m ≤ t + 8 * kT n)) →
      (x + m ≤ zp + 16 * kn2 n ∨ zp + 16 * kn2 n + 8 * (2 * lx1) ≤ x) → Q.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 => hkm3.sqKeep hF hLF h1 h2
  have hx1 := hkm3.x1val
  rw [hx1] at hv2 hval
  -- reads of `z` outside the write: through the call and the stores
  have hkz : ∀ x m, zp ≤ x → x + m ≤ zp + 8 * zc → (x + m ≤ zp + 16 * kn2 n ∨ zp + 16 * kn2 n + 8 * (2 * lx1) ≤ x) →
      S.mem.readLE x m = S3.mem.readLE x m :=
    fun x m h1 h2 h3 => (hk x m (by omega)).trans (hzt x m (Or.inl ⟨h1, h2⟩) h3)
  have hkf : ∀ x m, (s.regs 4).toNat - 256 ≤ x → x + m ≤ (s.regs 4).toNat + 48 → (x + m ≤ (s.regs 4).toNat - 136 ∨ (s.regs 4).toNat - 112 ≤ x) →
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
  have hkS := hkmQ.store (ws := [((s.regs 4).toNat - 136, (s.regs 4).toNat - 112)])
    (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
                    exact ⟨by simp only; omega, Or.inr ⟨by simp only; omega, by simp only; omega⟩⟩) hfr hreg
  obtain ⟨n2b, -, -, -⟩ := hB.z2h
  refine hK S Lk bk l1 l0 l2 ⟨hA, hkS,
    hB.z1h.keep fun x m h1 h2 => hkf x m (by omega) (by omega) (Or.inl (by omega)), hB.hl1, ?_, ?_,
    hB.z0h.keep fun x m h1 h2 => hkf x m (by omega) (by omega) (Or.inr (by omega)), hB.hl0, ?_, ?_,
    ⟨(hkf _ _ (by omega) (by omega) (Or.inl (by omega))).trans n2b,
      by rw [show (s.regs 4).toNat - 144 + 8 = (s.regs 4).toNat - 136 by omega]; exact q0,
      by rw [show (s.regs 4).toNat - 144 + 16 = (s.regs 4).toNat - 128 by omega]; exact q1,
      by rw [show (s.regs 4).toNat - 144 + 24 = (s.regs 4).toNat - 120 by omega]; exact q2⟩,
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
/-- the stores of `z2`'s new header (`0x5f26db → 0x5f26f3`), then `kS3fin` -/
theorem kS3st (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} {Lk3 : List (Nat × Nat)} {bk3 l1 l0 : Nat} {S3 : State}
    (hB : KB4 R b H L W st zp zc xp n xc s lx0 lx1 t S3 Lk3 bk3 l1 l0) {Lk : List (Nat × Nat)} {bk l2 : Nat}
    (Q : State)
    (hkmQ : KM R b H L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc5 n) Q.mem)
    (hF : MemFrame S3.mem Q.mem (R.rt ++ [((s.regs 4).toNat - 320 - (W - 320), (s.regs 4).toNat - 320 + 64)] ++ [(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++
      stkWs S3.mem st))
    (hLF : LiveFrame S3.mem Q.mem Lk3 ([(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++ stkWs S3.mem st))
    (hv2 : natVal Q.mem (kq2 zp n) (2 * lx1) = natVal S3.mem (xp + 8 * kn2 n) lx1 * natVal S3.mem (xp + 8 * kn2 n) lx1)
    (hval : natVal Q.mem (kq2 zp n) l2 = natVal S3.mem (xp + 8 * kn2 n) lx1 * natVal S3.mem (xp + 8 * kn2 n) lx1)
    (hnn : NatNorm Q.mem (kq2 zp n) l2) (hl2 : l2 ≤ 2 * lx1) (hA : KAt s Q 0x5f26db)
    (r0 : Q.regs 0 = BitVec.ofNat 64 (kq2 zp n)) (r1 : Q.regs 3 = BitVec.ofNat 64 l2)
    (r2 : Q.regs 1 = BitVec.ofNat 64 (zc - 2 * kn2 n))
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 l2 : Nat),
      KB5 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 l2 → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s Q := by
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hA
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkmQ.lay
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := hkmQ.pre.1.2.1.2.2
  have hsacc : Q.mem.accessible ((s.regs 4).toNat - 320) 368 true = true := by
    rw [hkmQ.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hz48 : zp + 8 * zc ≤ 2 ^ 48 := hkmQ.zops.2.2.2.2.2.2.2.2.2
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  have hl2' : l2 < 2 ^ 64 := by have := hkmQ.l1; omega
  have hq2 : kq2 zp n < 2 ^ 64 := by simp only [kq2]; omega
  have hsp' : (Q.regs 4).toNat = (s.regs 4).toNat - 312 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold KGoal
  janus64_run [hsp'] until [0x5f26f3]
  refine kS3fin impl R hB hkmQ hF hLF hv2 hval hnn hl2 _ ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?fr ?reg ?q0 ?q1 ?q2 hK
  case fr => janus_frame
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KB4 → KB5`**: the loads and the inner `nat.sqr(z2 ← x1)` (`0x5f26d6`, return `0x5f26db` pushed;
`ks_sqcallR`, `z[2n2:]` reused), then `kS3st` -/
theorem kS3 (impl : List Amd64.Segment) (R : RtInv) {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat}
    {s : State} {lx0 lx1 t : Nat} (ih : ∀ a, IH impl R H (2 * n) (false, a)) (hx150 : s.xmm 15 = 0#128)
    (hdf0 : s.df = false)
    {Lk : List (Nat × Nat)} {bk l1 l0 : Nat} (S : State)
    (hB : KB4 R b H L W st zp zc xp n xc s lx0 lx1 t S Lk bk l1 l0)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' l1 l0 l2 : Nat),
      KB5 R b H L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' l1 l0 l2 → KGoal impl R H b L W st zp xp n s S') :
    KGoal impl R H b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h14, h5, hfs, hdf, hx15⟩ := hB.pos
  obtain ⟨-, z2b, z2c, z2d⟩ := hB.z2h
  obtain ⟨-, x1b, x1c, x1d⟩ := hkm.x1h
  have q136 : S.mem.readLE ((s.regs 4).toNat - 136) 8 = kq2 zp n := by
    rw [show (s.regs 4).toNat - 136 = (s.regs 4).toNat - 144 + 8 by omega]; exact z2b
  have q128 : S.mem.readLE ((s.regs 4).toNat - 128) 8 = 2 * n - 2 * kn2 n := by
    rw [show (s.regs 4).toNat - 128 = (s.regs 4).toNat - 144 + 16 by omega]; exact z2c
  have q120 : S.mem.readLE ((s.regs 4).toNat - 120) 8 = zc - 2 * kn2 n := by
    rw [show (s.regs 4).toNat - 120 = (s.regs 4).toNat - 144 + 24 by omega]; exact z2d
  have q72 : S.mem.readLE ((s.regs 4).toNat - 72) 8 = xp + 8 * kn2 n := by
    rw [show (s.regs 4).toNat - 72 = (s.regs 4).toNat - 80 + 8 by omega]; exact x1b
  have q64 : S.mem.readLE ((s.regs 4).toNat - 64) 8 = lx1 := by
    rw [show (s.regs 4).toNat - 64 = (s.regs 4).toNat - 80 + 16 by omega]; exact x1c
  have q56 : S.mem.readLE ((s.regs 4).toNat - 56) 8 = xc - kn2 n := by
    rw [show (s.regs 4).toNat - 56 = (s.regs 4).toNat - 80 + 24 by omega]; exact x1d
  have q8 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = st := hkm.s1
  clear z2b z2c z2d x1b x1c x1d
  have hst : st + 24 ≤ 2 ^ 48 := hkm.sok.2.2.2.1
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  obtain ⟨-, hzlive, hzw, hzg, hzs, hne, -, hzal, hzh, hz48⟩ := hkm.zops
  obtain ⟨-, hzt⟩ := hkm.ttls
  have hl1 := hkm.l1
  have hxacc0 : s.mem.accessible xp (8 * n) false = true := hkm.pre.2.2.2.2.2.2.2.2.2.1
  have hxh0 : Held R L xp (8 * xc) := hkm.pre.2.2.2.2.2.2.2.2.2.2.1
  have hx48 : xp + 8 * xc ≤ 2 ^ 48 := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.1
  have hxw0 : Outside xp (8 * n) (win s W 48) := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzx0 : Apart zp (8 * zc) xp (8 * n) := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hxs0 : StkSep S.mem st xp (8 * n) :=
    hkm.sepOf (hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (hxh0.sub (by omega) (by omega))
  have hxacc : S.mem.accessible (xp + 8 * kn2 n) (8 * lx1) false = true := by
    rw [hkm.fr.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hxacc0 (Or.inl rfl) (by omega) (by omega)
  obtain ⟨-, -, hzacc, -⟩ := hzlive (by omega)
  have hsc : kc4 n + kcS n ≤ ksqrCQ n := by
    have := kc7_le h80; unfold kc7 kc6 kc5 at this; omega
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 320) 368 true = true := by
    rw [hkm.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  clear hw0
  have hsp' : (S.regs 4).toNat = (s.regs 4).toNat - 312 := by rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  -- the facts at the call memory (return address `0x5f26db` pushed at `SP - 320`)
  have hkmP := hkm.push 0x5f26db
  have hxw' : xp + 8 * n ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 48 ≤ xp := by
    simp only [win, outside_cons, outside_nil, and_true] at hxw0; omega
  have hxaccP : (S.mem.writeLE ((s.regs 4).toNat - 320) 8 0x5f26db).accessible (xp + 8 * kn2 n) (8 * lx1) false = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]; exact hxacc
  have hzaccP : (S.mem.writeLE ((s.regs 4).toNat - 320) 8 0x5f26db).accessible zp (8 * zc) true = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]; exact hzacc
  have hzsP := hkm.pushSep 0x5f26db hzs
  have hxsP := hkm.pushSep 0x5f26db hxs0
  have hxvP : natVal (S.mem.writeLE ((s.regs 4).toNat - 320) 8 0x5f26db) (xp + 8 * kn2 n) lx1 =
      natVal S.mem (xp + 8 * kn2 n) lx1 := by
    unfold natVal; exact pushRd (by omega)
  have hzw' : zp + 8 * zc ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 48 ≤ zp := by
    simp only [win, outside_cons, outside_nil, and_true] at hzw; omega
  obtain ⟨e1, e2, e3⟩ := hkm.pushHdr 0x5f26db
  have hLs := hkm.lsep
  unfold KGoal
  janus64_run [q136, q128, q120, q72, q64, q56, q8, hsp'] until [0x5f0fe0]
  refine ks_sqcallR impl R hkmP ih _ ?pcS ?sp ?g ?hm ?fs (ra := 0x5f26db) ?rv (by decide) ?x15 ?df ?h5 hx150 hdf0
    (zp' := kq2 zp n) (zl' := 2 * n - 2 * kn2 n)
    (zc' := zc - 2 * kn2 n) (xp' := xp + 8 * kn2 n) (xl' := lx1) (xc' := xc - kn2 n) (by simp only [kq2]; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 (by omega)
    (by omega) (by omega) hxaccP (fun _ => ⟨(hkm.ext.held hxh0).sub (by omega) (by omega), by omega⟩)
    (fun _ => hxw0.of_sub (by omega) (by omega)) (by omega)
    (fun _ => ⟨by simp only [kq2]; omega, hzh.sub (by simp only [kq2]; omega) (by simp only [kq2]; omega),
      Janus.Arm64.Memory.accessible_sub _ hzaccP (Or.inr rfl) (by simp only [kq2]; omega) (by simp only [kq2]; omega),
      by simp only [kq2]; omega⟩)
    (hzw.of_sub (by simp only [kq2]; omega) (by simp only [kq2]; omega))
    (fun _ => ⟨by simp only [guard] at hzg ⊢; unfold Apart at hzg ⊢; simp only [kq2]; omega,
      by simp only [tls] at hzt ⊢; unfold Apart at hzt ⊢; simp only [kq2]; omega,
      hzsP.shift (by simp only [kq2]; omega) (by simp only [kq2]; omega)⟩)
    (fun _ _ => by unfold Apart at hzx0 ⊢; simp only [kq2]; omega)
    (fun _ => hxsP.shift (by omega) (by omega)) (by omega) (by simp only [kq2]; omega)
    (Or.inl ⟨by simp only [kq2]; omega, by simp only [kq2]; omega⟩) hsc ?cont
  case cont =>
    intro s2 Lk' bk' l' hA2 hreg hkm' e0 e1' e2' hval hnn hl2 hv2 hF hLF
    rw [hxvP] at hval hv2
    have hF' : MemFrame S.mem s2.mem (R.rt ++ [((s.regs 4).toNat - 320 - (W - 320), (s.regs 4).toNat - 320 + 64)] ++ [(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++ stkWs S.mem st) := by
      have := pushFrame (rt := R.rt) (w := [((s.regs 4).toNat - 320 - (W - 320), (s.regs 4).toNat - 320 + 64)]) (ws := [(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++ stkWs S.mem st)
        (q := (s.regs 4).toNat - 320) (v := 0x5f26db) (M := S.mem) (M' := s2.mem)
        (fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega)
      simp only [stkWs, BasicSqr.freeP, BasicSqr.freeN, e1, e2, e3, List.append_assoc] at hF this ⊢
      exact this hF
    have hLF' : LiveFrame S.mem s2.mem Lk ([(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++ stkWs S.mem st) := by
      have := pushLF (M := S.mem) (M' := s2.mem) (q := (s.regs 4).toNat - 320) (v := 0x5f26db) (Lk := Lk)
        (ws := [(kq2 zp n, kq2 zp n + 8 * (2 * lx1))] ++ stkWs S.mem st)
        (fun r hr => by have := hLs r hr; simp only [outside_cons, outside_nil, and_true]; omega)
      simp only [stkWs, BasicSqr.freeP, BasicSqr.freeN, e1, e2, e3] at hLF this ⊢
      exact this hLF
    exact kS3st impl R hB s2 hkm' hF' hLF' hv2 hval hnn hl2 hA2 e0 e1' e2' hK
  case pcS => rfl
  case hm => rfl
  all_goals (try janus64_simp)
  all_goals first | exact hfs | exact hdf | exact hx15 | omega

end FvModexp.Amd64.Q.NatSqr
