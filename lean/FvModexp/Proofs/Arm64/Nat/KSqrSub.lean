import FvModexp.Proofs.Arm64.Nat.KSqrB

/-!
# `karatsubaSqr` (arm64): `z1 := …; tx := &Int{abs: z[0:n2]}; tx.Sub(x0, x1)` (natmul.go:293-296), `KB1 → KB2`

`kSubCall`: at the `(*Int).Sub` entry (headers `z1 = (0, t, kT, kT)`, `tx = (0, zp, n2, zc)` stored), the call
(`ks_intcall`) and `KB2` from its postcondition (pure). `kSub`: the stores from `KB1` (`0x1bc428`) to the call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

theorem sp_sub (x : BitVec 64) {k : Nat} (h : k ≤ x.toNat) :
    x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat - k) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem natAbs_sub_lt {a b B : Nat} (ha : a < B) (hb : b < B) : ((a : Int) - (b : Int)).natAbs < B := by
  omega

set_option maxRecDepth 20000 in
theorem kSubCall (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} {S : State} (hB : KB1 R b L W st zp zc xp n xc s lx0 lx1 t S Lk bk)
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 0x1b0ab0) (hsp : S1.sp = s.sp - 320#64)
    (h28 : S1.regs 28 = s.regs 28) (h29 : S1.regs 29 = s.sp - 328#64) (h18 : S1.regs 18 = s.regs 18)
    (hra : S1.regs 30 = BitVec.ofNat 64 0x1bc470)
    (r0 : S1.regs 0 = BitVec.ofNat 64 (s.sp.toNat - 232)) (r1 : S1.regs 1 = BitVec.ofNat 64 (s.sp.toNat - 48))
    (r2 : S1.regs 2 = BitVec.ofNat 64 (s.sp.toNat - 80))
    (hfr : MemFrame S.mem S1.mem [(s.sp.toNat - 232, s.sp.toNat - 168)]) (hreg : S1.mem.regions = S.mem.regions)
    (htx : IntAt S1.mem (s.sp.toNat - 232) 0 zp (kn2 n) zc)
    (hz1 : IntAt S1.mem (s.sp.toNat - 200) 0 t (kT n) (kT n))
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' tng ltx : Nat),
      KB2 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' tng ltx → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S1 := by
  have hkm0 := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkm0.lay
  have hkm := hkm0.store (ws := [(s.sp.toNat - 232, s.sp.toNat - 168)])
    (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
                    exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩) hfr hreg
  have hsp' : S1.sp.toNat = s.sp.toNat - 320 := by
    rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hox0, hv0, hp0, hl0e⟩ := hkm.x0op
  obtain ⟨hox1, hv1, hp1, hl1e⟩ := hkm.x1op
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, -, -, -⟩ := hkm.zops
  obtain ⟨-, hxc40', -, -, -, -, hzx0⟩ := hkm.x0ops
  obtain ⟨t1, t2, t3, t4⟩ := htx
  have hl0 := hkm.l0; have hl1 := hkm.l1
  simp only [kn2] at hl0 hl1
  have hzx1 : Apart zp (8 * zc) (xp + 8 * kn2 n) (8 * lx1) := by
    have hzx : Apart zp (8 * zc) xp (8 * n) := hkm.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    unfold Apart at hzx ⊢; simp only [kn2]; omega
  have hcost : IntAS.asCost lx0 lx1 ≤ bk := by
    refine hkm.cost (spent := kc1 (stLen s.mem st) n) ?_
    have h7 := kc7_le (ℓ := stLen s.mem st) h80
    have ha := asCost_le_asB (a := lx0) (b := lx1) (k := kT n) (by simp only [kT, kn2]; omega)
      (by simp only [kT, kn2]; omega)
    unfold kc7 kc6 kc5 kc4 kc3 kc2 at h7; omega
  refine ks_intcall impl hap R hmk hmv hwb hkm true S1 hpc hsp' h28 rfl (i := 112) (by decide) hra r0 r1 r2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by unfold Apart; omega))
    (by unfold Apart; omega) hox0 hox1 ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [IntAS.hC, t4]; exact hzc40
  · simp only [IntAS.hP, IntAS.hC, t2, t4]; exact hzlive
  · simp only [IntAS.hP, IntAS.hC, t2, t4]; exact hzw
  · intro _
    simp only [IntAS.hP, IntAS.hC, IntAS.hL, t2, t4, hp0, hl0e, hp1, hl1e]
    exact ⟨hzg, Or.inr hzx0, Or.inr hzx1⟩
  · simp only [hl0e, hl1e]; exact hcost
  intro s2 hpc2 hreg2 hk hq
  obtain ⟨-, hval, hng, -, hnn, -, hlmax, -, L', b', hext, hbud, hinv, -, -, hreuse, hF, hLF⟩ := hq
  simp only [IntAS.hP, IntAS.hC, IntAS.hL, t2, t4, hl0e, hl1e] at hF hLF hreuse hlmax hbud
  have hre := hreuse (by unfold IntAS.asNeed; split <;> omega)
  rw [hv0, hv1] at hval
  simp only [IntAS.resZ, IntAS.intZ, ↓reduceIte, IntAS.hNeg, IntAS.hP, IntAS.hL] at hval
  have hvN := natAbs_of_signed hval
  rw [h28] at hinv
  simp only [IntAS.hP, IntAS.hL] at hnn
  rw [hre.1] at hvN hnn
  have hkm2 := (hkm.intStep (S1 := S1) hsp' (z := s.sp.toNat - 232) (q := zp) (w := min (max lx0 lx1 + 1) zc)
    (Or.inl ⟨by omega, by omega⟩) (Or.inl ⟨Nat.le_refl _, by omega⟩) hF hLF hreg2 hext hbud hinv).weaken
    (spent' := kc2 (stLen s.mem st) n) (by
      have ha := asCost_le_asB (a := lx0) (b := lx1) (k := kT n) (by simp only [kT, kn2]; omega)
        (by simp only [kT, kn2]; omega)
      unfold kc2; omega)
  have hF' := hF
  simp only [winA, hsp'] at hF'
  have hzw' := hzw; simp only [win, outside_cons, outside_nil, and_true] at hzw'
  have hk1 : ∀ x m, s.sp.toNat - 200 ≤ x → x + m ≤ s.sp.toNat + 48 → s2.mem.readLE x m = S1.mem.readLE x m :=
    fun x m h1 h2 => hkm.rdW (k := 4560) (a := 32) (by omega) (by omega) hF' (by omega) h2
      (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hk0 : ∀ x m, s.sp.toNat - 168 ≤ x → x + m ≤ s.sp.toNat + 48 → S1.mem.readLE x m = S.mem.readLE x m :=
    fun x m h1 h2 => hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hX0 := natVal_lt s.mem xp (kn2 n)
  have hX1 := natVal_lt s.mem (xp + 8 * kn2 n) (n - kn2 n)
  have hpw : 2 ^ (64 * (n - kn2 n)) ≤ 2 ^ (64 * kn2 n) := Nat.pow_le_pow_right (by decide) (by simp only [kn2]; omega)
  refine hK s2 L' b' _ _ ⟨⟨by rw [hpc2, hra], by rw [hk.1, hsp], by rw [hk.2.1, h28], by rw [hk.2.2.1, h29],
    by rw [hk.2.2.2, h18]⟩, hkm2, hz1.keep fun x m h1 h2 => hk1 x m (by omega) (by omega),
    (hB.z0h.keep fun x m h1 h2 => hk0 x m (by omega) (by omega)).keep fun x m h1 h2 => hk1 x m (by omega) (by omega),
    (hB.z2h.keep fun x m h1 h2 => hk0 x m (by omega) (by omega)).keep fun x m h1 h2 => hk1 x m (by omega) (by omega),
    ⟨rfl, hre.1, rfl, hre.2⟩, hng, natNorm_le hnn (by rw [hvN]; exact natAbs_sub_lt hX0 (Nat.lt_of_lt_of_le hX1 hpw)), hvN, hnn⟩

end FvModexp.Arm64.NatSqr

namespace FvModexp.Arm64.NatSqr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KB1 → KB2`**: the header stores and the `CALL (*Int).Sub` (`0x1bc428 … 0x1bc46c`), then `kSubCall` -/
theorem kSub (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk : Nat} (S : State) (hB : KB1 R b L W st zp zc xp n xc s lx0 lx1 t S Lk bk)
    (hK : ∀ (S' : State) (Lk' : List (Nat × Nat)) (bk' tng ltx : Nat),
      KB2 R b L W st zp zc xp n xc s lx0 lx1 t S' Lk' bk' tng ltx → KGoal impl R b L W st zp xp n s S') :
    KGoal impl R b L W st zp xp n s S := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, -, -, -⟩ := hkm.lay
  obtain ⟨hpc, hsp, h28, h29, h18⟩ := hB.pos
  have r0 := hB.r0; have r1 := hB.r1; have r2 := hB.r2
  have q352 : S.mem.readLE (s.sp.toNat + 32) 8 = zc := hkm.s4
  have q80 : S.mem.readLE (s.sp.toNat - 240) 8 = n + 1 := hkm.n1s
  have q72 : S.mem.readLE (s.sp.toNat - 248) 8 = kn2 n := hkm.n2s
  have q336 : S.mem.readLE (s.sp.toNat + 16) 8 = zp := hkm.s2
  have hw0 : s.mem.accessible (s.sp.toNat - W) (W + 48) true = true := hkm.pre.1.2.1.2.2.2
  have hsacc : S.mem.accessible (s.sp.toNat - 328) 376 true = true := by
    rw [hkm.fr.accessible]; exact Memory.accessible_mono _ hw0 (by omega) (by omega)
  have hsacc' : S.mem.accessible (s.sp.toNat - 328) 376 false = true :=
    Memory.accessible_sub _ hsacc (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _)
  clear hw0
  have hsh : BitVec.ofNat 64 (n + 1) >>> 1 = BitVec.ofNat 64 (kn2 n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, kn2]; omega
  have hzc2 : kn2 n ≤ zc := by simp only [kn2]; omega
  have hzp48 : zp + 8 * zc ≤ 2 ^ 48 := hkm.zops.2.2.2.2.2.2.2.2.2
  have ht48 : t + 8 * kT n ≤ 2 ^ 48 := hkm.tops.2.2.2.2.2
  unfold KGoal
  janus_run [q352, q80, q72, q336, hsh] until [0x1b0ab0]
  refine kSubCall impl hap R hmk hmv hwb hB _ (by rfl) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?fr ?reg ?_ ?_ hK
  case fr => janus_frame
  all_goals (try simp only [IntAt])
  all_goals janus_simp
  all_goals exact sp_sub _ (by omega)

end FvModexp.Arm64.NatSqr
