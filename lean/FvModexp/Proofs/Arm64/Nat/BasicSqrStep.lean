import FvModexp.Proofs.Arm64.Nat.BasicSqrDefs
import FvModexp.Proofs.Common.DivmcNat

/-!
# `basicSqr` (arm64): one loop iteration on the invariant (pure memory reasoning, no execution)

`inv_step`: from `Inv i M`, the two `z` words written (`S1m`), the `addMulVVWW` call on `t[i:2i]` (`w`, carry `c` at
`SP - 112`) and the store `t[2i] = c`, `Inv (i+1)`.
-/

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.BasicSqr

/-- two limbs -/
theorem natVal_two (m : Memory) (p : Nat) : natVal m p 2 = m.readLE p 8 + 2 ^ 64 * m.readLE (p + 8) 8 := by
  rw [natVal_succ, natVal_succ, natVal_zero]; simp

/-- the facts of `Env`/`Pre` the memory reasoning uses, as plain arithmetic -/
structure Lay (R : RtInv) (L L1 : List (Nat × Nat)) (st zp zl xp xl : Nat) (s : State) (t : Nat) : Prop where
  sp0 : 4432 ≤ s.sp.toNat
  sp1 : s.sp.toNat + 64 ≤ 2 ^ 48
  zl2 : zl = 2 * xl
  x0 : 0 < xl
  z48 : zp + 8 * zl ≤ 2 ^ 48
  zw : zp + 8 * zl ≤ s.sp.toNat - 4432 ∨ s.sp.toNat + 64 ≤ zp
  xw : xp + 8 * xl ≤ s.sp.toNat - 4432 ∨ s.sp.toNat + 64 ≤ xp
  tw : t + 16 * xl ≤ s.sp.toNat - 4432 ∨ s.sp.toNat + 64 ≤ t
  sw : st + 24 ≤ s.sp.toNat - 4432 ∨ s.sp.toNat + 64 ≤ st
  zx : zp + 8 * zl ≤ xp ∨ xp + 8 * xl ≤ zp
  tz : t + 16 * xl ≤ zp ∨ zp + 8 * zl ≤ t
  tx : t + 16 * xl ≤ xp ∨ xp + 8 * xl ≤ t
  ts : t + 16 * xl ≤ st ∨ st + 24 ≤ t
  sz : st + 24 ≤ zp ∨ zp + 8 * zl ≤ st
  t48 : t + 16 * xl ≤ 2 ^ 48
  theld : Held R L1 t (16 * xl)
  lsep : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 4432 ∨ s.sp.toNat + 64 ≤ r.1

theorem Env.lay {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat} (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1) :
    Lay R L L1 st zp zl xp xl s t := by
  have hpre := hE.pre
  have hce := hpre.ce
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce
  have hscr := hE.scr
  have hfr : ∀ p n, Held R L p n → (0 < stCap s.mem st → Apart p n (freeP s.mem st) (freeN s.mem st)) →
      Apart t (8 * (2 * xl)) p n := fun p n h1 h2 => hscr.apart h1 h2
  have htz := hfr zp (8 * zl) (hpre.zlive (by have := hpre.x0; have := hpre.zl2; omega)).2.1
    (fun _ => hpre.free.1)
  have e : 8 * (2 * xl) = 16 * xl := by omega
  have htx := hfr xp (8 * xl) hpre.xh (fun _ => hpre.free.2)
  have hts := hfr st 24 hpre.stok.2.1 (fun _ => hpre.stfree)
  have htw : Outside t (8 * (2 * xl)) (win s 4432 64) := by
    refine hscr.outside ?_ ?_
    · intro r hr; simp only [win, List.mem_singleton] at hr; subst hr
      simp only; exact hout.of_sub (by omega) (by omega)
    · intro r hr hc; simp only [win, List.mem_singleton] at hr; subst hr
      have := (hpre.starr hc).1
      simp only [win, outside_cons, outside_nil, and_true] at this
      have hlc := hpre.stok.2.2.2.2.2.1
      simp only [Apart]; omega
  have hzl := hpre.zlive (by have := hpre.x0; have := hpre.zl2; omega)
  have hzw := hpre.zw; have hxw := hpre.xw; have hsw := hpre.stw; have hzx := hpre.zx; have hsz := hpre.stz
  simp only [win, outside_cons, outside_nil, and_true] at hzw hxw hsw htw
  unfold Apart at htz htx hts hzx hsz
  rw [e] at htz htx hts htw
  have hth := hscr.held; rw [e] at hth
  have ht48 := hscr.b48; rw [e] at ht48
  refine ⟨hb', ha, hpre.zl2, hpre.x0, hzl.2.2.2, hzw, hxw, htw, hsw, hzx, htz, htx, hts, hsz,
    ht48, hth, fun r hr => ?_⟩
  have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem inv_step {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl xc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1) {i : Nat} (hi1 : 1 ≤ i) (hiy : i < xl) {M S1m w : Memory}
    (hI : Inv R L st zp zl zc xp xl xc s t L1 b1 w1 c1 i M)
    (hF : MemFrame M S1m [(zp + 16 * i, zp + 16 * i + 16), (s.sp.toNat - 200, s.sp.toNat - 112),
      (s.sp.toNat - 72, s.sp.toNat - 56)])
    (hz0 : S1m.readLE (zp + 16 * i) 8 = (s.mem.readLE (xp + 8 * i) 8 * s.mem.readLE (xp + 8 * i) 8) % 2 ^ 64)
    (hz1 : S1m.readLE (zp + 16 * i + 8) 8 = s.mem.readLE (xp + 8 * i) 8 * s.mem.readLE (xp + 8 * i) 8 / 2 ^ 64)
    (hFw : MemFrame S1m w [(t + 8 * i, t + 8 * i + 8 * i), (s.sp.toNat - 112, s.sp.toNat - 104)])
    (hval : natVal w (t + 8 * i) i + 2 ^ (64 * i) * w.readLE (s.sp.toNat - 112) 8 =
      natVal S1m (t + 8 * i) i + natVal S1m xp i * s.mem.readLE (xp + 8 * i) 8)
    (hinvw : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 w)) :
    Inv R L st zp zl zc xp xl xc s t L1 b1 w1 c1 (i + 1)
      (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)) := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hzl2 := hl.zl2; have hx0 := hl.x0; have hz48 := hl.z48
  have ht48 := hl.t48
  obtain ⟨hM, hvz, hvt, hzero⟩ := hI
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, mxs, mfr, mlf, minv⟩ := hM
  -- the three changes after `M`: `S1m` (z words, frame), `w` (t[i:2i], carry slot), the store `t[2i]`
  have keep : ∀ a n, (a + n ≤ zp + 16 * i ∨ zp + 16 * i + 16 ≤ a) → (a + n ≤ s.sp.toNat - 200 ∨ s.sp.toNat - 56 ≤ a ∨
      (s.sp.toNat - 104 ≤ a ∧ a + n ≤ s.sp.toNat - 72)) → (a + n ≤ t + 8 * i ∨ t + 16 * i + 8 ≤ a) →
      (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)).readLE a n = M.readLE a n := by
    intro a n h1 h2 h3
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have slot : ∀ a, (s.sp.toNat - 216 ≤ a ∧ a + 8 ≤ s.sp.toNat - 200) ∨ (s.sp.toNat - 104 ≤ a ∧ a + 8 ≤ s.sp.toNat - 72) ∨
      (s.sp.toNat - 56 ≤ a ∧ a + 8 ≤ s.sp.toNat - 8) ∨ (s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 64) →
      (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)).readLE a 8 = M.readLE a 8 :=
    fun a ha => by have := hl.zw; have := hl.tw; exact keep a 8 (by omega) (by omega) (by omega)
  have lst : MemFrame M (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8))
      [(s.sp.toNat - 200, s.sp.toNat - 104), (s.sp.toNat - 72, s.sp.toNat - 56), (zp, zp + 8 * zl), (t, t + 16 * xl)] :=
    ⟨fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h
      exact keep a n (by omega) (by omega) (by omega),
     fun a n v => by rw [Memory.accessible_writeLE, hFw.accessible, hF.accessible]⟩
  have hsth : st + 24 ≤ 2 ^ 48 := hE.pre.stok.2.2.2.1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?vz, ?vt, ?zero⟩
  · rw [slot _ (by omega)]; exact m1
  · rw [slot _ (by omega)]; exact m2
  · rw [slot _ (by omega)]; exact m3
  · rw [slot _ (by omega)]; exact m4
  · rw [slot _ (by omega)]; exact m5
  · rw [slot _ (by omega)]; exact m6
  · rw [slot _ (by omega)]; exact m7
  · rw [slot _ (by omega)]; exact m8
  · rw [slot _ (by omega)]; exact m9
  · rw [slot _ (by omega)]; exact m10
  · rw [slot _ (by omega)]; exact m11
  · rw [slot _ (by omega)]; exact m12
  · rw [slot _ (by omega)]; exact m13
  · rw [slot _ (by omega)]; exact m14
  · rw [slot _ (by omega)]; exact m15
  · rw [slot _ (by omega)]; exact m16
  · have := hl.sz; have := hl.sw; have := hl.ts
    rw [keep _ 8 (by omega) (by omega) (by omega)]; exact m17
  · have := hl.sz; have := hl.sw; have := hl.ts
    rw [keep _ 8 (by omega) (by omega) (by omega)]; exact m18
  · have := hl.sz; have := hl.sw; have := hl.ts
    rw [keep _ 8 (by omega) (by omega) (by omega)]; exact m19
  · intro a n h1 h2; have := hl.zx; have := hl.xw; have := hl.tx
    rw [keep a n (by omega) (by omega) (by omega)]; exact mxs a n h1 h2
  · refine MemFrame.trans mfr lst fun a n h => ⟨h, ?_⟩
    simp only [stkWs, winA, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    omega
  · refine LiveFrame.trans mlf (liveFrame_of_frame (rs := [(s.sp.toNat - 200, s.sp.toNat - 104),
      (s.sp.toNat - 72, s.sp.toNat - 56)]) (lo := s.sp.toNat - 4432) (hi := s.sp.toNat + 64)
      (lst.mono fun a n h => by
        simp only [stkWs, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega) hl.lsep ?_) (fun _ _ h => h)
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega
  · exact inv_store_held hinvw (hl.theld.sub (by omega) (by omega))
  case vz =>
    have := hl.zw; have := hl.tz
    rw [show 2 * (i + 1) = 2 * i + 2 by omega, natVal_add, natVal_two, SqrMath.sqS]
    have r0 : (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)).readLE (zp + 8 * (2 * i)) 8 =
        S1m.readLE (zp + 16 * i) 8 := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), show zp + 8 * (2 * i) = zp + 16 * i by omega,
        hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    have r1 : (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)).readLE (zp + 8 * (2 * i) + 8) 8 =
        S1m.readLE (zp + 16 * i + 8) 8 := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), show zp + 8 * (2 * i) + 8 = zp + 16 * i + 8 by omega,
        hFw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    have rlo : natVal (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)) zp (2 * i) = natVal M zp (2 * i) :=
      keep _ _ (by omega) (by omega) (by omega)
    rw [r0, r1, hz0, hz1, rlo, hvz, Nat.mod_add_div]
    simp only [SqrMath.lim]; rw [Nat.mul_comm (2 ^ _)]
  case vt =>
    have := hl.tw; have := hl.tz; have := hl.tx
    have e1 := natVal_add (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)) t i (i + 2)
    have e2 := natVal_add (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)) (t + 8 * i) i 2
    have e3 := natVal_two (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)) (t + 8 * i + 8 * i)
    rw [show i + (i + 2) = 2 * (i + 1) by omega] at e1
    have rtop : (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)).readLE (t + 16 * i + 8) 8 = 0 := by
      rw [keep (t + 16 * i + 8) 8 (by omega) (by omega) (by omega)]
      exact hzero (t + 16 * i + 8) 8 (by omega) (by omega)
    rw [e1, e2, e3, show t + 8 * i + 8 * i = t + 16 * i by omega, Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _), rtop]
    have rw1 : natVal (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)) (t + 8 * i) i = natVal w (t + 8 * i) i :=
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)
    have rlo : natVal (w.writeLE (t + 16 * i) 8 (w.readLE (s.sp.toNat - 112) 8)) t i = natVal M t i :=
      keep _ _ (by omega) (by omega) (by omega)
    have hS1t : natVal S1m (t + 8 * i) i = natVal M (t + 8 * i) i :=
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hS1x : natVal S1m xp i = natVal s.mem xp i := by
      have := hl.zx; have := hl.xw
      rw [show natVal S1m xp i = S1m.readLE xp (8 * i) from rfl,
        hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact mxs _ _ (Nat.le_refl _) (by omega)
    have hMt := natVal_add M t i i
    rw [show i + i = 2 * i by omega, hvt] at hMt
    rw [rw1, rlo, SqrMath.sqT, hMt, ← SqrMath.natVal_eq_pre]
    rw [hS1t, hS1x] at hval
    simp only [SqrMath.lim]
    generalize natVal w (t + 8 * i) i = W at hval ⊢
    generalize w.readLE (s.sp.toNat - 112) 8 = c at hval ⊢
    generalize natVal M (t + 8 * i) i = Mt at hval ⊢
    generalize natVal M t i = Tlo
    generalize natVal s.mem xp i = X at hval ⊢
    generalize s.mem.readLE (xp + 8 * i) 8 = d at hval ⊢
    generalize 2 ^ (64 * i) = Q at hval ⊢
    rw [Nat.mul_zero, Nat.add_zero, hval, Nat.mul_add, Nat.mul_comm Q (X * d), Nat.mul_comm X d]
    omega
  case zero =>
    intro a n h1 h2
    have := hl.tw; have := hl.tz
    rw [keep a n (by omega) (by omega) (by omega)]
    exact hzero a n (by omega) h2

end FvModexp.Arm64.BasicSqr

namespace FvModexp.Arm64.BasicSqr

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

/-- after `lshVU(t[1:2n-1], t[1:2n-1], 1)` and `t[2n-1] = c`: `t[0:2n] = 2 · Σ_{j<n} x_j·x[0:j]·B^j` -/
theorem tval {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {st zp zl zc xp xl xc : Nat} {s : State}
    {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b L st zp zl zc xp xl s t L1 b1 w1 c1) {M C w : Memory}
    (hI : Inv R L st zp zl zc xp xl xc s t L1 b1 w1 c1 xl M)
    (hF : MemFrame M C [(s.sp.toNat - 200, s.sp.toNat - 144), (s.sp.toNat - 56, s.sp.toNat - 48)])
    (q1 : natVal w (t + 8) (2 * xl - 2) = (natVal C (t + 8) (2 * xl - 2) * 2) % 2 ^ (64 * (2 * xl - 2)))
    (q2 : w.readLE (s.sp.toNat - 144) 8 = (natVal C (t + 8) (2 * xl - 2) * 2) / 2 ^ (64 * (2 * xl - 2)))
    (q3 : MemFrame C w [(t + 8, t + 8 + 8 * (2 * xl - 2)), (s.sp.toNat - 144, s.sp.toNat - 136)]) :
    natVal (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE (s.sp.toNat - 144) 8)) t (2 * xl) =
      2 * SqrMath.sqT (SqrMath.lim s.mem xp) xl := by
  have hl := hE.lay
  have hx0 := hl.x0; have hbig := hE.big; have hsp0 := hl.sp0
  obtain ⟨-, -, hvt, -⟩ := hI
  have htw := hl.tw
  -- the old value: T = t0 + B (V + B^(2n-2) top)
  have hC : natVal C (t + 8) (2 * xl - 2) = natVal M (t + 8) (2 * xl - 2) :=
    hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  rw [hC] at q1 q2
  have e1 := natVal_add M t 1 (2 * xl - 1)
  have e2 := natVal_add M (t + 8 * 1) (2 * xl - 2) 1
  rw [show 1 + (2 * xl - 1) = 2 * xl by omega, hvt] at e1
  rw [show 2 * xl - 2 + 1 = 2 * xl - 1 by omega, show t + 8 * 1 = t + 8 by omega] at e2
  have e3 : natVal M t 1 = M.readLE t 8 := rfl
  have e4 : natVal M (t + 8 + 8 * (2 * xl - 2)) 1 = M.readLE (t + 8 * (2 * xl - 1)) 8 := by
    show M.readLE _ (8 * 1) = _; congr 1; omega
  rw [e2, e3, e4, show (64 * 1) = 64 by rfl] at e1
  have hmod := SqrMath.sqT_mod (SqrMath.lim s.mem xp) xl
  have hlt := SqrMath.sqT_lt (SqrMath.lim s.mem xp) (SqrMath.lim_lt s.mem xp) (xl - 1)
  rw [show xl - 1 + 1 = xl by omega, show 2 * (xl - 1) + 1 = 2 * xl - 1 by omega] at hlt
  -- the new value
  have f1 := natVal_add (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE (s.sp.toNat - 144) 8)) t 1 (2 * xl - 1)
  have f2 := natVal_add (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE (s.sp.toNat - 144) 8)) (t + 8 * 1) (2 * xl - 2) 1
  rw [show 1 + (2 * xl - 1) = 2 * xl by omega] at f1
  rw [show 2 * xl - 2 + 1 = 2 * xl - 1 by omega, show t + 8 * 1 = t + 8 by omega] at f2
  have g0 : natVal (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE (s.sp.toNat - 144) 8)) t 1 = M.readLE t 8 := by
    show Memory.readLE _ t (8 * 1) = _
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      q3.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have g1 : natVal (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE (s.sp.toNat - 144) 8)) (t + 8) (2 * xl - 2) =
      natVal w (t + 8) (2 * xl - 2) := Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have g2 : natVal (w.writeLE (t + 8 * (2 * xl - 1)) 8 (w.readLE (s.sp.toNat - 144) 8)) (t + 8 + 8 * (2 * xl - 2)) 1 =
      w.readLE (s.sp.toNat - 144) 8 := by
    show Memory.readLE _ _ (8 * 1) = _
    rw [show t + 8 + 8 * (2 * xl - 2) = t + 8 * (2 * xl - 1) by omega, Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)]
  rw [f1, f2, g0, g1, g2, q1, q2, Nat.mod_add_div]
  have ht0 : M.readLE t 8 < 2 ^ 64 := by have := Memory.readLE_lt M t 8; simpa using this
  have eP : 2 ^ (64 * (2 * xl - 1)) = 2 ^ 64 * 2 ^ (64 * (2 * xl - 2)) := by
    rw [← Nat.pow_add, show 64 + 64 * (2 * xl - 2) = 64 * (2 * xl - 1) by omega]
  rw [eP] at hlt
  rw [e1] at hmod hlt
  generalize natVal M (t + 8) (2 * xl - 2) = V at hmod hlt e1 ⊢
  generalize M.readLE t 8 = t0 at hmod hlt e1 ht0 ⊢
  generalize M.readLE (t + 8 * (2 * xl - 1)) 8 = top at hmod hlt e1
  generalize 2 ^ (64 * (2 * xl - 2)) = P at hmod hlt e1 ⊢
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht0] at hmod
  subst hmod
  have htop : top = 0 := by
    rcases Nat.eq_zero_or_pos top with h | h
    · exact h
    · exfalso
      have h1 : P ≤ V + P * top := by have := Nat.le_mul_of_pos_right P h; omega
      have h2 : 2 ^ 64 * P ≤ 2 ^ 64 * (V + P * top) := Nat.mul_le_mul_left _ h1
      omega
  subst htop
  rw [e1]; simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  rw [Nat.mul_comm V 2, Nat.mul_left_comm]

end FvModexp.Arm64.BasicSqr
