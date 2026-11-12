import FvModexp.Proofs.Arm64.Nat.KMulMath

set_option autoImplicit false

/-!
# `karatsuba` (arm64): the end (natmul.go:217, :250) — pure part

After `KM7` (`z = X0·Y0 + E²·X1·Y1`, `z1 = X0·Y1 + X1·Y0` in `t`): `addTo(z[n2:], z1.abs)` (`0x1bc1b4`), the defer bit
cleared, the deferred `stk.restore` closure (`karatsuba.deferwrap1`, `len(stk.w)` restored), the epilogue.
* `knAddPre` — `addTo`'s precondition at its entry (`z[n2:] = (zp + 8·n2, 2n - n2, zc - n2)`, `x = (t, l, kT)`);
* `KN.addStep` — `KN` after `addTo` (its writes are inside `z[0:2n]`);
* `kn_val` — `z[0:2n] = X·Y` after `addTo` (`kar_final`);
* `knRestPre` — the closure's precondition; `knEndFin` — `KPost` from `KN` and the last two frames.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (IntAt tN' stackBack_keep')

/-- `addTo`'s entry (`CALL` at `0x1bc1b4`) -/
abbrev kAddToA : Nat := 0x1b37f0

theorem kaddTo_entry : segAddr Extracted.program AddTo.fn = kAddToA := by decide

theorem kar_expand (x0 x1 y0 y1 E : Nat) :
    (x0 + E * x1) * (y0 + E * y1) = x0 * y0 + E * (x0 * y1 + x1 * y0) + E * E * (x1 * y1) := by
  have e : (x0 + E * x1) * (y0 + E * y1) = x0 * y0 + x0 * (E * y1) + (E * x1) * y0 + (E * x1) * (E * y1) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have h1 : x0 * (E * y1) = E * (x0 * y1) := by
    rw [← Nat.mul_assoc, Nat.mul_comm x0 E, Nat.mul_assoc]
  have h2 : (E * x1) * y0 = E * (x1 * y0) := Nat.mul_assoc _ _ _
  have h3 : (E * x1) * (E * y1) = E * E * (x1 * y1) := by
    rw [Nat.mul_assoc, ← Nat.mul_assoc x1, Nat.mul_comm x1 E, Nat.mul_assoc, ← Nat.mul_assoc]
  rw [e, h1, h2, h3, Nat.mul_add]; omega

/-- the high part after `addTo` does not wrap -/
theorem kar_final {lo hi w x0 x1 y0 y1 E F : Nat}
    (hEF : (x0 + E * x1) * (y0 + E * y1) < E * F)
    (h0 : lo + E * hi = x0 * y0 + E * E * (x1 * y1)) (hw : w = x0 * y1 + x1 * y0) :
    lo + E * ((hi + w) % F) = (x0 + E * x1) * (y0 + E * y1) := by
  have hx := kar_expand x0 x1 y0 y1 E
  have hs : lo + E * (hi + w) = (x0 + E * x1) * (y0 + E * y1) := by
    rw [Nat.mul_add, ← Nat.add_assoc, h0, hx, hw]; omega
  have hlt : hi + w < F := by
    have : E * (hi + w) < E * F := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  rw [Nat.mod_eq_of_lt hlt, hs]

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}

/-- `addTo(z[n2:], z1.abs)`'s precondition at its entry (`SP - 448`) -/
theorem knAddPre (h : KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {l : Nat}
    (hl : l ≤ kT n) (S1 : State) (hsp : S1.sp.toNat = s.sp.toNat - 448) (hg : S1.regs 28 = s.regs 28)
    (hm : S1.mem = M) :
    CallEnv R Lk S1 4240 48 ∧ l ≤ 2 * n - kh n ∧ 2 * n - kh n ≤ zc - kh n ∧ 2 * n - kh n < 2 ^ 40 ∧
      NatLive S1.mem R Lk (zp + 8 * kh n) (2 * n - kh n) ∧
      Outside (zp + 8 * kh n) (8 * (2 * n - kh n)) (win S1 4240 48) ∧ zc - kh n < 2 ^ 63 ∧
      S1.mem.accessible t (8 * l) false = true ∧ t + 8 * l ≤ 2 ^ 48 ∧
      Held R Lk t (8 * l) ∧ Outside t (8 * l) (win S1 4240 48) ∧
      (0 < l → Apart (zp + 8 * kh n) (8 * (2 * n - kh n)) t (8 * l)) ∧
      Apart (zp + 8 * kh n) (8 * (2 * n - kh n)) ((S1.regs 28).toNat + 16) 8 ∧
      R.inv bk Lk (S1.regs 28).toNat (view R.rt Lk S1.mem) := by
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, -, -, -, -, hzl, hzc40, hout, -, -⟩ := h.lay
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, hzh, hz48⟩ := h.zops
  obtain ⟨htl, htw, htg, htz, -, -, ht48⟩ := h.tops
  have hkT : kT n = 2 * kh n + 1 := rfl
  have hkh : kh n = (n + 1) / 2 := rfl
  obtain ⟨-, hth, htacc, -⟩ := htl (by omega)
  obtain ⟨hzal, -, hzacc, -⟩ := hzlive (by omega)
  have hce := h.callee (S1 := S1) (stk1 := 4240) (above1 := 48) hsp hg hm (by omega) (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw htw ⊢
  simp only [NatSqr.guard] at hzg htg
  rw [hm, hg, hsp]
  refine ⟨hce, by omega, by omega, by omega, fun _ => ⟨by omega, hzh.sub (by omega) (by omega),
    Memory.accessible_sub _ hzacc (Or.inr rfl) (by omega) (by omega), by omega⟩, by omega, by omega,
    Memory.accessible_sub _ htacc (Or.inl rfl) (Nat.le_refl _) (by omega), by omega,
    hth.sub (Nat.le_refl _) (by omega), by omega, fun _ => by unfold Apart at htz ⊢; omega,
    by unfold Apart at hzg ⊢; omega, h.inv⟩

set_option maxRecDepth 20000 in
/-- **`KN` after `addTo`** (writes `z[n2:2n]`, `R.rt`, its window; charges nothing) -/
theorem KN.addStep (h : KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {M' : Memory}
    {S1 : State} (hsp : S1.sp.toNat = s.sp.toNat - 448)
    (hF : MemFrame M M' (R.rt ++ winA S1 4240 48 ++ [(zp + 8 * kh n, zp + 8 * kh n + 8 * (2 * n - kh n))]))
    (hLF : LiveFrame M M' Lk [(zp + 8 * kh n, zp + 8 * kh n + 8 * (2 * n - kh n))])
    (hreg : M'.regions = M.regions)
    {Lk' : List (Nat × Nat)} {bk' : Nat} (hext : LiveExt R Lk Lk') (hb : bk ≤ bk')
    (hinv : R.inv bk' Lk' (s.regs 28).toNat (view R.rt Lk' M')) :
    KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk' bk' spent M' := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, hzl, -, hout, -, -⟩ := h.lay
  have hstw : Outside st 24 (win s W 72) := h.F.stk.2.2.1
  have hzs1 := h.F.zs.1
  have hkh : kh n = (n + 1) / 2 := rfl
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  unfold Apart at hzs1
  simp only [winA, hsp] at hF
  have hF' : MemFrame M M' (R.rt ++ ([(s.sp.toNat - 448 - 4240, s.sp.toNat - 448 - 8),
      (s.sp.toNat - 448 + 8, s.sp.toNat - 448 + 48)] ++
      [(zp + 8 * kh n, zp + 8 * kh n + 8 * (2 * n - kh n))])) := by
    rw [← List.append_assoc]; exact hF
  have hsb : StackBackL R Lk Lk' st M M' := by
    refine stackBack_keep' h.sok hF'
      (FvModexp.LiveFrame.mono_ws hLF fun a k ho => by rw [outside_append] at ho; exact ho.2) ?_ hext
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨by omega, by omega⟩, by omega⟩
  have := h.step (k := 4240) (a := 48) (by omega) (by omega) (fun r hr => ?_) hF hLF hreg hext (c := 0)
    (by omega) hinv hsb
  · simpa using this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩

end

/-- **`z[0:2n] = X·Y` after `addTo`** -/
theorem kn_val {M A : Memory} {zp t l n : Nat} (X0 X1 Y0 Y1 X Y : Nat) (h40 : 40 ≤ n)
    (hX : X = X0 + 2 ^ (64 * kh n) * X1) (hY : Y = Y0 + 2 ^ (64 * kh n) * Y1)
    (hXlt : X < 2 ^ (64 * n)) (hYlt : Y < 2 ^ (64 * n))
    (hlo : natVal A zp (kh n) = natVal M zp (kh n))
    (hhi : natVal A (zp + 8 * kh n) (2 * n - kh n) =
      (natVal M (zp + 8 * kh n) (2 * n - kh n) + natVal M t l) % 2 ^ (64 * (2 * n - kh n)))
    (zlo : natVal M zp (2 * kh n) = X0 * Y0) (zhi : natVal M (zp + 16 * kh n) (2 * n - 2 * kh n) = X1 * Y1)
    (hw : natVal M t l = X0 * Y1 + X1 * Y0) : natVal A zp (2 * n) = X * Y := by
  have hkn : n ≤ 2 * kh n ∧ 2 * kh n ≤ n + 1 := by simp only [kh]; omega
  have e1 := natVal_add A zp (kh n) (2 * n - kh n)
  rw [show kh n + (2 * n - kh n) = 2 * n by omega] at e1
  have e2 := natVal_add M zp (kh n) (2 * n - kh n)
  rw [show kh n + (2 * n - kh n) = 2 * n by omega] at e2
  have e3 := natVal_add M zp (2 * kh n) (2 * n - 2 * kh n)
  rw [show 2 * kh n + (2 * n - 2 * kh n) = 2 * n by omega, show zp + 8 * (2 * kh n) = zp + 16 * kh n by omega]
    at e3
  have hEE : 2 ^ (64 * (2 * kh n)) = 2 ^ (64 * kh n) * 2 ^ (64 * kh n) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hEF : 2 ^ (64 * kh n) * 2 ^ (64 * (2 * n - kh n)) = 2 ^ (64 * n) * 2 ^ (64 * n) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have h0 : natVal M zp (kh n) + 2 ^ (64 * kh n) * natVal M (zp + 8 * kh n) (2 * n - kh n) =
      X0 * Y0 + 2 ^ (64 * kh n) * 2 ^ (64 * kh n) * (X1 * Y1) := by
    rw [← e2, e3, zlo, zhi, hEE]
  have hlt : (X0 + 2 ^ (64 * kh n) * X1) * (Y0 + 2 ^ (64 * kh n) * Y1) <
      2 ^ (64 * kh n) * 2 ^ (64 * (2 * n - kh n)) := by
    rw [hEF, ← hX, ← hY]; exact Nat.mul_lt_mul'' hXlt hYlt
  have := kar_final hlt h0 hw
  rw [e1, hlo, hhi, hX, hY]; exact this

/-- `addTo` as a summary in `LibMul.program` -/
theorem knAddSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Summary (LibMul.program.link impl) kAddToA
      (fun s => RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [zp, zl, zc, xp, xl, xc] ∧
        (CallEnv R L s 4240 48 ∧ xl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat < 2 ^ 40 ∧
          NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4240 48) ∧ zc.toNat < 2 ^ 63 ∧
          s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
          Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4240 48) ∧
          (0 < xl.toNat → Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * xl.toNat)) ∧
          Apart zp.toNat (8 * zl.toNat) ((s.regs 28).toNat + 16) 8 ∧
          R.inv b L (s.regs 28).toNat (view R.rt L s.mem)))
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        (natVal s'.mem zp.toNat zl.toNat =
          (natVal s.mem zp.toNat zl.toNat + natVal s.mem xp.toNat xl.toNat) % 2 ^ (64 * zl.toNat) ∧
        ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
          R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
          MemFrame s.mem s'.mem (R.rt ++ winA s 4240 48 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
          LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)])) := by
  have hS := Ensures.toSummaryIn (AddTo.ens impl hap R hmv b L zp zl zc xp xl xc)
    (noExit_restrict hap AddTo.names) (codeIn_restrict_mono hap (IntAS.sub_of_all (ms := LibMul.names) (by decide)))
  rw [← LibMul.eq_only, kaddTo_entry] at hS
  exact hS

set_option maxRecDepth 20000 in
/-- **The `addTo(z[n2:], z1.abs)` call** (at its entry, from `KM7`'s memory): the continuation gets `KN` (all charged)
and `z[0:2n] = X·Y` -/
theorem kn_addcall (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk l : Nat} {S : State}
    (hB : KM7 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk l)
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 kAddToA) (hsp : S1.sp.toNat = s.sp.toNat - 448)
    (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = S.mem) (hra : S1.regs 30 = BitVec.ofNat 64 (0x1bbe70 + 4 * 210))
    (r0 : S1.regs 0 = BitVec.ofNat 64 (zp + 8 * kh n)) (r1 : S1.regs 1 = BitVec.ofNat 64 (2 * n - kh n))
    (r2 : S1.regs 2 = BitVec.ofNat 64 (zc - kh n)) (r3 : S1.regs 3 = BitVec.ofNat 64 t)
    (r4 : S1.regs 4 = BitVec.ofNat 64 l) (r5 : S1.regs 5 = BitVec.ofNat 64 (kT n))
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ s2 : State, s2.pc = BitVec.ofNat 64 (0x1bbe70 + 4 * 210) → s2.mem.regions = S.mem.regions →
      (s2.sp = S1.sp ∧ s2.regs 28 = S1.regs 28 ∧ s2.regs 29 = S1.regs 29 ∧ s2.regs 18 = S1.regs 18) →
      ∀ (Lk' : List (Nat × Nat)) (bk' : Nat),
        KN R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk' bk' (kc7 (stLen s.mem st) n) s2.mem →
      natVal s2.mem zp (2 * n) = natVal s.mem xp n * natVal s.mem yp n → ReachesRet (LibMul.program.link impl) ret s2 Q) :
    ReachesRet (LibMul.program.link impl) ret S1 Q := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  have hkn : n ≤ 2 * kh n ∧ 2 * kh n ≤ n + 1 := by simp only [kh]; omega
  have hkT : kT n = 2 * kh n + 1 := rfl
  have hl := hB.hl
  obtain ⟨htl, -, -, -, -, -, ht48⟩ := hkm.tops
  obtain ⟨-, -, hzw, -, -, -, -, hzh, hz48⟩ := hkm.zops
  have hP := knAddPre hkm hl S1 hsp hg hm
  have b0 : zp + 8 * kh n < 2 ^ 64 := by omega
  have b1 : 2 * n - kh n < 2 ^ 64 := by omega
  have b2 : zc - kh n < 2 ^ 64 := by omega
  have b3 : t < 2 ^ 64 := by omega
  have b4 : l < 2 ^ 64 := by omega
  have b5 : kT n < 2 ^ 64 := by omega
  refine ReachesRet.call_regions (knAddSum impl hap R hmv bk Lk (BitVec.ofNat 64 (zp + 8 * kh n))
    (BitVec.ofNat 64 (2 * n - kh n)) (BitVec.ofNat 64 (zc - kh n)) (BitVec.ofNat 64 t) (BitVec.ofNat 64 l)
    (BitVec.ofNat 64 (kT n))) hpc ⟨?_, ⟨r0, r1, r2, r3, r4, r5, trivial⟩, ?_⟩ fun s2 hr hq hreg => ?_
  · rw [hra, tN' (by omega)]; exact kn_ra hap (by decide) 210 (by decide)
  · simp only [tN' b0, tN' b1, tN' b2, tN' b3, tN' b4]; exact hP
  · obtain ⟨hk, hval, L', b', hext, hbud, hinv, hF, hLF⟩ := hq
    simp only [tN' b0, tN' b1, tN' b3, tN' b4] at hval hF hLF
    rw [hg] at hinv
    rw [hm] at hF hLF hreg hval
    have hkmA := hkm.addStep hsp hF hLF hreg hext hbud hinv
    have hrdZ : ∀ x m, zp ≤ x → x + m ≤ zp + 8 * kh n → s2.mem.readLE x m = S.mem.readLE x m := by
      intro x m h1 h2
      have hzw' := hzw
      simp only [win, outside_cons, outside_nil, and_true] at hzw'
      refine Held.readLE2 (hzh.sub h1 (by omega)) hF hLF ?_ ?_
      · simp only [winA, outside_cons, outside_nil, and_true]; rw [hsp]; omega
      · simp only [outside_cons, outside_nil, and_true]; omega
    have hX := natVal_add s.mem xp (kh n) (n - kh n)
    rw [show kh n + (n - kh n) = n by omega] at hX
    have hY := natVal_add s.mem yp (kh n) (n - kh n)
    rw [show kh n + (n - kh n) = n by omega] at hY
    have hz := kn_val (M := S.mem) (A := s2.mem) (zp := zp) (t := t) (l := l) (kX0 s xp n) (kX1 s xp n)
      (kX0 s yp n) (kX1 s yp n) (natVal s.mem xp n) (natVal s.mem yp n) h40 hX hY (natVal_lt _ _ _)
      (natVal_lt _ _ _) (by unfold natVal; exact hrdZ _ _ (Nat.le_refl _) (by omega))
      hval hB.zlo hB.zhi hB.z1v
    exact hK s2 (by rw [hr, hra]) (by rw [hreg]) hk L' b' hkmA hz

end FvModexp.Arm64.NatMul
