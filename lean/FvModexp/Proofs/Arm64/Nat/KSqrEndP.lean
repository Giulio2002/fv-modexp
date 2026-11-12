import FvModexp.Proofs.Arm64.Nat.KSqrB

/-!
# `karatsubaSqr` (arm64): the end (natmul.go:304, :332) — pure part

After `KB7` (`z = X0² + E²·X1²`, `z1 = 2·X0·X1` in `t`): `addTo(z[n2:], z1.abs)` (`0x1bc54c`), the defer bit cleared,
the deferred `stk.restore` closure (`karatsubaSqr.deferwrap1`, `len(stk.w)` restored), the epilogue.
* `kAddPre` — `addTo`'s precondition at its entry (`z[n2:] = (zp + 8·n2, 2n - n2, zc - n2)`, `x = (t, l, kT)`);
* `KM.addStep` — `KM` after `addTo` (its writes are inside `z[0:2n]`);
* `ks_val` — `z[0:2n] = X²` after `addTo` (`ks_final`);
* `kRestPre` — the closure's precondition; `kEndFin` — `KPost` from `KM` and the last two frames.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- `addTo`'s entry (`CALL` at `0x1bc54c`) -/
abbrev addToA : Nat := 0x1b37f0

theorem addTo_entry : segAddr Extracted.program AddTo.fn = addToA := by decide

/-- `addTo(z[n2:], z1.abs)`'s precondition at its entry (`SP - 320`) -/
theorem kAddPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) {l : Nat} (hl : l ≤ kT n)
    (S1 : State) (hsp : S1.sp.toNat = s.sp.toNat - 320) (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = M) :
    CallEnv R Lk S1 4240 48 ∧ l ≤ 2 * n - kn2 n ∧ 2 * n - kn2 n ≤ zc - kn2 n ∧ 2 * n - kn2 n < 2 ^ 40 ∧
      NatLive S1.mem R Lk (zp + 8 * kn2 n) (2 * n - kn2 n) ∧
      Outside (zp + 8 * kn2 n) (8 * (2 * n - kn2 n)) (win S1 4240 48) ∧ zc - kn2 n < 2 ^ 63 ∧
      S1.mem.accessible t (8 * l) false = true ∧ t + 8 * l ≤ 2 ^ 48 ∧
      Held R Lk t (8 * l) ∧ Outside t (8 * l) (win S1 4240 48) ∧
      (0 < l → Apart (zp + 8 * kn2 n) (8 * (2 * n - kn2 n)) t (8 * l)) ∧
      Apart (zp + 8 * kn2 n) (8 * (2 * n - kn2 n)) ((S1.regs 28).toNat + 16) 8 ∧
      R.inv bk Lk (S1.regs 28).toNat (view R.rt Lk S1.mem) := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := h.lay
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, -, hzh, hz48⟩ := h.zops
  obtain ⟨htl, htw, htg, htz, -, ht48⟩ := h.tops
  have hkT : kT n = 2 * kn2 n + 1 := rfl
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  obtain ⟨-, hth, htacc, -⟩ := htl (by omega)
  obtain ⟨hzal, -, hzacc, -⟩ := hzlive (by omega)
  have hce := h.callee (S1 := S1) (stk1 := 4240) (above1 := 48) hsp hg hm (by omega) (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw htw ⊢
  simp only [guard] at hzg htg
  rw [hm, hg, hsp]
  refine ⟨hce, by omega, by omega, by omega, fun _ => ⟨by omega, hzh.sub (by omega) (by omega),
    Memory.accessible_sub _ hzacc (Or.inr rfl) (by omega) (by omega), by omega⟩, by omega, by omega,
    Memory.accessible_sub _ htacc (Or.inl rfl) (Nat.le_refl _) (by omega), by omega,
    hth.sub (Nat.le_refl _) (by omega), by omega, fun _ => by unfold Apart at htz ⊢; omega,
    by unfold Apart at hzg ⊢; omega, h.inv⟩

/-- **`KM` after `addTo`** (writes `z[n2:2n]`, `R.rt`, its window; charges nothing) -/
theorem KM.addStep {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) {M' : Memory} {S1 : State}
    (hsp : S1.sp.toNat = s.sp.toNat - 320)
    (hF : MemFrame M M' (R.rt ++ winA S1 4240 48 ++ [(zp + 8 * kn2 n, zp + 8 * kn2 n + 8 * (2 * n - kn2 n))]))
    (hLF : LiveFrame M M' Lk [(zp + 8 * kn2 n, zp + 8 * kn2 n + 8 * (2 * n - kn2 n))])
    (hreg : M'.regions = M.regions)
    {Lk' : List (Nat × Nat)} {bk' : Nat} (hext : LiveExt R Lk Lk') (hb : bk ≤ bk')
    (hinv : R.inv bk' Lk' (s.regs 28).toNat (view R.rt Lk' M')) :
    KM R b L W st zp zc xp n xc s lx0 lx1 t Lk' bk' spent M' := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, hout, -, -⟩ := h.lay
  have hstw : Outside st 24 (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hzs : StkSep s.mem st zp (8 * zc) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzl : 2 * n ≤ zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  have hzs1 := hzs.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  unfold Apart at hzs1
  simp only [winA, hsp] at hF
  have hF' : MemFrame M M' (R.rt ++ ([(s.sp.toNat - 320 - 4240, s.sp.toNat - 320 - 8),
      (s.sp.toNat - 320 + 8, s.sp.toNat - 320 + 48)] ++
      [(zp + 8 * kn2 n, zp + 8 * kn2 n + 8 * (2 * n - kn2 n))])) := by
    rw [← List.append_assoc]; exact hF
  have hsb : StackBackL R Lk Lk' st M M' := by
    refine stackBack_keep' h.sok hF' (FvModexp.LiveFrame.mono_ws hLF fun a k ho => by rw [outside_append] at ho; exact ho.2) ?_ hext
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨by omega, by omega⟩, by omega⟩
  have := h.step (k := 4240) (a := 48) (by omega) (by omega) (fun r hr => ?_) hF hLF hreg hext (c := 0)
    (by omega) hinv hsb
  · simpa using this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩

/-- **`z[0:2n] = X²` after `addTo`**: the low `n2` limbs are untouched, the high part is `(hi + 2·X0·X1) mod F`, which
does not wrap (`ks_final`) -/
theorem ks_val {M A : Memory} {zp t l n : Nat} (X0 X1 X : Nat) (h80 : 80 ≤ n)
    (hX : X = X0 + 2 ^ (64 * kn2 n) * X1) (hXlt : X < 2 ^ (64 * n))
    (hlo : natVal A zp (kn2 n) = natVal M zp (kn2 n))
    (hhi : natVal A (zp + 8 * kn2 n) (2 * n - kn2 n) =
      (natVal M (zp + 8 * kn2 n) (2 * n - kn2 n) + natVal M t l) % 2 ^ (64 * (2 * n - kn2 n)))
    (zlo : natVal M zp (2 * kn2 n) = X0 * X0) (zhi : natVal M (zp + 16 * kn2 n) (2 * n - 2 * kn2 n) = X1 * X1)
    (hw : natVal M t l = 2 * X0 * X1) : natVal A zp (2 * n) = X * X := by
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  have e1 := natVal_add A zp (kn2 n) (2 * n - kn2 n)
  rw [show kn2 n + (2 * n - kn2 n) = 2 * n by omega] at e1
  have e2 := natVal_add M zp (kn2 n) (2 * n - kn2 n)
  rw [show kn2 n + (2 * n - kn2 n) = 2 * n by omega] at e2
  have e3 := natVal_add M zp (2 * kn2 n) (2 * n - 2 * kn2 n)
  rw [show 2 * kn2 n + (2 * n - 2 * kn2 n) = 2 * n by omega, show zp + 8 * (2 * kn2 n) = zp + 16 * kn2 n by omega]
    at e3
  have hEE : 2 ^ (64 * (2 * kn2 n)) = 2 ^ (64 * kn2 n) * 2 ^ (64 * kn2 n) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hEF : 2 ^ (64 * kn2 n) * 2 ^ (64 * (2 * n - kn2 n)) = 2 ^ (64 * n) * 2 ^ (64 * n) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have h0 : natVal M zp (kn2 n) + 2 ^ (64 * kn2 n) * natVal M (zp + 8 * kn2 n) (2 * n - kn2 n) =
      X0 * X0 + 2 ^ (64 * kn2 n) * 2 ^ (64 * kn2 n) * (X1 * X1) := by
    rw [← e2, e3, zlo, zhi, hEE]
  have hlt : (X0 + 2 ^ (64 * kn2 n) * X1) * (X0 + 2 ^ (64 * kn2 n) * X1) <
      2 ^ (64 * kn2 n) * 2 ^ (64 * (2 * n - kn2 n)) := by
    rw [hEF, ← hX]; exact Nat.mul_lt_mul'' hXlt hXlt
  have := ks_final hlt h0 hw
  rw [e1, hlo, hhi, hX]; exact this

/-- the deferred closure's precondition (`Restore.Pre`) at its entry: `R26 = SP - 168` (the defer record), the
memory = `KM`'s plus the defer-bit store -/
theorem kRestPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) (S2 : State)
    (hsp : S2.sp.toNat = s.sp.toNat - 320) (hg : S2.regs 28 = s.regs 28)
    (h26 : (S2.regs 26).toNat = s.sp.toNat - 168) (h30 : S2.regs 30 = BitVec.ofNat 64 0x1bc560)
    (hF : MemFrame M S2.mem [(s.sp.toNat - 249, s.sp.toNat - 248)]) : Restore.Pre S2 := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have hce := h.callee (S1 := { S2 with mem := M }) (stk1 := 24) (above1 := 0) hsp hg rfl (by omega) (by omega)
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal', hb', ha', hw'⟩, -⟩ := hce
  have hstw : Outside st 24 (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  obtain ⟨hst8, -, hstacc, hst48, -, hslc, -⟩ := h.sok
  have hsl := h.slen
  have hrd : ∀ x m, (x + m ≤ s.sp.toNat - 249 ∨ s.sp.toNat - 248 ≤ x) → S2.mem.readLE x m = M.readLE x m :=
    fun x m hx => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hgw : S2.mem.readLE ((s.regs 28).toNat + 16) 8 = M.readLE ((s.regs 28).toNat + 16) 8 := by
    unfold Apart at hga; exact hrd _ _ (by omega)
  have hdst : S2.mem.readLE (s.sp.toNat - 168 + 8) 8 = st := by
    rw [hrd _ _ (by omega), show s.sp.toNat - 168 + 8 = s.sp.toNat - 160 by omega]; exact h.dst
  have hdln : S2.mem.readLE (s.sp.toNat - 168 + 16) 8 = stLen s.mem st := by
    rw [hrd _ _ (by omega), show s.sp.toNat - 168 + 16 = s.sp.toNat - 152 by omega]; exact h.dln
  have hcap : S2.mem.readLE (st + 16) 8 = stCap M st := hrd _ _ (by omega)
  have hacc : ∀ a k w, S2.mem.accessible a k w = M.accessible a k w := fun a k w => hF.accessible a k w
  simp only at hg1 hg2 hg3 hal' hb' ha' hw'
  rw [← hg] at hgw
  unfold Restore.Pre GuardOK
  refine ⟨⟨hg1, by rw [hacc]; exact hg2, by rw [hgw]; omega⟩, ⟨hal', hb', ha', by rw [hacc]; exact hw'⟩,
    by rw [h30]; decide, by rw [h30]; decide, by rw [h26]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h26, hacc, h.fr.accessible]
    exact Memory.accessible_sub _ (h.pre.1.2.1.2.2.2) (Or.inl rfl) (by omega) (by omega)
  · rw [h26, hdst]; omega
  · rw [h26, hdst, hacc]; exact hstacc
  · rw [h26, hdst, hdln, hcap]; simp only [stLen, stCap] at hsl hslc ⊢; omega
  · rw [h26, hdst, hsp]; unfold Apart; omega
  · rw [h26, hsp]; unfold Apart; omega

/-- **`KPost` at the return**: from `KM` after `addTo` (memory `A`, everything charged), the defer-bit store, the
closure's frame and `len(stk.w)` restored (memory `F`) -/
theorem kEndFin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk : Nat} {A : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc7 (stLen s.mem st) n) A) {F : Memory}
    (hF : MemFrame A F [(s.sp.toNat - 249, s.sp.toNat - 248), (s.sp.toNat - 344, s.sp.toNat - 328),
      (st + 8, st + 16)])
    (hlen : F.readLE (st + 8) 8 = stLen s.mem st)
    (hz : natVal A zp (2 * n) = natVal s.mem xp n * natVal s.mem xp n) (s' : State) (hs' : s'.mem = F) :
    KPost R b L W st zp (2 * n) xp n s s' := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have hstw : Outside st 24 (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hzw : Outside zp (8 * zc) (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzs : StkSep s.mem st zp (8 * zc) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzs1 := hzs.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw hzw
  unfold Apart at hzs1
  have hok := h.sok
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hslc, hsc40⟩ := hok
  have hsl := h.slen
  subst hs'
  have hrd : ∀ x m, Outside x m [(s.sp.toNat - 249, s.sp.toNat - 248), (s.sp.toNat - 344, s.sp.toNat - 328),
      (st + 8, st + 16)] → s'.mem.readLE x m = A.readLE x m := fun x m hx => hF.readLE _ _ hx
  have eW : s'.mem.readLE st 8 = A.readLE st 8 := hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have eC : s'.mem.readLE (st + 16) 8 = A.readLE (st + 16) 8 :=
    hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hzF : natVal s'.mem zp (2 * n) = natVal A zp (2 * n) :=
    hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a k w, s'.mem.accessible a k w = A.accessible a k w := fun a k w => hF.accessible a k w
  refine ⟨hzF.trans hz, Lk, bk, h.ext, ?bud, ?inv, ?sb, ?mf, ?lf⟩
  case bud => have := h.bud; have := kc7_le (ℓ := stLen s.mem st) h80; omega
  case inv =>
    refine RtInv.inv_frame' hF (fun r hr => ?_) h.inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · left; exact hout.of_sub (by omega) (by omega)
    · left; exact hout.of_sub (by omega) (by omega)
    · rcases hsth.sub (a := st + 8) (n := 8) (by omega) (by omega) with h1 | h1
      · right; simpa using h1
      · left; simpa using h1
  case sb =>
    refine ⟨⟨⟨hst8, hsth, by rw [hacc]; exact hstacc, hst48, ?_, ?_, ?_⟩, hlen, ?_⟩, ?_⟩
    · show NatLive s'.mem R Lk (s'.mem.readLE st 8) (s'.mem.readLE (st + 16) 8)
      rw [eW, eC]
      intro h0
      obtain ⟨a1, a2, a3, a4⟩ := hnl h0
      exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
    · show s'.mem.readLE (st + 8) 8 ≤ s'.mem.readLE (st + 16) 8
      rw [hlen]; have := eC; simp only [stLen, stCap] at hsl hslc ⊢; omega
    · show s'.mem.readLE (st + 16) 8 < 2 ^ 40
      rw [eC]; exact hsc40
    · show (s'.mem.readLE st 8 = stW s.mem st ∧ s'.mem.readLE (st + 16) 8 = stCap s.mem st) ∨
        (InRanges (s'.mem.readLE st 8) (8 * s'.mem.readLE (st + 16) 8) R.rt ∧
          ApartAll (s'.mem.readLE st 8) (8 * s'.mem.readLE (st + 16) 8) L)
      rw [eW, eC]; exact h.sarr
    · show ¬(s'.mem.readLE st 8 = stW s.mem st ∧ s'.mem.readLE (st + 16) 8 = stCap s.mem st) →
        (s'.mem.readLE st 8, s'.mem.readLE st 8 + 8 * s'.mem.readLE (st + 16) 8) ∈ Lk
      rw [eW, eC]; exact h.smem
  case mf =>
    refine h.fr.trans hF fun x m ho => ⟨ho, ?_⟩
    simp only [winA, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  case lf =>
    refine ⟨fun x m hin hz => ?_⟩
    rw [hrd x m ?_]
    · exact h.lf.readLE x m hin hz
    · obtain ⟨r, hr, i1, i2⟩ := hin
      have := h.wsep r hr
      simp only [win, stkWs, outside_cons, outside_nil, and_true] at this hz ⊢
      omega

/-- `addTo` as a summary in `LibSqr.program` -/
theorem ksAddSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Summary (LibSqr.program.link impl) addToA
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
    (noExit_restrict hap AddTo.names) (codeIn_restrict_mono hap (IntAS.sub_of_all (ms := LibSqr.names) (by decide)))
  rw [← LibSqr.eq_only, addTo_entry] at hS
  exact hS

set_option maxRecDepth 20000 in
/-- **The `addTo(z[n2:], z1.abs)` call** (at its entry, from `KB7`'s memory): the continuation gets `KM` (all charged)
and `z[0:2n] = X²` -/
theorem ks_addcall (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 t : Nat}
    {Lk : List (Nat × Nat)} {bk l : Nat} {S : State} (hB : KB7 R b L W st zp zc xp n xc s lx0 lx1 t S Lk bk l)
    (S1 : State) (hpc : S1.pc = BitVec.ofNat 64 addToA) (hsp : S1.sp.toNat = s.sp.toNat - 320)
    (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = S.mem) (hra : S1.regs 30 = BitVec.ofNat 64 (0x1bc2b0 + 4 * 168))
    (r0 : S1.regs 0 = BitVec.ofNat 64 (zp + 8 * kn2 n)) (r1 : S1.regs 1 = BitVec.ofNat 64 (2 * n - kn2 n))
    (r2 : S1.regs 2 = BitVec.ofNat 64 (zc - kn2 n)) (r3 : S1.regs 3 = BitVec.ofNat 64 t)
    (r4 : S1.regs 4 = BitVec.ofNat 64 l) (r5 : S1.regs 5 = BitVec.ofNat 64 (kT n))
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ s2 : State, s2.pc = BitVec.ofNat 64 (0x1bc2b0 + 4 * 168) → s2.mem.regions = S.mem.regions →
      (s2.sp = S1.sp ∧ s2.regs 28 = S1.regs 28 ∧ s2.regs 29 = S1.regs 29 ∧ s2.regs 18 = S1.regs 18) →
      ∀ (Lk' : List (Nat × Nat)) (bk' : Nat), KM R b L W st zp zc xp n xc s lx0 lx1 t Lk' bk' (kc7 (stLen s.mem st) n) s2.mem →
      natVal s2.mem zp (2 * n) = natVal s.mem xp n * natVal s.mem xp n → ReachesRet (LibSqr.program.link impl) ret s2 Q) :
    ReachesRet (LibSqr.program.link impl) ret S1 Q := by
  have hkm := hB.km
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, -, -⟩ := hkm.lay
  have hkn : n ≤ 2 * kn2 n ∧ 2 * kn2 n ≤ n + 1 := by simp only [kn2]; omega
  have hkT : kT n = 2 * kn2 n + 1 := rfl
  have hl := hB.hl
  obtain ⟨htl, -, -, -, -, ht48⟩ := hkm.tops
  obtain ⟨-, -, hzw, -, -, -, -, -, hzh, hz48⟩ := hkm.zops
  have hP := kAddPre hkm hl S1 hsp hg hm
  have b0 : zp + 8 * kn2 n < 2 ^ 64 := by omega
  have b1 : 2 * n - kn2 n < 2 ^ 64 := by omega
  have b2 : zc - kn2 n < 2 ^ 64 := by omega
  have b3 : t < 2 ^ 64 := by omega
  have b4 : l < 2 ^ 64 := by omega
  have b5 : kT n < 2 ^ 64 := by omega
  refine ReachesRet.call_regions (ksAddSum impl hap R hmv bk Lk (BitVec.ofNat 64 (zp + 8 * kn2 n))
    (BitVec.ofNat 64 (2 * n - kn2 n)) (BitVec.ofNat 64 (zc - kn2 n)) (BitVec.ofNat 64 t) (BitVec.ofNat 64 l)
    (BitVec.ofNat 64 (kT n))) hpc ⟨?_, ⟨r0, r1, r2, r3, r4, r5, trivial⟩, ?_⟩ fun s2 hr hq hreg => ?_
  · rw [hra, tN' (by omega)]; exact ks_ra hap (by decide) 168 (by decide)
  · simp only [tN' b0, tN' b1, tN' b2, tN' b3, tN' b4]; exact hP
  · obtain ⟨hk, hval, L', b', hext, hbud, hinv, hF, hLF⟩ := hq
    simp only [tN' b0, tN' b1, tN' b3, tN' b4] at hval hF hLF
    rw [hg] at hinv
    rw [hm] at hF hLF hreg hval
    have hkmA := hkm.addStep hsp hF hLF hreg hext hbud hinv
    have hrdZ : ∀ x m, zp ≤ x → x + m ≤ zp + 8 * kn2 n → s2.mem.readLE x m = S.mem.readLE x m := by
      intro x m h1 h2
      have hzw' := hzw
      simp only [win, outside_cons, outside_nil, and_true] at hzw'
      refine Held.readLE2 (hzh.sub h1 (by omega)) hF hLF ?_ ?_
      · simp only [winA, outside_cons, outside_nil, and_true]; rw [hsp]; omega
      · simp only [outside_cons, outside_nil, and_true]; omega
    have hX := natVal_add s.mem xp (kn2 n) (n - kn2 n)
    rw [show kn2 n + (n - kn2 n) = n by omega] at hX
    have hz := ks_val (M := S.mem) (A := s2.mem) (zp := zp) (t := t) (l := l) (kX0 s xp n) (kX1 s xp n)
      (natVal s.mem xp n) h80 hX (natVal_lt _ _ _) (by unfold natVal; exact hrdZ _ _ (Nat.le_refl _) (by omega))
      hval hB.zlo hB.zhi hB.z1v
    exact hK s2 (by rw [hr, hra]) (by rw [hreg]) hk L' b' hkmA hz

set_option maxRecDepth 20000 in
/-- **The deferred closure call** (at `karatsubaSqr.deferwrap1`'s entry, memory = `KM`'s plus the defer-bit store): the
continuation (at `0x1bc560`) gets the saved `X29`/`X30` and `KPost` for every state with its memory -/
theorem ks_restcall (impl : List Segment) (hD : Summary (LibSqr.program.link impl) 0x1bc5e0 Restore.Pre Restore.Post)
    {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk : Nat} {A : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk (kc7 (stLen s.mem st) n) A)
    (hz : natVal A zp (2 * n) = natVal s.mem xp n * natVal s.mem xp n)
    (S2 : State) (hpc : S2.pc = BitVec.ofNat 64 0x1bc5e0) (hsp : S2.sp.toNat = s.sp.toNat - 320)
    (hg : S2.regs 28 = s.regs 28) (h26 : (S2.regs 26).toNat = s.sp.toNat - 168)
    (h30 : S2.regs 30 = BitVec.ofNat 64 0x1bc560) (hF : MemFrame A S2.mem [(s.sp.toNat - 249, s.sp.toNat - 248)])
    {ret : BitVec 64} {Q : State → Prop}
    (hK : ∀ s3 : State, s3.pc = BitVec.ofNat 64 0x1bc560 → s3.sp = S2.sp → s3.regs 28 = S2.regs 28 →
      s3.regs 18 = S2.regs 18 → s3.mem.readLE (s.sp.toNat - 328) 8 = (s.regs 29).toNat →
      s3.mem.readLE (s.sp.toNat - 320) 8 = (s.regs 30).toNat →
      (∀ a k w, s3.mem.accessible a k w = A.accessible a k w) →
      (∀ s' : State, s'.mem = s3.mem → KPost R b L W st zp (2 * n) xp n s s') →
      ReachesRet (LibSqr.program.link impl) ret s3 Q) :
    ReachesRet (LibSqr.program.link impl) ret S2 Q := by
  have hP := kRestPre h S2 hsp hg h26 h30 hF
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have hstw : Outside st 24 (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hrd : ∀ x m, (x + m ≤ s.sp.toNat - 249 ∨ s.sp.toNat - 248 ≤ x) → S2.mem.readLE x m = A.readLE x m :=
    fun x m hx => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hdst : S2.mem.readLE ((S2.regs 26).toNat + 8) 8 = st := by
    rw [h26, hrd _ _ (by omega), show s.sp.toNat - 168 + 8 = s.sp.toNat - 160 by omega]; exact h.dst
  have hdln : S2.mem.readLE ((S2.regs 26).toNat + 16) 8 = stLen s.mem st := by
    rw [h26, hrd _ _ (by omega), show s.sp.toNat - 168 + 16 = s.sp.toNat - 152 by omega]; exact h.dln
  refine ReachesRet.call_regions hD hpc hP fun s3 hr hq hreg => ?_
  obtain ⟨q1, q2, q3, -, q5, q6⟩ := hq
  rw [hdst, hdln] at q5
  rw [hdst, hsp] at q6
  have hFF : MemFrame A s3.mem [(s.sp.toNat - 249, s.sp.toNat - 248), (s.sp.toNat - 344, s.sp.toNat - 328),
      (st + 8, st + 16)] :=
    hF.trans q6 fun x m ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hr2 : ∀ x m, s.sp.toNat - 328 ≤ x → x + m ≤ s.sp.toNat - 312 → s3.mem.readLE x m = A.readLE x m :=
    fun x m h1 h2 => hFF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  exact hK s3 (by rw [hr, h30]) q1 q3 q2 ((hr2 _ _ (by omega) (by omega)).trans h.fp)
    ((hr2 _ _ (by omega) (by omega)).trans h.lr) (fun a k w => hFF.accessible a k w) fun s' hs' => kEndFin h hFF q5 hz s' hs'

end FvModexp.Arm64.NatSqr
