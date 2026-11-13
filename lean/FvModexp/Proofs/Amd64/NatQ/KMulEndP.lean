import FvModexp.Proofs.Amd64.NatQ.KMulMath

set_option autoImplicit false

/-!
# [amd64 port (divmc s51) of the Q-form Arm64/NatQ/KMulEndP.lean + KMulEnd.lean (pure part) — TIGHT COSTS] `karatsuba` (amd64): the end (natmul.go:217, :250) — pure part

After `KM7` (`z = X0·Y0 + E²·X1·Y1`, `z1 = X0·Y1 + X1·Y0` in `t`): `addTo(z[n2:], z1.abs)` (`CALL` at `0x5f2277`, return
`0x5f227c` pushed at `RSP - 456`), the defer bit cleared, the deferred `stk.restore` closure (`karatsuba.deferwrap1`,
`CALL SI` at `0x5f228c`, return `0x5f228e`, `RDX` = the defer record `RSP - 232`), the epilogue.
* `knAddPre` — `addTo`'s precondition at its entry (`z[n2:] = (zp + 8·n2, 2n - n2, zc - n2)`, `x = (t, l, kT)`);
* `KN.addStep` — `KN` after `addTo` (its writes are inside `z[0:2n]`);
* `kn_val` — `z[0:2n] = X·Y` after `addTo` (`kar_final`);
* `knRestPre` — the closure's precondition; `knEndFin` — `KPost` from `KN` and the last frames.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (IntAt tN' stackBack_keepC tls pushRd StkSep)

/-- `addTo`'s entry (`CALL` at `0x5f2277`) -/
abbrev kAddToA : Nat := 0x5e62c0

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

theorem sp_add8E {a c : BitVec 64} (h : a.toNat = c.toNat - 456) (hc : 456 ≤ c.toNat) : a + 8#64 = c - 448#64 := by
  apply BitVec.eq_of_toNat_eq
  have := c.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}

/-- `addTo(z[n2:], z1.abs)`'s precondition at its entry (`RSP - 456`) -/
theorem knAddPre (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {l : Nat}
    (hl : l ≤ kT n) (S1 : State) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456) (hg : S1.regs 14 = s.regs 14)
    (hm : S1.mem = M) (hfs : S1.fsBase = s.fsBase) :
    CallEnv R Lk S1 4232 48 ∧ l ≤ 2 * n - kh n ∧ 2 * n - kh n ≤ zc - kh n ∧ 2 * n - kh n < 2 ^ 40 ∧
      NatLive S1.mem R Lk (zp + 8 * kh n) (2 * n - kh n) ∧
      Outside (zp + 8 * kh n) (8 * (2 * n - kh n)) (win S1 4232 48) ∧ zc - kh n < 2 ^ 63 ∧
      S1.mem.accessible t (8 * l) false = true ∧ t + 8 * l ≤ 2 ^ 48 ∧
      Held R Lk t (8 * l) ∧ Outside t (8 * l) (win S1 4232 48) ∧
      (0 < l → Apart (zp + 8 * kh n) (8 * (2 * n - kh n)) t (8 * l)) ∧
      Apart (zp + 8 * kh n) (8 * (2 * n - kh n)) ((S1.regs 14).toNat + 16) 8 ∧
      Apart (zp + 8 * kh n) (8 * (2 * n - kh n)) (S1.fsBase.toNat - 8) 8 ∧
      R.inv bk Lk (S1.regs 14).toNat (view R.rt Lk S1.mem) := by
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, -, -, -, -, hzl, hzc40, hout, -, -⟩ := h.lay
  obtain ⟨-, hzlive, hzw, hzg, -, -, -, hzh, hz48⟩ := h.zops
  obtain ⟨htl, htw, htg, htz, -, -, ht48⟩ := h.tops
  obtain ⟨-, hzt⟩ := h.ttls
  have hkT : kT n = 2 * kh n + 1 := rfl
  have hkh : kh n = (n + 1) / 2 := rfl
  obtain ⟨-, hth, htacc, -⟩ := htl (by omega)
  obtain ⟨hzal, -, hzacc, -⟩ := hzlive (by omega)
  have hce := h.callee (S1 := S1) (stk1 := 4232) (above1 := 48) hsp hg hm hfs (by omega) (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw htw ⊢
  simp only [NatSqr.guard, tls] at hzg htg hzt
  rw [hm, hg, hsp, hfs]
  refine ⟨hce, by omega, by omega, by omega, fun _ => ⟨by omega, hzh.sub (by omega) (by omega),
    Janus.Arm64.Memory.accessible_sub _ hzacc (Or.inr rfl) (by omega) (by omega), by omega⟩, by omega, by omega,
    Janus.Arm64.Memory.accessible_sub _ htacc (Or.inl rfl) (Nat.le_refl _) (by omega), by omega,
    hth.sub (Nat.le_refl _) (by omega), by omega, fun _ => by unfold Apart at htz ⊢; omega,
    by unfold Apart at hzg ⊢; omega, by unfold Apart at hzt ⊢; omega, h.inv⟩

set_option maxRecDepth 20000 in
/-- **`KN` after `addTo`** (writes `z[n2:2n]`, `R.rt`, its window; charges nothing) -/
theorem KN.addStep (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) {M' : Memory}
    {S1 : State} (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456)
    (hF : MemFrame M M' (R.rt ++ win S1 4232 48 ++ [(zp + 8 * kh n, zp + 8 * kh n + 8 * (2 * n - kh n))]))
    (hLF : LiveFrame M M' Lk [(zp + 8 * kh n, zp + 8 * kh n + 8 * (2 * n - kh n))])
    (hreg : M'.regions = M.regions)
    {Lk' : List (Nat × Nat)} {bk' : Nat} (hext : LiveExt R Lk Lk') (hb : bk ≤ bk')
    (hinv : R.inv bk' Lk' (s.regs 14).toNat (view R.rt Lk' M')) :
    KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk' bk' spent M' := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, hzl, -, hout, -, -⟩ := h.lay
  have hstw : Outside st 24 (win s W 72) := h.F.stk.2.2.1
  have hzs1 := h.F.zs.1
  have hkh : kh n = (n + 1) / 2 := rfl
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  unfold Apart at hzs1
  simp only [win, hsp] at hF
  have hF' : MemFrame M M' (R.rt ++ ([((s.regs 4).toNat - 456 - 4232, (s.regs 4).toNat - 456 + 48)] ++
      [(zp + 8 * kh n, zp + 8 * kh n + 8 * (2 * n - kh n))])) := by
    rw [← List.append_assoc]; exact hF
  have hsbC : StackBackL R Lk Lk' st M M' ∧ stCap M' st = stCap M st := by
    refine stackBack_keepC h.sok hF'
      (FvModexp.LiveFrame.mono_ws hLF fun a k ho => by rw [outside_append] at ho; exact ho.2) ?_ hext
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨by omega, by omega⟩
  have := h.step (k := 4232) (a := 48) (by omega) (by omega) (fun r hr => ?_) hF hLF hreg hext (c := 0)
    (Or.inr ⟨by omega, hsbC.2⟩) (by have := h.spk; omega) hinv hsbC.1
  · simpa using this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact ⟨by simp only; omega, Or.inl ⟨by simp only; omega, by simp only; omega⟩⟩

/-- the deferred closure's precondition (`Restore.Pre`) at its entry (`RSP = SP - 456`, return address pushed there):
`RDX = SP - 232` (the defer record), the memory = `KN`'s plus the defer-bit store and the push -/
theorem knRestPre (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk spent M) (S2 : State)
    (hsp : (S2.regs 4).toNat = (s.regs 4).toNat - 456)
    (h2 : (S2.regs 2).toNat = (s.regs 4).toNat - 232)
    (hF : MemFrame M S2.mem [((s.regs 4).toNat - 369, (s.regs 4).toNat - 368),
      ((s.regs 4).toNat - 456, (s.regs 4).toNat - 448)])
    (hra : S2.mem.readLE ((s.regs 4).toNat - 456) 8 = 0x5f228e) : Restore.Pre S2 := by
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have hw0 : s.mem.accessible ((s.regs 4).toNat - W) (W + 72) true = true := h.F.env.2.1.2.2
  have hstw : Outside st 24 (win s W 72) := h.F.stk.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  obtain ⟨hst8, -, hstacc, hst48, -, hslc, -⟩ := h.sok
  have hsl := h.slen
  have hrd : ∀ x m, (x + m ≤ (s.regs 4).toNat - 369 ∨ (s.regs 4).toNat - 368 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 456 ∨ (s.regs 4).toNat - 448 ≤ x) → S2.mem.readLE x m = M.readLE x m :=
    fun x m hx hy => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hdst : S2.mem.readLE ((s.regs 4).toNat - 232 + 8) 8 = st := by
    rw [hrd _ _ (by omega) (by omega), show (s.regs 4).toNat - 232 + 8 = (s.regs 4).toNat - 224 by omega]; exact h.dst
  have hdln : S2.mem.readLE ((s.regs 4).toNat - 232 + 16) 8 = stLen s.mem st := by
    rw [hrd _ _ (by omega) (by omega), show (s.regs 4).toNat - 232 + 16 = (s.regs 4).toNat - 216 by omega]; exact h.dln
  have hcap : S2.mem.readLE (st + 16) 8 = stCap M st := hrd _ _ (by omega) (by omega)
  have hacc : ∀ a k w, S2.mem.accessible a k w = M.accessible a k w := fun a k w => hF.accessible a k w
  unfold Restore.Pre StackWritable
  simp only [regSP]
  rw [hsp, h2, hdst, hdln, hcap, hra]
  simp only [hacc]
  refine ⟨⟨by omega, by omega, ?_⟩, by omega, by decide, by omega, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rw [h.fr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hw0 (by omega) (by omega)
  · rw [h.fr.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hw0 (Or.inl rfl) (by omega) (by omega)
  · exact hstacc
  · simp only [stLen, stCap] at hsl hslc ⊢; omega
  · unfold Apart; omega
  · unfold Apart; omega

/-- **`KPost` at the return**: from `KN` after `addTo` (memory `A`, everything charged), the defer-bit store, the
push, the closure's frame and `len(stk.w)` restored (memory `F`) -/
theorem knEndFin {A : Memory}
    (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc7 n) A) {F : Memory}
    (hF : MemFrame A F [((s.regs 4).toNat - 369, (s.regs 4).toNat - 368),
      ((s.regs 4).toNat - 464, (s.regs 4).toNat - 448), (st + 8, st + 16)])
    (hlen : F.readLE (st + 8) 8 = stLen s.mem st)
    (hz : natVal A zp (2 * n) = natVal s.mem xp n * natVal s.mem yp n) (s' : State) (hs' : s'.mem = F)
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df) :
    KPost R b H L W st zp (2 * n) xp n yp n s s' := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have hstw : Outside st 24 (win s W 72) := h.F.stk.2.2.1
  have hzw : Outside zp (8 * zc) (win s W 72) := h.F.zw
  have hzs : StkSep s.mem st zp (8 * zc) := h.F.zs
  have hzs1 := hzs.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw hzw
  unfold Apart at hzs1
  have hok := h.sok
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hslc, hsc40⟩ := hok
  have hsl := h.slen
  subst hs'
  have hrd : ∀ x m, Outside x m [((s.regs 4).toNat - 369, (s.regs 4).toNat - 368),
      ((s.regs 4).toNat - 464, (s.regs 4).toNat - 448), (st + 8, st + 16)] → s'.mem.readLE x m = A.readLE x m :=
    fun x m hx => hF.readLE _ _ hx
  have eW : s'.mem.readLE st 8 = A.readLE st 8 := hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have eC : s'.mem.readLE (st + 16) 8 = A.readLE (st + 16) 8 :=
    hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hzF : natVal s'.mem zp (2 * n) = natVal A zp (2 * n) :=
    hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hacc : ∀ a k w, s'.mem.accessible a k w = A.accessible a k w := fun a k w => hF.accessible a k w
  refine ⟨hfs, hdf, hzF.trans hz, Lk, bk, h.ext, ?bud, ?inv, ?sb, ?mf, ?lf⟩
  case bud =>
    have := h.bud; have := kc7_le n
    rw [stkR_congr (m := A) (m' := s'.mem) (by simp only [stCap]; exact eC)]; omega
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
    · exact h.smem.congr eW eC fun _ h => h
  case mf =>
    refine h.fr.trans hF fun x m ho => ⟨ho, ?_⟩
    simp only [win, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
    omega
  case lf =>
    refine ⟨fun x m hin hz => ?_⟩
    rw [hrd x m ?_]
    · exact h.lf.readLE x m hin hz
    · obtain ⟨r, hr, i1, i2⟩ := hin
      have := h.wsep r hr
      simp only [win, stkWs, outside_cons, outside_nil, and_true] at this hz ⊢
      omega

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
theorem knAddSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Summary (LibMul.program.link impl) kAddToA
      (fun s => RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) (s.mem.readLE (s.regs regSP).toNat 8) ∧
        s.xmm xmmZero = 0 ∧ ArgsFrom64 s 0 [zp, zl, zc, xp, xl, xc] ∧ s.df = false ∧
        (CallEnv R L s 4232 48 ∧ xl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat < 2 ^ 40 ∧
          NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4232 48) ∧ zc.toNat < 2 ^ 63 ∧
          s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
          Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4232 48) ∧
          (0 < xl.toNat → Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * xl.toNat)) ∧
          Apart zp.toNat (8 * zl.toNat) ((s.regs 14).toNat + 16) 8 ∧ Apart zp.toNat (8 * zl.toNat) (s.fsBase.toNat - 8) 8 ∧
          R.inv b L (s.regs 14).toNat (view R.rt L s.mem)))
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        (s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ natVal s'.mem zp.toNat zl.toNat =
          (natVal s.mem zp.toNat zl.toNat + natVal s.mem xp.toNat xl.toNat) % 2 ^ (64 * zl.toNat) ∧
        ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
          R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
          MemFrame s.mem s'.mem (R.rt ++ win s 4232 48 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
          LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)])) := by
  have hS := Ensures.toSummaryIn (AddTo.ens impl hap R hmv b L zp zl zc xp xl xc)
    (A64.noExit_restrict64 hap AddTo.names) (by simp [numIntRegs])
    (A64.codeIn_restrict_mono64 hap (IntAS.sub_of_all (ms := LibMul.names) (by decide)))
  rw [← LibMul.eq_only, kaddTo_entry] at hS
  exact hS

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The `addTo(z[n2:], z1.abs)` call** (at its entry, return `0x5f227c` pushed on `KM7`'s memory): the continuation
gets `KNAt`, `KN` (all charged) and `z[0:2n] = X·Y` -/
theorem kn_addcall (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State} {lx0 lx1 ly0 ly1 t : Nat}
    {Lk : List (Nat × Nat)} {bk l : Nat} {S : State}
    (hB : KM7 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t S Lk bk l)
    (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    (S1 : State) (hpc : S1.rip = BitVec.ofNat 64 kAddToA) (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 456)
    (hg : S1.regs 14 = s.regs 14) (h5 : S1.regs 5 = s.regs 4 - 8#64) (hfs : S1.fsBase = s.fsBase)
    (hdf : S1.df = s.df) (hx15 : S1.xmm 15 = s.xmm 15)
    (hm : S1.mem = S.mem.writeLE ((s.regs 4).toNat - 456) 8 0x5f227c)
    (r0 : S1.regs 0 = BitVec.ofNat 64 (zp + 8 * kh n)) (r1 : S1.regs 3 = BitVec.ofNat 64 (2 * n - kh n))
    (r2 : S1.regs 1 = BitVec.ofNat 64 (zc - kh n)) (r3 : S1.regs 7 = BitVec.ofNat 64 t)
    (r4 : S1.regs 6 = BitVec.ofNat 64 l) (r5 : S1.regs 8 = BitVec.ofNat 64 (kT n))
    {ret : W64} {Q : State → Prop}
    (hK : ∀ s2 : State, KNAt s s2 0x5f227c → s2.mem.regions = S.mem.regions →
      ∀ (Lk' : List (Nat × Nat)) (bk' : Nat),
        KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk' bk' (kc7 n) s2.mem →
      natVal s2.mem zp (2 * n) = natVal s.mem xp n * natVal s.mem yp n → ReachesRet (LibMul.program.link impl) ret s2 Q) :
    ReachesRet (LibMul.program.link impl) ret S1 Q := by
  have hkmS := hB.km
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, -, -⟩ := hkmS.lay
  have hkm := hkmS.push 0x5f227c
  rw [← hm] at hkm
  have hkn : n ≤ 2 * kh n ∧ 2 * kh n ≤ n + 1 := by simp only [kh]; omega
  have hkT : kT n = 2 * kh n + 1 := rfl
  have hl := hB.hl
  obtain ⟨htl, htw, -, -, -, -, ht48⟩ := hkm.tops
  obtain ⟨-, -, hzw, -, -, -, -, hzh, hz48⟩ := hkm.zops
  have hzw' := hzw; have htw' := htw
  simp only [win, outside_cons, outside_nil, and_true] at hzw' htw'
  have hpr : ∀ x m, (x + m ≤ (s.regs 4).toNat - 456 ∨ (s.regs 4).toNat - 448 ≤ x) →
      S1.mem.readLE x m = S.mem.readLE x m := fun x m h => by rw [hm]; exact pushRd (by omega)
  have zlo : natVal S1.mem zp (2 * kh n) = kX0 s xp n * kX0 s yp n := by
    rw [← hB.zlo]; unfold natVal; exact hpr _ _ (by omega)
  have zhi : natVal S1.mem (zp + 16 * kh n) (2 * n - 2 * kh n) = kX1 s xp n * kX1 s yp n := by
    rw [← hB.zhi]; unfold natVal; exact hpr _ _ (by omega)
  have z1v : natVal S1.mem t l = kX0 s xp n * kX1 s yp n + kX1 s xp n * kX0 s yp n := by
    rw [← hB.z1v]; unfold natVal; exact hpr _ _ (by omega)
  have hP := knAddPre hkm hl S1 hsp hg rfl hfs
  have b0 : zp + 8 * kh n < 2 ^ 64 := by omega
  have b1 : 2 * n - kh n < 2 ^ 64 := by omega
  have b2 : zc - kh n < 2 ^ 64 := by omega
  have b3 : t < 2 ^ 64 := by omega
  have b4 : l < 2 ^ 64 := by omega
  have b5 : kT n < 2 ^ 64 := by omega
  have hrd : S1.mem.readLE (S1.regs 4).toNat 8 = 0x5f1da0 + 1244 := by
    rw [hm, hsp, Janus.Arm64.Memory.readLE_writeLE_self]
  refine ReachesRet.call_regions (knAddSum impl hap R hmv bk Lk (BitVec.ofNat 64 (zp + 8 * kh n))
    (BitVec.ofNat 64 (2 * n - kh n)) (BitVec.ofNat 64 (zc - kh n)) (BitVec.ofNat 64 t) (BitVec.ofNat 64 l)
    (BitVec.ofNat 64 (kT n))) hpc ⟨?_, hx15.trans hx150, by simp [ArgsFrom64, argReg, intArgRegs, r0, r1, r2, r3, r4, r5],
      hdf.trans hdf0, ?_⟩ fun s2 hr hq hreg => ?_
  · simp only [regSP]; rw [hrd]; exact kn_ra hap (by decide) 1244 (by decide)
  · simp only [tN' b0, tN' b1, tN' b2, tN' b3, tN' b4]; exact hP
  · obtain ⟨hk, efs, edf, hval, L', b', hext, hbud, hinv, hF, hLF⟩ := hq
    simp only [tN' b0, tN' b1, tN' b3, tN' b4] at hval hF hLF
    rw [hg] at hinv
    have hkmA := hkm.addStep hsp hF hLF hreg hext hbud hinv
    have hrdZ : ∀ x m, zp ≤ x → x + m ≤ zp + 8 * kh n → s2.mem.readLE x m = S1.mem.readLE x m := by
      intro x m h1 h2
      refine Held.readLE2 (hzh.sub h1 (by omega)) hF hLF ?_ ?_
      · simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]; omega
      · simp only [outside_cons, outside_nil, and_true]; omega
    have hX := natVal_add s.mem xp (kh n) (n - kh n)
    rw [show kh n + (n - kh n) = n by omega] at hX
    have hY := natVal_add s.mem yp (kh n) (n - kh n)
    rw [show kh n + (n - kh n) = n by omega] at hY
    have hz := kn_val (M := S1.mem) (A := s2.mem) (zp := zp) (t := t) (l := l) (kX0 s xp n) (kX1 s xp n)
      (kX0 s yp n) (kX1 s yp n) (natVal s.mem xp n) (natVal s.mem yp n) h40 hX hY (natVal_lt _ _ _)
      (natVal_lt _ _ _) (by unfold natVal; exact hrdZ _ _ (Nat.le_refl _) (by omega)) hval zlo zhi z1v
    have hA : KNAt s s2 0x5f227c := ⟨by rw [hr, retAddrOf, hrd], by rw [hk.1]; exact sp_add8E hsp (by omega),
      hk.2.2.1.trans hg, hk.2.1.trans h5, efs.trans hfs, edf.trans hdf, hk.2.2.2.trans hx15⟩
    exact hK s2 hA (by rw [hreg, hm]; simp only [Janus.Arm64.Memory.regions_writeLE]) L' b' hkmA hz

set_option maxRecDepth 20000 in
/-- **The deferred closure call** (at `karatsuba.deferwrap1`'s entry, memory = `KN`'s plus the defer-bit store
and the push of `0x5f228e`): the continuation (at `0x5f228e`) gets the saved `RBP`/return address and `KPost` for
every state with its memory, TLS base and DF -/
theorem kn_restcall (impl : List Amd64.Segment) (hD : Summary (LibMul.program.link impl) kDfn Restore.Pre Restore.Post)
    {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 t : Nat} {Lk : List (Nat × Nat)} {bk : Nat} {A : Memory}
    (h : KN R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 t Lk bk (kc7 n) A)
    (hz : natVal A zp (2 * n) = natVal s.mem xp n * natVal s.mem yp n)
    (S2 : State) (hpc : S2.rip = BitVec.ofNat 64 kDfn) (hsp : (S2.regs 4).toNat = (s.regs 4).toNat - 456)
    (h2 : (S2.regs 2).toNat = (s.regs 4).toNat - 232)
    (hF : MemFrame A S2.mem [((s.regs 4).toNat - 369, (s.regs 4).toNat - 368),
      ((s.regs 4).toNat - 456, (s.regs 4).toNat - 448)])
    (hra : S2.mem.readLE ((s.regs 4).toNat - 456) 8 = 0x5f228e)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ s3 : State, s3.rip = BitVec.ofNat 64 0x5f228e → s3.regs 4 = S2.regs 4 + 8 → s3.regs 5 = S2.regs 5 →
      s3.regs 14 = S2.regs 14 → s3.xmm 15 = S2.xmm 15 → s3.fsBase = S2.fsBase → s3.df = S2.df →
      s3.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat →
      s3.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 →
      (∀ a k w, s3.mem.accessible a k w = A.accessible a k w) →
      (∀ s' : State, s'.mem = s3.mem → s'.fsBase = s.fsBase → s'.df = s.df → KPost R b H L W st zp (2 * n) xp n yp n s s') →
      ReachesRet (LibMul.program.link impl) ret s3 Q) :
    ReachesRet (LibMul.program.link impl) ret S2 Q := by
  have hP := knRestPre h S2 hsp h2 hF hra
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hyc, hyc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have hstw : Outside st 24 (win s W 72) := h.F.stk.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hrd : ∀ x m, (x + m ≤ (s.regs 4).toNat - 369 ∨ (s.regs 4).toNat - 368 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 456 ∨ (s.regs 4).toNat - 448 ≤ x) → S2.mem.readLE x m = A.readLE x m :=
    fun x m hx hy => hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hdst : S2.mem.readLE ((S2.regs 2).toNat + 8) 8 = st := by
    rw [h2, hrd _ _ (by omega) (by omega), show (s.regs 4).toNat - 232 + 8 = (s.regs 4).toNat - 224 by omega]; exact h.dst
  have hdln : S2.mem.readLE ((S2.regs 2).toNat + 16) 8 = stLen s.mem st := by
    rw [h2, hrd _ _ (by omega) (by omega), show (s.regs 4).toNat - 232 + 16 = (s.regs 4).toNat - 216 by omega]; exact h.dln
  refine ReachesRet.call_regions hD hpc hP fun s3 hr hq hreg => ?_
  obtain ⟨q4, q5, q14, q15, qfs, qdf, q7, q8⟩ := hq
  rw [hdst, hdln] at q7
  rw [hdst, hsp] at q8
  have hFF : MemFrame A s3.mem [((s.regs 4).toNat - 369, (s.regs 4).toNat - 368),
      ((s.regs 4).toNat - 464, (s.regs 4).toNat - 448), (st + 8, st + 16)] :=
    hF.trans q8 fun x m ho => by
      simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hr2 : ∀ x m, (s.regs 4).toNat - 8 ≤ x → x + m ≤ (s.regs 4).toNat + 8 → s3.mem.readLE x m = A.readLE x m :=
    fun x m h1 h2 => hFF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  exact hK s3 (by rw [hr, retAddrOf, hsp, hra]) q4 q5 q14 q15 qfs qdf ((hr2 _ _ (by omega) (by omega)).trans h.fp)
    ((hr2 _ _ (by omega) (by omega)).trans h.lr) (fun a k w => hFF.accessible a k w)
    fun s' hs' hfs' hdf' => knEndFin h hFF q7 hz s' hs' hfs' hdf'

end FvModexp.Amd64.Q.NatMul
