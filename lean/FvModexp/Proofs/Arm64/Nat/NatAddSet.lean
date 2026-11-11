import FvModexp.Proofs.Arm64.Nat.NatAddMid
import FvModexp.Proofs.Common.AsmVW

/-!
# `nat.add` (arm64): `case n == 0: return z.set(x)` from `+0x19c` (after `z.make(m)`)

`z.set(x)` (nat.go:83) = `z = z.make(len(x)); copy(z, x); return z`. At `+0x19c` (the join of the reuse and the two
`makeslice` paths of `make(m)`): `R0 = p`, `R1 = m`, `R2 = c`, `R3 = xp`, `R4 = m` (`len z`).
`CMP R4, R1; CSEL LT, R1, R4, R5` (`min`); `CMP R0, R3; BEQ` (Go's `copy` skips `memmove` when the pointers agree);
spills to `120/112/144(RSP')`; `memmove(p, xp, 8 m)`; `return z[:m]`. The result is normalised because `x` is.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatAdd

abbrev hSet : Nat := segAddr Extracted.program fn + 0x19c

/-- The facts at `+0x19c` (cf. `Mid`): the result array `(p, c)`, `c ≥ m`, of `make(m)`. -/
structure SetMid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl : BitVec 64) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory) : Prop where
  gok : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4304 < s.sp.toNat
  g48 : (s.regs 28).toNat + 24 ≤ 2 ^ 48
  al : s.sp.toNat % 16 = 0
  sp0 : 4304 ≤ s.sp.toNat
  sp1 : s.sp.toNat + 80 ≤ 2 ^ 48
  wrt : Outside (s.sp.toNat - 4304) (4304 + 80) R.rt
  gw : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4304) (4304 + 80)
  grt : Outside ((s.regs 28).toNat + 16) 8 R.rt
  lr4 : (s.regs 30).toNat % 4 = 0
  lr48 : (s.regs 30).toNat < 2 ^ 48
  xl40 : xl.toNat < 2 ^ 40
  x0 : 0 < xl.toNat
  lr : M.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat
  sacc : M.accessible (s.sp.toNat - 4304) (4304 + 80) true = true
  gacc : M.accessible ((s.regs 28).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8
  cap : xl.toNat ≤ c
  c41 : c < 2 ^ 41
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) (s.sp.toNat - 4304) (4304 + 80)
  pheld : Held R L' p (8 * c)
  px : p = xp.toNat ∨ Apart p (8 * c) xp.toNat (8 * xl.toNat)
  xacc : M.accessible xp.toNat (8 * xl.toNat) false = true
  x48 : xp.toNat + 8 * xl.toNat ≤ 2 ^ 48
  xw : Apart xp.toNat (8 * xl.toNat) (s.sp.toNat - 4304) (4304 + 80)
  xv : natVal M xp.toNat xl.toNat = natVal s.mem xp.toNat xl.toNat
  xn : M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8 ≠ 0
  ext : LiveExt R L L'
  bud : b - makeCost xl.toNat ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M)
  lsep : LiveSep L' (win s 4304 80)
  ror : (p = zp.toNat ∧ c = zc.toNat) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ winA s 4304 80 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)])
  lf : LiveFrame s.mem M L [(zp.toNat, zp.toNat + 8 * zc.toNat)]
  mv : ∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k]

/-- **The postcondition of the `z.set(x)` path** from the final memory `M'`: `M` changed by the window and (when
`p ≠ xp`) the copy into `p[:m]`. -/
theorem SetMid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl yp yl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M M' : Memory}
    (h : SetMid R b L zp zc xp xl s p c L' b' M) (hy0 : yl.toNat = 0)
    (hF : MemFrame M M' (R.rt ++ [(s.sp.toNat - 4304, s.sp.toNat - 8), (p, p + 8 * xl.toNat)]))
    (hLF : LiveFrame M M' L' [(p, p + 8 * xl.toNat)])
    (hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M'))
    (hcp : M'.readLE p (8 * xl.toNat) = M.readLE xp.toNat (8 * xl.toNat))
    (hnz : M'.readLE (p + 8 * (xl.toNat - 1)) 8 = M.readLE (xp.toNat + 8 * (xl.toNat - 1)) 8)
    (s' : State) (hm : s'.mem = M') (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 1).toNat = xl.toNat)
    (h2 : (s'.regs 2).toNat = c) :
    PostS 4304 R b L zp zc xp xl yp yl s s' := by
  subst hm
  have hpw := h.pw; have hsp0 := h.sp0; have hcap := h.cap
  unfold Apart at hpw
  have hneed : need xl yl = xl.toNat := by unfold need mx; rw [if_pos (by omega)]; omega
  refine ⟨p, xl.toNat, c, h0, h1, h2, ?_, Or.inr ?_, hcap, by unfold mx; omega, L', b', h.ext, by rw [hneed]; exact h.bud,
    hinv, fun _ => ⟨h.p8, h.pheld, by rw [hF.accessible]; exact h.pacc, h.p48⟩, h.ror, ?_, ?_⟩
  · show s'.mem.readLE p (8 * xl.toNat) = _ + natVal s.mem yp.toNat yl.toNat
    rw [hcp, hy0, natVal_zero, Nat.add_zero]; exact h.xv
  · rw [hnz]; exact h.xn
  · refine h.mf.trans hF fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1, hw2⟩, hz⟩ := ho
    refine ⟨hrt, by omega, ?_⟩
    rcases h.ror with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · omega
    · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hLF.readLE a n (h.ext.inRanges_old hin) ?_]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      simp only [outside_cons, outside_nil, and_true] at hz ⊢
      rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hap⟩
      · omega
      · have := hap q hq; unfold Apart at this; omega

end FvModexp.Arm64.NatAdd

namespace FvModexp.Arm64.NatAdd

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-- **`SetMid` on the reuse path** (`zc ≥ m`). -/
theorem setmid_of_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    {M : Memory} (hpre : PreS 4304 R b L zp zc xp xl xc yp yl yc s) (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48) (hz : xl.toNat ≤ zc.toNat)
    (hF : MemFrame s.mem M (winA s 4304 80))
    (r1 : M.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat) (r2 : M.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat) :
    SetMid R b L zp zc xp xl s zp.toNat zc.toNat L b M := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, hzl, hzw', hzw, hxacc, hx48, hxh, hxn, _, hxw, hyacc, hy48, hyh, hyw, hinv, _, hmv⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  obtain ⟨hzg, hzx, hzy⟩ := hzw (by omega)
  simp only [win, outside_cons, outside_nil, and_true] at hzw' hxw hyw
  unfold Apart at hga
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4304 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  exact {
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl40 := hx40, x0 := hx0, lr := r1, fp := r2,
    sacc := by rw [hF.accessible]; exact hw, gacc := by rw [hF.accessible]; exact hg2,
    grd := hF.readLE _ _ (hFo _ _ (by omega)), cap := hz, c41 := by omega, p8 := hzal, p48 := hz48,
    pacc := by rw [hF.accessible]; exact hzacc, pw := by unfold Apart; omega, pheld := hzh,
    px := hzx.imp (fun e => by rw [e]) id,
    xacc := by rw [hF.accessible]; exact hxacc, x48 := hx48, xw := by unfold Apart; omega,
    xv := natVal_frame hF (hFo _ _ (by omega)),
    xn := by
      rw [hF.readLE _ _ (hFo _ _ (by omega))]
      rcases hxn with h0 | h0
      · omega
      · exact h0,
    ext := LiveExt.refl R L, bud := Nat.sub_le _ _, inv := inv_frame_winA hF hout hb' (by omega) hinv, lsep := hLs,
    ror := Or.inl ⟨rfl, rfl⟩, mf := hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2,
    lf := liveFrame_of_frame (rs := winA s 4304 80) (hF.mono fun a n h => by
        simp only [outside_append] at h; exact h.1) (fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega)
      (fun r hr => by
        simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp only <;> omega),
    mv := fun d src k hk => hmv d src k (by unfold mx; omega) }

/-- **`SetMid` on an allocation path** (`zc < m`): `makeslice(Word, m, c)` (`c = makeCap m`) at `SP' = SP - 160`
returned `[ptr, ptr + round)`. -/
theorem setmid_of_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s : State} {M0 m : Memory} {ptr round c : Nat} (hpre : PreS 4304 R b L zp zc xp xl xc yp yl yc s)
    (hy0 : yl.toNat = 0) (hx0 : 0 < xl.toNat)
    (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hF : MemFrame s.mem M0 (winA s 4304 80))
    (r1 : M0.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat) (r2 : M0.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat)
    (hLF : LiveFrame M0 m L [])
    (hMF : MemFrame M0 m (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
      (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 28).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hc1 : xl.toNat ≤ c) (hc2 : c ≤ xl.toNat + 4) (hsz : 8 * c ≤ round) (hcost : round ≤ makeCost xl.toNat) :
    SetMid R b L zp zc xp xl s ptr c (L ++ [(ptr, ptr + round)]) (b - round) m := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, _, hout, hga, hgr, hLs, _⟩, _, hxc, hyc, hxc40, hyc40, hx40, hy40,
    hz40, hzl, hzw', hzw, hxacc, hx48, hxh, hxn, _, hxw, hyacc, hy48, hyh, hyw, hinv0, _, hmv⟩ := hpre
  simp only [win, outside_cons, outside_nil, and_true] at hxw hyw
  unfold Apart at hga
  have hext : LiveExt R L (L ++ [(ptr, ptr + round)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hpo := outside_of_inRanges hout hIn
  have hgM : Outside ((s.regs 28).toNat + 16) 8 (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
      (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]) := by
    rw [outside_append]; refine ⟨hgr, ?_⟩
    simp only [outside_cons, outside_nil, and_true]; omega
  have hcw : ∀ a n, (s.sp.toNat - 168 ≤ a ∧ a + n ≤ s.sp.toNat - 152) →
      Outside a n (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
        (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩
  have hFo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n (winA s 4304 80) := by
    intro a n h; simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hCo : ∀ a n, (a + n ≤ s.sp.toNat - 4304 ∨ s.sp.toNat + 80 ≤ a) → Outside a n
      [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8), (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)] := by
    intro a n h; simp only [outside_cons, outside_nil, and_true]; omega
  have hxk : ∀ a n, xp.toNat ≤ a → a + n ≤ xp.toNat + 8 * xl.toNat → m.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    rw [held_keep (hxh.sub h1 h2) hLF hMF (hCo _ _ (by omega)), hF.readLE _ _ (hFo _ _ (by omega))]
  have hmo : ∀ a n, Outside a n (R.rt ++ winA s 4304 80 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) →
      Outside a n (R.rt ++ [(s.sp.toNat - 160 - 4096, s.sp.toNat - 160 - 8),
        (s.sp.toNat - 160 + 8, s.sp.toNat - 160 + 8 + 24)]) := by
    intro a n h
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.1.1, by omega, by omega⟩
  exact {
    gok := hg3, g48 := hg1, al := hal, sp0 := hb', sp1 := ha, wrt := hout, gw := by unfold Apart; omega, grt := hgr,
    lr4 := hl4, lr48 := hl48, xl40 := hx40, x0 := hx0,
    lr := by rw [hMF.readLE _ _ (hcw _ _ (by omega))]; exact r1,
    fp := by rw [hMF.readLE _ _ (hcw _ _ (by omega))]; exact r2,
    sacc := by rw [hMF.accessible, hF.accessible]; exact hw,
    gacc := by rw [hMF.accessible, hF.accessible]; exact hg2,
    grd := by rw [hMF.readLE _ _ hgM]; exact hF.readLE _ _ (hFo _ _ (by omega)),
    cap := hc1, c41 := by omega, p8 := h8, p48 := by omega,
    pacc := Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    pw := by unfold Apart; omega,
    pheld := Or.inl ⟨(ptr, ptr + round), by simp, Nat.le_refl _, by simp only; omega⟩,
    px := Or.inr ((held_apart_fresh hxh hAp hIn).mono hsz (Nat.le_refl _)),
    xacc := by rw [hMF.accessible, hF.accessible]; exact hxacc, x48 := hx48, xw := by unfold Apart; omega,
    xv := hxk _ _ (Nat.le_refl _) (Nat.le_refl _),
    xn := by
      rw [hxk _ _ (by omega) (by omega)]
      rcases hxn with h0 | h0
      · omega
      · exact h0,
    ext := hext, bud := by omega, inv := hinv,
    lsep := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hLs r hr
      · simp only [List.mem_singleton] at hr; subst hr
        simp only [win, outside_cons, outside_nil, and_true]; omega,
    ror := Or.inr ⟨hIn.sub (Nat.le_refl _) (by omega), fun r hr => (hAp r hr).mono hsz (Nat.le_refl _)⟩,
    mf := (hF.mono fun a n h => by simp only [outside_append] at h; exact h.1.2).trans hMF fun a n h => ⟨h, hmo a n h⟩,
    lf := by
      refine ⟨fun a n hin hz => ?_⟩
      rw [hLF.readLE a n hin trivial]
      refine hF.readLE a n ?_
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this
      simp only [winA, outside_cons, outside_nil, and_true]; omega,
    mv := fun d src k hk => hmv d src k (by unfold mx; omega) }

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem setTail (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibNatAdd.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : SetMid R b L zp zc xp xl s p c L' b' M) (hy0 : yl.toNat = 0)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hSet) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = xl) (h2 : S.regs 2 = BitVec.ofNat 64 c) (h3 : S.regs 3 = xp) (h4 : S.regs 4 = xl)
    (hsp : S.sp = s.sp - 160#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 168#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M) :
    ReachesRet (LibNatAdd.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        PostS 4304 R b L zp zc xp xl yp yl s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc41 := h.c41; have hp48 := h.p48
  have hxl := h.xl40; have hx0 := h.x0; have hx48 := h.x48
  have r1 := h.lr; have r2 := h.fp; have hsacc := h.sacc; have hal := h.al; have hinv := h.inv
  have hpacc : M.accessible p (8 * xl.toNat) true = true := Memory.accessible_mono _ h.pacc (Nat.le_refl _) (by omega)
  have hxacc := h.xacc; have hl4 := h.lr4; have hl48 := h.lr48; have hwrt := h.wrt
  have hpw := h.pw; have hxw := h.xw; have hgw := h.gw
  unfold Apart at hpw hxw hgw
  have hph : Held R L' p (8 * xl.toNat) := h.pheld.sub (Nat.le_refl _) (by omega)
  have hLs := h.lsep
  simp only [LiveSep, win] at hLs
  have hmv1 : ∀ d src, R.ok (cA "runtime.memmove") [d, src, 8 * xl.toNat] := fun d src => h.mv d src _ (Nat.le_refl _)
  have hg48 : (s.regs 28).toNat ≤ 281474976710632 := by have := h.g48; omega
  have hgacc := h.gacc
  have hgok : M.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 160 := by rw [h.grd]; have := h.gok; omega
  have hph' : InRanges p (8 * xl.toNat) L' ∨ Outside p (8 * xl.toNat) R.rt := hph
  janus_run [hm, r1, r2, Nat.mod_eq_of_lt (by omega : c < 18446744073709551616)] calls [hmv]
  · -- `p = xp`: no copy
    rename_i hpx _
    refine h.post hy0 (MemFrame.refl _ _) ⟨fun _ _ _ _ => rfl⟩ h.inv (by rw [hpx]) (by rw [hpx]) _ rfl ?_ ?_ ?_
    all_goals janus_simp
  · rename_i _ _ _ _ m _ _ hF2 hLF2 hinv2 hcp _
    have hcp' := Asm.readLE_of_copied hcp
    have hsub : Mem.Copied _ m (p + 8 * (xl.toNat - 1)) (xp.toNat + 8 * (xl.toNat - 1)) 8 := fun i hi => by
      have := hcp (8 * (xl.toNat - 1) + i) (by omega)
      rw [← Nat.add_assoc, ← Nat.add_assoc] at this; exact this
    have hnz' := Asm.readLE_of_copied hsub
    have hW : MemFrame M (((M.writeLE (s.sp.toNat - 40) 8 c).writeLE (s.sp.toNat - 48) 8 xl.toNat).writeLE
        (s.sp.toNat - 16) 8 p) [(s.sp.toNat - 48, s.sp.toNat - 32), (s.sp.toNat - 16, s.sp.toNat - 8)] := by
      janus_frame
    have rdW : ∀ a n, (a + n ≤ s.sp.toNat - 48 ∨ s.sp.toNat - 8 ≤ a) →
        (((M.writeLE (s.sp.toNat - 40) 8 c).writeLE (s.sp.toNat - 48) 8 xl.toNat).writeLE
          (s.sp.toNat - 16) 8 p).readLE a n = M.readLE a n := fun a n h' =>
      hW.readLE a n (by simp only [outside_cons, outside_nil, and_true]; omega)
    refine h.post hy0 (hW.trans hF2 fun a n ho => ?_) ⟨fun a n hin ho => ?_⟩ hinv2 ?_ ?_ _ rfl ?_ ?_ ?_
    · simp only [outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨hr, h1', h2'⟩ := ho
      and_intros <;> first | exact hr | omega
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      have := hLs q hq
      simp only [outside_cons, outside_nil, and_true] at this
      rw [hLF2.readLE a n ⟨q, hq, hq1, hq2⟩ ho, rdW a n (by omega)]
    · rw [hcp', rdW _ _ (by omega)]
    · rw [hnz', rdW _ _ (by omega)]
    all_goals janus_simp

end FvModexp.Arm64.NatAdd
