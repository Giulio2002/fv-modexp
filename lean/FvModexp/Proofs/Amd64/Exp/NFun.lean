import FvModexp.Proofs.Amd64.Exp.NJ1
import FvModexp.Proofs.Amd64.Exp.NPro

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), stack given, modulus odd or a power of two: `ens_noEven` (agent expmc s72; twin of
`Arm64.ExpN.ens_noEven`, CONVENTIONS §3)

`z.expNN(stk, x, y, m, false)` returns `x^y mod m` (see `ExpN.Pre`/`Post`): the prologue and alias test (`pro`), then
`fromJ1` (`z[:0]` / `setWord(1)` / `rem` / `make` → `expNNSlow` | `expNNOdd` | `expNNPowerOfTwo`).
Premises: the callee shapes (`DHyps`: live runtime contracts, `nat.div`'s `DivHypL`, `SlowHyp`, `P2Hyp`; `RemHyp`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- `z` kept by the alias test (`pro`'s `Kk`; `lastA p c = (p + 8 (c - 1)) % 2^64`) ⇒ the third disjunct of
`NPre`'s alias clause (`ZOK`) -/
theorem zok_of_keep {P : Prop} {zp zc xp xc yp yc : Nat}
    (hal : 0 < zc → (0 < xc ∧ zp + 8 * zc = xp + 8 * xc) ∨ (0 < yc ∧ zp + 8 * zc = yp + 8 * yc) ∨ P)
    (hk : zc = 0 ∨ ((xc = 0 ∨ lastA xp xc ≠ lastA zp zc) ∧ (yc = 0 ∨ lastA yp yc ≠ lastA zp zc))) :
    0 < zc → P := by
  intro hz
  rcases hal hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
  · exfalso
    rcases hk with h | ⟨h3 | h3, -⟩
    · omega
    · omega
    · exact h3 (by unfold lastA; congr 1; omega)
  · exfalso
    rcases hk with h | ⟨-, h3 | h3⟩
    · omega
    · omega
    · exact h3 (by unfold lastA; congr 1; omega)
  · exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNN`** (amd64), `stk ≠ nil`, `slow = false`, `m` odd or a power of two: `z.expNN(stk, x, y, m, false)`
returns `x^y mod m` (see `Pre`/`Post`) -/
theorem ens_noEven (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true) (hnfR : nsR.contains fn = false)
    (hKR : stkR ≤ K + 0x388)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 slow]
      (Pre R b L K costF costD needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow)
      (Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n) := by
  janus64_ensures_old [FvModexp.Amd64.ExpN.Pre, FvModexp.Amd64.ExpN.NPre, FvModexp.natVal, FvModexp.Amd64.ExpN.NEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.StackNat.wT, FvModexp.Amd64.W4En.wTy, FvModexp.Amd64.MontHyp.hasADX, FvModexp.Amd64.ExpN.NE, FvModexp.NatNorm, FvModexp.Amd64.ExpN.ZOK, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.EvenHyp.NatOne, FvModexp.Amd64.ExpHyp.stWs, FvModexp.Amd64.NHyp.StkApart, FvModexp.StkOK, FvModexp.stCap, FvModexp.stW, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.W4En.free, FvModexp.stLen, FvModexp.Amd64.ExpN.XG, FvModexp.Amd64.CallW.CEnv, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.Amd64.EvenHyp.natOneA, FvModexp.stkWs, FvModexp.Amd64.Callees.adxAddr]
  rw [show names = LibN.names from rfl, ← LibN.eq_only, show segAddr Extracted.program fn = fnN by decide]
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hP, hev, hX⟩ := hpre
  have hevB : NoEvenB s.mem mp n := hev
  clear hev
  generalize hspd : (s.regs 4).toNat - 0x498 = sp at hP
  generalize hgd : (s.regs 14).toNat = g at hP
  generalize hfsd : s.fsBase.toNat = fs at hP
  have hP' := hP
  obtain ⟨⟨hs4, hs14, -, -, -, hK1, -, hce, -⟩, -, -, -, -, -, hry, -, hryc, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hyc, -, -, hx48, -, -, -, hxc, hzp, -, hzc, ⟨hal, -⟩, -⟩ := hP'
  obtain ⟨-, hK0, hA0, hacc, hg1, hg2, hg3, -⟩ := hce
  have hs : (s.regs 4).toNat = sp + 0x498 := by rw [hs4, BitVec.toNat_ofNat]; omega
  have hr48 := hret.user
  refine returns_of_reaches (pro impl ret hret _ (sp + 0x498) g zp zc xp xc yp yc s.mem (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by rw [show sp + 0x498 + 8 = sp + 0x4a0 by omega]; exact hry)
    (by rw [show sp + 0x498 + 0x18 = sp + 0x4b0 by omega]; exact hryc)
    s h_rip hs4 h_a0 h_a2 h_a4 h_a6 hs14 h_x15 rfl ?Kk ?K0)
  case Kk =>
    intro hk S M c_rip c4 c0 c3 c1 c7 c6 c8 c9 c10 c2 c12 c5 c14 cfs cdf cx15 cm hF hrg q_bp q38 q58 q10 q99
    refine fromJ1 impl hap R H hRem hnsR hnfR hKR ret hret (fun s' => ABIReturn s s' ∧
        Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s s') hP hX hevB (zp' := zp) (zl' := zl)
      (zc' := zc) (Or.inl ⟨rfl, rfl, rfl, zok_of_keep hal hk⟩) (noAlias_keep hk) S M c_rip
      (c4.trans (congrArg _ (by omega))) (c0.trans h_a0) (c3.trans h_a1) (c1.trans h_a2) (c7.trans h_a3)
      (c6.trans h_a4) (c8.trans h_a5) (c9.trans h_a6) (c10.trans h_a7) c2 c12 c14 cfs cdf (cx15.trans h_x15) cm
      (hF.mono fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega) hrg
      (by rw [show sp + 0x490 = sp + 0x498 - 8 by omega, q_bp]) (by
        rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), ← hs]; exact h_ret)
      fun s'' a4 a5 a14 ax hq => ⟨⟨ExpOdd.add8 hs a4 (by omega), a5.trans (ExpOdd.ofNat_self _), a14.trans c14,
        ax.trans h_x15.symm⟩, hq⟩
  case K0 =>
    intro hz0 hk S M c_rip c4 c0 c3 c1 c7 c6 c8 c9 c10 c2 c12 c5 c14 cfs cdf cx15 cm hF hrg q_bp q38 q58 q10 q99
    refine fromJ1 impl hap R H hRem hnsR hnfR hKR ret hret (fun s' => ABIReturn s s' ∧
        Post R b L K costD costR costS costP zp zc st xp xl yp yl mp n s s') hP hX hevB (zp' := 0) (zl' := 0)
      (zc' := 0) (Or.inr ⟨rfl, rfl, rfl⟩) (noAlias_nil _ _) S M c_rip
      (c4.trans (congrArg _ (by omega))) c0 c3 c1 (c7.trans h_a3)
      (c6.trans h_a4) (c8.trans h_a5) (c9.trans h_a6) (c10.trans h_a7) c2 c12 c14 cfs cdf (cx15.trans h_x15) cm
      (hF.mono fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega) hrg
      (by rw [show sp + 0x490 = sp + 0x498 - 8 by omega, q_bp]) (by
        rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), ← hs]; exact h_ret)
      fun s'' a4 a5 a14 ax hq => ⟨⟨ExpOdd.add8 hs a4 (by omega), a5.trans (ExpOdd.ofNat_self _), a14.trans c14,
        ax.trans h_x15.symm⟩, hq⟩

end FvModexp.Amd64.ExpN
