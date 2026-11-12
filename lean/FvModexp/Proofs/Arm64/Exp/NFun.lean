import FvModexp.Proofs.Arm64.Exp.NJ1
import FvModexp.Proofs.Arm64.Exp.NPro

/-!
# `nat.expNN` (arm64), stack given, modulus odd or a power of two: `ens_noEven` (CONVENTIONS §3)

`z.expNN(stk, x, y, m, false)` returns `x^y mod m` (see `ExpN.Pre`/`Post`): the prologue and alias test (`pro`), then
`fromJ1` (`z[:0]` / `setWord(1)` / `rem` / `make` → `expNNSlow` | `expNNOdd` | `expNNPowerOfTwo`).
Premises: the callee shapes (`DHyps`: live runtime contracts, `nat.div`'s `DivHyp`, `SlowHyp`, `P2Hyp`; `RemHyp`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNN`** (arm64), `stk ≠ nil`, `slow = false`, `m` odd or a power of two: `z.expNN(stk, x, y, m, false)`
returns `x^y mod m` (see `Pre`/`Post`) -/
theorem ens_noEven (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true)
    (hn11R : nsR.contains Extracted.seg11.name = false) (hKR : stkR ≤ K + 1056)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc, BitVec.ofNat 64 slow]
      (Pre R b L K costF needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow)
      (Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n) := by
  rw [show names = LibN.names from rfl, ← LibN.eq_only, show segAddr Extracted.program fn = fnN by decide]
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨hP, hev⟩ := hpre
  have hevB : NoEvenB s.mem mp n := hev
  clear hev
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, hg2, hg3, -, hal, hK4, hKs, hsp2, hacc, -, -, -, -⟩, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hy48, -, -, hyc, -, -, -, -, -, hxp, hxc, hzp, hzlc, hzc, hali, -⟩ := hP'
  generalize hspd : s.sp.toNat - 1312 = sp at hP hs1 hg3 hal hKs hsp2 hacc hali
  generalize hgd : (s.regs 28).toNat = g at hP hs28 hg1 hg2 hg3 hali
  have hr48 := hret.user
  refine returns_of_reaches (pro impl ret hret _ sp g ret zp zc xp xc yp yc (s.regs 29) s.mem hal (by omega) hsp2
    (Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) hr48 hzp (by omega) hxp hxc
    (by omega) hyc s h_pc hs1 h_x0 h_x2 h_x4 h_x6 h_x7 h_x9 hs28 rfl h_lr rfl ?Kk ?K0)
  case Kk =>
    intro hk S M c1 c2 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d18 d28 cm hF hrg q29 q30 _ _
    refine fromJ1 impl hap R H hRem hnsR hn11R hKR ret hret (fun s' => ABIReturn s s' ∧ Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s') hP hevB (zp' := zp) (zl' := zl) (zc' := zc)
      (Or.inl ⟨rfl, rfl, rfl, zok_of_keep hali hk⟩) S M c1 c2 (d0.trans h_x0) (d1.trans h_x1) (d2.trans h_x2)
      (d3.trans h_x3) (d4.trans h_x4) (d5.trans h_x5) (d6.trans h_x6) (d7.trans h_x7) (d8.trans h_x8)
      (d9.trans h_x9) (d10.trans h_x10) (d11.trans h_x11) (d12.trans h_x12) (d13.trans h_x13) d28 cm hF hrg q29 q30
      fun s'' a1 a2 a3 a4 hq => ⟨⟨a1.trans hs1.symm, a4.trans (d28.trans rfl), a2.trans (Expmc.bv_ofNat_toNat _),
        a3.trans d18⟩, hq⟩
  case K0 =>
    intro hz0 hk S M c1 c2 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d18 d28 cm hF hrg q29 q30 _ _
    refine fromJ1 impl hap R H hRem hnsR hn11R hKR ret hret (fun s' => ABIReturn s s' ∧ Post R b L K costF costR costS costP zp zc st xp xl yp yl mp n s s') hP hevB (zp' := 0) (zl' := 0) (zc' := 0)
      (Or.inr ⟨rfl, rfl, rfl⟩) S M c1 c2 d0 d1 d2 (d3.trans h_x3) (d4.trans h_x4) (d5.trans h_x5) (d6.trans h_x6)
      (d7.trans h_x7) (d8.trans h_x8) (d9.trans h_x9) (d10.trans h_x10) (d11.trans h_x11) (d12.trans h_x12)
      (d13.trans h_x13) d28 cm hF hrg q29 q30
      fun s'' a1 a2 a3 a4 hq => ⟨⟨a1.trans hs1.symm, a4.trans (d28.trans rfl), a2.trans (Expmc.bv_ofNat_toNat _),
        a3.trans d18⟩, hq⟩

end FvModexp.Arm64.ExpN
