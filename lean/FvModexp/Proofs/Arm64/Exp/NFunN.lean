import FvModexp.Proofs.Arm64.Exp.NJ1N
import FvModexp.Proofs.Arm64.Exp.NPro

/-!
# `nat.expNN` (arm64), `stk == nil`, modulus odd or a power of two: `ensNil` (CONVENTIONS §3)

`z.expNN(nil, x, y, m, false)` — the call `(*Int).exp` makes (int.go `z.abs = z.abs.expNN(nil, x, y, m, false)`) —
returns `x^y mod m` (see `PreN`/`PostN`): the prologue and alias test (`pro`), then `fromJ1N`.
Premises: the callee shapes (as `ens_noEven`) and the pool / allocation contracts (`Get`, `newobject`, `Put`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false

namespace FvModexp.Arm64.ExpN

/-- the precondition, `stk == nil` (entry state `s`; arguments `[z, zl, zc, st, x, xl, xc, y, yl, yc, m, n, mc, slow]`) -/
def PreN (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (needR : Nat → Nat → Nat) (costR : Nat → Nat → Nat → Nat) (needS needP : Nat → Nat → Nat → Nat)
    (costS costP : Nat → Nat → Nat → Nat → Nat)
    (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) (s : State) : Prop :=
  PreNil R b L K costF needR costR needS needP costS costP (s.regs 28).toNat (s.sp.toNat - 1312) zp zl zc st xp xl xc
    yp yl yc mp n mc slow s ∧
  (natVal s.mem mp n % 2 = 1 ∨ ∃ k, natVal s.mem mp n = 2 ^ k)

/-- the postcondition, `stk == nil` (results `X0..X2`): ABI return and `PostNil` -/
def PostN (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costR : Nat → Nat → Nat → Nat) (costS costP : Nat → Nat → Nat → Nat → Nat)
    (zp zc xp xl yp yl mp n : Nat) (s s' : State) : Prop :=
  PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNN`** (arm64), `stk == nil` (`st = 0`), `slow = false`, `m` odd or a power of two:
`z.expNN(nil, x, y, m, false)` returns `x^y mod m` (see `PreN`/`PostN`); the stack comes from `stackPool` (`Get`) or
`newobject` and is given back by the deferred `Put` -/
theorem ensNil (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    (hget : PoolGetLive (LibN.program.link impl) getA 4096 R Free.stkT StkSh)
    (hno : NewobjectLiveContract (LibN.program.link impl) noA 4096 R)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true)
    (hn11R : nsR.contains Extracted.seg11.name = false) (hKR : stkR ≤ K + 1056)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) :
    Ensures ((Extracted.program.onlySegments names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 yl, BitVec.ofNat 64 yc,
        BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc, BitVec.ofNat 64 slow]
      (PreN R b L K costF needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow)
      (PostN R b L K costF costR costS costP zp zc xp xl yp yl mp n) := by
  rw [show names = LibN.names from rfl, ← LibN.eq_only, show segAddr Extracted.program fn = fnN by decide]
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨hP, hev⟩ := hpre
  have hevB : NoEvenB s.mem mp n := hev
  clear hev
  have hP' := hP
  obtain ⟨⟨hs1, hs28, hg1, hg2, hg3, -, hal, hK4, hKs, hsp2, hacc, -, -, -, -⟩, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, hy48, hyc, -, -, -, -, -, hxp, hxc, hzp, hzlc, hzc, -, hali, -⟩ := hP'
  generalize hspd : s.sp.toNat - 1312 = sp at hP hs1 hg3 hal hKs hsp2 hacc hali
  generalize hgd : (s.regs 28).toNat = g at hP hs28 hg1 hg2 hg3 hali
  have hr48 := hret.user
  refine returns_of_reaches (pro impl ret hret _ sp g ret zp zc xp xc yp yc (s.regs 29) s.mem hal (by omega) hsp2
    (Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) hr48 hzp (by omega) hxp hxc
    (by omega) hyc.1 s h_pc hs1 h_x0 h_x2 h_x4 h_x6 h_x7 h_x9 hs28 rfl h_lr rfl ?Kk ?K0)
  case Kk =>
    intro hk S M c1 c2 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d18 d28 cm hF hrg q29 q30 _ _
    refine fromJ1N impl hap R H hget hno hput hRem hnsR hn11R hKR ret hret (fun s' => ABIReturn s s' ∧ PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s') hP hevB (zp' := zp) (zl' := zl) (zc' := zc)
      (Or.inl ⟨rfl, rfl, rfl, zok_of_keep hali hk⟩) (noAlias_keep hk) S M c1 c2 (d0.trans h_x0) (d1.trans h_x1) (d2.trans h_x2)
      (d3.trans h_x3) (d4.trans h_x4) (d5.trans h_x5) (d6.trans h_x6) (d7.trans h_x7) (d8.trans h_x8)
      (d9.trans h_x9) (d10.trans h_x10) (d11.trans h_x11) (d12.trans h_x12) (d13.trans h_x13) d28 cm hF hrg q29 q30
      fun s'' a1 a2 a3 a4 hq => ⟨⟨a1.trans hs1.symm, a4.trans (d28.trans rfl), a2.trans (Expmc.bv_ofNat_toNat _),
        a3.trans d18⟩, hq⟩
  case K0 =>
    intro hz0 hk S M c1 c2 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d18 d28 cm hF hrg q29 q30 _ _
    refine fromJ1N impl hap R H hget hno hput hRem hnsR hn11R hKR ret hret (fun s' => ABIReturn s s' ∧ PostNil R b L K costF costR costS costP zp zc xp xl yp yl mp n s s') hP hevB (zp' := 0) (zl' := 0) (zc' := 0)
      (Or.inr ⟨rfl, rfl, rfl⟩) (noAlias_nil _ _) S M c1 c2 d0 d1 d2 (d3.trans h_x3) (d4.trans h_x4) (d5.trans h_x5) (d6.trans h_x6)
      (d7.trans h_x7) (d8.trans h_x8) (d9.trans h_x9) (d10.trans h_x10) (d11.trans h_x11) (d12.trans h_x12)
      (d13.trans h_x13) d28 cm hF hrg q29 q30
      fun s'' a1 a2 a3 a4 hq => ⟨⟨a1.trans hs1.symm, a4.trans (d28.trans rfl), a2.trans (Expmc.bv_ofNat_toNat _),
        a3.trans d18⟩, hq⟩

end FvModexp.Arm64.ExpN
