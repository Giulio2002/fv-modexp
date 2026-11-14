import FvModexp.Proofs.Amd64.Exp.NJ1NE
import FvModexp.Proofs.Amd64.Exp.NProE
import FvModexp.Proofs.Amd64.Exp.NFun

set_option autoImplicit false

/-!
# `nat.expNN` (amd64), `stk == nil`, every modulus: `ensNilF` (agent expmc s75; twin of `Arm64.ExpN.ensNilF`)

`z.expNN(nil, x, y, m, false)` (the call `(*Int).exp` makes, `x = z`) returns `x^y mod m` (`PreNF` / `PostNil`,
Amd64/Exp/NNilD.lean): the prologue and alias test (`proE`), then `fromJ1NE` (trivial cases | `Pool.Get` /
`newobject` → the stack-given chain on the new stack → the deferred `stk.free()`). Program: `LibNE` (the recursive pair
`nat.expNN` ↔ `nat.expNNEven`). Premises: the callee shapes (`DHyps`, `RemHyp`, `EvH` for every size: asm's
`ExpEven.EvenSum`), the live `newobject` / `Pool.Get` / `Pool.Put` contracts of the whole program.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts
  Janus.Contracts.Pool Janus.Contracts.PoolAmd64 FvModexp
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.ExpN

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`nat.expNN`** (amd64), `stk == nil`, `slow = false`, every modulus: `z.expNN(nil, x, y, m, false)` returns
`x^y mod m` (see `PreNF` / `PostNil`) -/
theorem ensNilF (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {costD : Nat} {needR : Nat → Nat → Nat}
    {costR : Nat → Nat → Nat → Nat} {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true) (hnfR : nsR.contains fn = false)
    (hKR : stkR ≤ K + 0x388) (hEv : ∀ xl yl n, EvH impl R K needS costS xl yl n)
    (hno0 : NewobjectLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.newobject") 4096 R)
    (hget0 : PoolGetLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh)
    (hput0 : PoolPutLive (Extracted.program.ofImpl impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc st xp xl xc yp yl yc mp n mc slow : Nat) :
    Ensures ((Extracted.program.onlySegments LibNE.names).link impl) (segAddr Extracted.program fn)
      [BitVec.ofNat 64 zp, BitVec.ofNat 64 zl, BitVec.ofNat 64 zc, BitVec.ofNat 64 st, BitVec.ofNat 64 xp,
        BitVec.ofNat 64 xl, BitVec.ofNat 64 xc, BitVec.ofNat 64 slow]
      (PreNF R b L K costF costD needR costR needS needP costS costP zp zl zc st xp xl xc yp yl yc mp n mc slow)
      (fun s s' => PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s') := by
  have hcE : CodeIn64 (Extracted.program.ofImpl impl) (LibNE.program.link impl) := by
    rw [LibNE.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibNE.names
  have hcF : CodeIn64 (Extracted.program.ofImpl impl) (LibFree.program.link impl) := by
    rw [LibFree.eq_only]; exact codeIn_ofImpl_restrict_of_apart64 hap LibFree.names
  have hno := NewobjectLiveContract64.of_codeIn hcE hno0
  have hget : PoolGetLive (LibNE.program.link impl) (cA "sync.(*Pool).Get") 4096 R Free.stkT StkSh :=
    fun L b => Summary.of_codeIn64 hcE (hget0 L b)
  have hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh :=
    fun L b rs => Summary.of_codeIn64 hcF (hput0 L b rs)
  rw [← LibNE.eq_only, show segAddr Extracted.program fn = fnN by decide]
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hP, hX⟩ := hpre
  generalize hspd : (s.regs 4).toNat - 0x498 = sp at hP
  generalize hgd : (s.regs 14).toNat = g at hP
  generalize hfsd : s.fsBase.toNat = fs at hP
  have hP' := hP
  obtain ⟨⟨hs4, hs14, -, -, -, hK1, -, hce, -⟩, -, -, -, -, -, -, hry, -, hryc, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hyc, -, -, -, -, -, -, hxc, hzp, ⟨-, hxz, -, -⟩, hzc, hal, -⟩ := hP'
  obtain ⟨-, hK0, hA0, hacc, hg1, hg2, hg3, -⟩ := hce
  have hs : (s.regs 4).toNat = sp + 0x498 := by rw [hs4, BitVec.toNat_ofNat]; omega
  have hr48 := hret.user
  refine returns_of_reaches (proE impl ret hret _ (sp + 0x498) g zp zc xp xc yp yc s.mem (by omega) (by omega)
    (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hg1 hg2 (by omega) (by omega) (by omega)
    (by subst hxz; omega) (by omega) (by rw [show sp + 0x498 + 8 = sp + 0x4a0 by omega]; exact hry)
    (by rw [show sp + 0x498 + 0x18 = sp + 0x4b0 by omega]; exact hryc)
    s h_rip hs4 h_a0 h_a2 h_a4 h_a6 hs14 h_x15 rfl ?Kk ?K0)
  case Kk =>
    intro hk S M c_rip c4 c0 c3 c1 c7 c6 c8 c9 c10 c2 c12 c5 c14 cfs cdf cx15 cm hF hrg q_bp q38 q58 q10 q99
    refine fromJ1NE impl hap R hput hget hno H hRem hnsR hnfR hKR ret hret (fun s' => ABIReturn s s' ∧
        PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s') hP hX (hEv xl yl n) (zp' := zp)
      (zl' := zl) (zc' := zc) (Or.inl ⟨rfl, rfl, rfl, zok_of_keep hal hk⟩) (noAlias_keep hk) S M c_rip
      (c4.trans (congrArg _ (by omega))) (c0.trans h_a0) (c3.trans h_a1) (c1.trans h_a2) (c7.trans h_a3)
      (c6.trans h_a4) (c8.trans h_a5) (c9.trans h_a6) (c10.trans h_a7) c2 c12 c14 cfs cdf (cx15.trans h_x15) cm
      (hF.mono fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega) hrg
      (by rw [show sp + 0x490 = sp + 0x498 - 8 by omega, q_bp]) (by
        rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), ← hs]; exact h_ret)
      fun s'' a4 a5 a14 ax hq => ⟨⟨ExpOdd.add8 hs a4 (by omega), a5.trans (ExpOdd.ofNat_self _), a14.trans c14,
        ax.trans h_x15.symm⟩, hq⟩
  case K0 =>
    intro hz0 hk S M c_rip c4 c0 c3 c1 c7 c6 c8 c9 c10 c2 c12 c5 c14 cfs cdf cx15 cm hF hrg q_bp q38 q58 q10 q99
    refine fromJ1NE impl hap R hput hget hno H hRem hnsR hnfR hKR ret hret (fun s' => ABIReturn s s' ∧
        PostNil R b L K costD costR costS costP zp zc xp xl yp yl mp n s s') hP hX (hEv xl yl n) (zp' := 0)
      (zl' := 0) (zc' := 0) (Or.inr ⟨rfl, rfl, rfl⟩) (noAlias_nil _ _) S M c_rip
      (c4.trans (congrArg _ (by omega))) c0 c3 c1 (c7.trans h_a3)
      (c6.trans h_a4) (c8.trans h_a5) (c9.trans h_a6) (c10.trans h_a7) c2 c12 c14 cfs cdf (cx15.trans h_x15) cm
      (hF.mono fun a k ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega) hrg
      (by rw [show sp + 0x490 = sp + 0x498 - 8 by omega, q_bp]) (by
        rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), ← hs]; exact h_ret)
      fun s'' a4 a5 a14 ax hq => ⟨⟨ExpOdd.add8 hs a4 (by omega), a5.trans (ExpOdd.ofNat_self _), a14.trans c14,
        ax.trans h_x15.symm⟩, hq⟩

end FvModexp.Amd64.ExpN
