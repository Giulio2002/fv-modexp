import FvModexp.Proofs.Arm64.Exp.IExpPost
import FvModexp.Proofs.Arm64.Exp.IExpB
import FvModexp.Proofs.Arm64.Exp.IExpC
import FvModexp.Proofs.Arm64.Exp.IExpL

/-!
# `(*Int).exp` (arm64): `z.exp(z, y, m, false)` returns `z = z^y mod m` (`RunIface.ExpSpec`, local form `ExpSpecX`)

Composition: segment A (entry → alias test), B (alias test → join), C (→ `nat.expNN`'s entry; its precondition by
`preNF_of`), the call of `nat.expNN` (`ExpN.ensNilF` on `LibNE`, a `Summary` of `LibExp`), `atN_of` at its return,
segment D (header stores, write barrier, `RET`) and `post_of`.

`ExpSpecX` = `RunIface.ExpSpec` with the precondition's extra conjunct `ExpX` (top's FINAL `PoolG` + `IntOK` cap bound,
`m ≠ nil`, `z`'s header apart from the write-barrier flag) and the result's cap bound in the post (`IntOK`'s new
conjunct) — the mechanical switch to top's text when `RunIface` has it.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Pool Janus.Contracts Janus.Contracts.Pool FvModexp

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace FvModexp.Arm64.IExp

open FvModexp.Arm64.RunIface (IntPre IntPost IntV IntLenLe OneG maxW ExpBudget lenW)

/-- `RunIface.ExpSpec` with `ExpX` in the pre and the result's cap bound in the post (see the module doc) -/
def ExpSpecX (impl : List Segment) (R : RtInv) (stk above : Nat) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (z y mm : BitVec 64),
    Ensures ((Extracted.program.onlySegments RunIface.namesExp).link impl)
      (segAddr Extracted.program (RunIface.P ++ "(*Int).exp")) [z, z, y, mm, 0#64]
      (fun s => IntPre R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above [z.toNat, y.toNat, mm.toNat] s ∧ 0 < IntV s.mem mm.toNat ∧
        IntLenLe s.mem z.toNat maxW ∧ IntLenLe s.mem y.toNat maxW ∧ IntLenLe s.mem mm.toNat maxW ∧
        OneG R L s.mem (win s stk above) [z.toNat, y.toNat, mm.toNat] ∧
        ExpX R s.mem (win s stk above) z.toNat y.toNat mm.toNat)
      (fun s s' => s'.regs 0 = z ∧
        IntPost R b (ExpBudget (max (max (lenW s.mem z.toNat) (lenW s.mem y.toNat)) (lenW s.mem mm.toNat))
          (lenW s.mem y.toNat)) L stk above z.toNat (IntV s.mem z.toNat ^ IntV s.mem y.toNat % IntV s.mem mm.toNat) s s' ∧
        s'.mem.readLE (z.toNat + 24) 8 < 2 ^ 40)

/-- the return address of the `expNN` call (fn+0x2dc, in `(*Int).exp`'s segment) is outside `LibNE` -/
theorem raN_ret (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    RetAddr ((Extracted.program.onlySegments ExpN.LibNE.names).link impl) raN :=
  CallW.retAddr_restrict hap (cs := Extracted.seg5)
    (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 183
    (by decide) (by decide) (by decide)

theorem log2_lt64 {m : Memory} {p n : Nat} (hn : 0 < n) : Nat.log2 (natVal m p n) < 64 * n := by
  rcases Nat.eq_zero_or_pos (natVal m p n) with h | h
  · rw [h]; simp only [Nat.log2_zero]; omega
  · refine (Nat.log2_lt (by omega)).2 ?_
    have := Memory.readLE_lt m p (8 * n)
    simp only [natVal]
    calc m.readLE p (8 * n) < 256 ^ (8 * n) := this
      _ = 2 ^ (64 * n) := by rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`(*Int).exp`** (arm64) as `Run` calls it: `z.exp(z, y, m, false)` returns `z` with `z = z^y mod m`
(`ExpSpecX`). Premises: `nat.expNN`'s callees (`DHyps`: division, slow / power-of-two paths, runtime contracts;
`hEv`: `nat.expNNEven`; `hRem`: `nat.rem`; the pool / `newobject` contracts), the write barrier, the stack sizes
(`expNN`'s `K + 1632 ≤ stk`, the barrier's 4096 bytes below `(*Int).exp`'s frame) and the callees' needs and
costs within `RunIface.ExpBudget` for operands of at most 128 words (`hneed`, `hbud`). -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    {K : Nat} {costF : Nat → Nat → Nat → Nat} {needR : Nat → Nat → Nat} {costR : Nat → Nat → Nat → Nat}
    {needS needP : Nat → Nat → Nat → Nat} {costS costP : Nat → Nat → Nat → Nat → Nat}
    {nsD : List String} {stkD : Nat} {nsS : List String} {stkS : Nat} {nsP : List String} {stkP : Nat}
    (H : ExpN.DHyps impl R K costF needS needP costS costP nsD stkD nsS stkS nsP stkP)
    {stkE : Nat} {needE : Nat → Nat → Nat → Nat} {costE : Nat → Nat → Nat → Nat → Nat}
    (hEv : ExpEven.EvenSum impl R stkE 112 needE costE) (hstkE : stkE ≤ K + 1056)
    (hget : PoolGetLive (ExpN.LibNE.program.link impl) ExpN.getA 4096 R Free.stkT StkSh)
    (hno : NewobjectLiveContract (ExpN.LibNE.program.link impl) ExpN.noA 4096 R)
    (hput : PoolPutLive (LibFree.program.link impl) (cA "sync.(*Pool).Put") 4096 R Free.stkT StkSh)
    {nsR : List String} {stkR : Nat} (hRem : NHyp.RemHyp impl R nsR stkR 112 needR costR)
    (hnsR : ∀ x, nsR.contains x = true → LibN.names.contains x = true)
    (hn11R : nsR.contains Extracted.seg11.name = false) (hKR : stkR ≤ K + 1056)
    (hwb : WbLiveContract (LibExp.program.link impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {stk above : Nat} (hK : K + 1632 ≤ stk) (hK4 : 4304 ≤ K) (hK20 : K + 288 ≤ 2 ^ 20) (h4416 : 4416 ≤ stk)
    (hab : 48 ≤ above)
    (hneed : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      needR xl n ≤ 2 ^ 16 ∧ ExpN.addN needS needE xl yl n ≤ 2 ^ 16 ∧ needP xl yl lm ≤ 2 ^ 16)
    (hbud : ∀ xl yl n lm, xl ≤ 128 → yl ≤ 128 → 0 < n → n ≤ 128 → lm < 64 * n →
      24 + (makeCost 1 + makeCost n + costR 0 xl n + ExpN.addC costS costE 0 xl yl n + costP 0 xl yl lm +
        ExpOdd.OBud costF n xl yl 0) ≤ ExpBudget (max (max xl yl) n) yl ∧
      24 + ExpN.NCost costF costR (ExpN.addC costS costE) costP xl yl n 0 lm ≤ ExpBudget (max (max xl yl) n) yl) :
    ExpSpecX impl R stk above := by
  intro b L z y mm
  rw [namesExp_eq, ← LibExp.eq_only, show segAddr Extracted.program (RunIface.P ++ "(*Int).exp") = fnI by decide]
  intro ret hret s hs hpre
  janus_intro hs
  have hr48 := hret.user
  obtain ⟨hIP, hm0, hlz, hly, hlm, hone, hx⟩ := hpre
  have hIP' := hIP
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hstk, hab48, hacc⟩, -, hrt, -, -, -, -⟩, hsv, hG, -, -, hops, hpw⟩ := hIP'
  have hoz := hops z.toNat (by simp)
  have hoy := hops y.toNat (by simp)
  have hom := hops mm.toNat (by simp)
  clear hops
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hpw
  obtain ⟨⟨⟨hzym, -, -, -⟩, ⟨hzmA, -, -, hzmArr⟩⟩, -⟩ := hpw
  obtain ⟨⟨-, -, hz48, hzacc, -, hzL, -, -, -⟩, hzW, -, -, -⟩ := hoz
  obtain ⟨⟨hy0, -, hy48, hyacc, -, -, -, -, -⟩, hyW, -, -, -⟩ := hoy
  obtain ⟨⟨-, -, hm48, hmacc, -, hmL, -, -, -⟩, -, -, -, -⟩ := hom
  have hx' := hx
  obtain ⟨-, -, -, -, hmA0, hwbz⟩ := hx'
  generalize hzp : s.mem.readLE (z.toNat + 8) 8 = zp at *
  generalize hzl : s.mem.readLE (z.toNat + 16) 8 = zl at *
  generalize hzc : s.mem.readLE (z.toNat + 24) 8 = zc at *
  generalize hyp : s.mem.readLE (y.toNat + 8) 8 = yp at *
  generalize hyl : s.mem.readLE (y.toNat + 16) 8 = yl at *
  generalize hyc : s.mem.readLE (y.toNat + 24) 8 = yc at *
  generalize hmp : s.mem.readLE (mm.toNat + 8) 8 = mp at *
  generalize hmn : s.mem.readLE (mm.toNat + 16) 8 = n at *
  generalize hmc : s.mem.readLE (mm.toNat + 24) 8 = mc at *
  sorry

end FvModexp.Arm64.IExp
