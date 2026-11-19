import FvModexp.Proofs.Amd64.SetRetLemmas
import FvModexp.Proofs.Amd64.Exp.RemInst
import FvModexp.Proofs.Common.NCostU

set_option autoImplicit false

/-!
# `nat.expNNSlow` (amd64), Q-form (TIGHT COSTS) export statement and its level-cost bridge (agent expmc s78; twin of
Arm64/ExpQ/SlowQStmt.lean + `Arm64/ExpQ/Bridge.slow_of_Q`)

* `Q.ExpSlow.costQ sqC mlC dvC xl yl ml` — level-free: `z.set(x)`'s `makeslice` + `64 · yl` rounds, each bounded by
  the box maxima of the level-free callee costs over the lengths the loop sees (`len z ≤ M` at `sqr`, `≤ 2M` at `mul`,
  `≤ 3M` at `div`, `M = max (len x) (len m)`) — the arm64 definition verbatim.
* `Q.ExpSlow.needH xl ml = 48 · max xl ml + 64` — the level twin (every callee's level bound at the loop's constant
  stack length is `≤ stLen + needH`).
* `NHyp.SlowHypQ … need needH cost`: amd64 `NHyp.SlowHyp`'s pre with the interface cost `cost xl yl ml + stkR H s.mem st`
  and the LAST conjunct `stLen s.mem st + needH xl ml ≤ H`; post `CPostR0Q` (= `CPostR0` with `RtPostQ`).
* `Q.ExpSlow.slow_of_Q : SlowHypQ … need needH C → SlowHyp … need (slowBr C needH)` (`H := stLen + needH` per call,
  `RemInst.ens_param`): the reserve is paid once per `expNNSlow` call at `nat.expNN`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.Q.ExpSlow

/-- the level-free budget of `nat.expNNSlow` (see the module doc) -/
def costQ (sqC : Nat → Nat) (mlC dvC : Nat → Nat → Nat) (xl yl ml : Nat) : Nat :=
  makeCost xl + 64 * yl * (Exp.supN sqC (max xl ml) + Exp.supN (fun n => mlC n xl) (2 * max xl ml) +
    Exp.supN (fun n => dvC n ml) (3 * max xl ml))

/-- the level twin of `nat.expNNSlow` (see the module doc) -/
@[reducible] def needH (xl ml : Nat) : Nat := 48 * max xl ml + 64

/-- the bridged cost of `nat.expNNSlow` -/
@[reducible] def slowBr (C : Nat → Nat → Nat → Nat) (nH : Nat → Nat → Nat) (l xl yl ml : Nat) : Nat :=
  C xl yl ml + stkRes (l + nH xl ml)

end FvModexp.Amd64.Q.ExpSlow

namespace FvModexp.Amd64.NHyp

open FvModexp.Amd64.ExpHyp

/-- `CPostR0` in the Q-form (`c` the interface cost, `r'` the reserve after the call) -/
@[reducible] def CPostR0Q (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (stk above zp zc st v c r' : Nat)
    (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ p l cp : Nat, s'.regs 0 = BitVec.ofNat 64 p ∧ s'.regs 3 = BitVec.ofNat 64 l ∧ s'.regs 1 = BitVec.ofNat 64 cp ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), NatOF0 R L L' s'.mem zp zc p l cp v ∧ RtPostQ R b c r' L L' b' s s' ∧
      StackBackL R L L' st s.mem s'.mem ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk above ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
      LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧ ResSep s.mem s'.mem st p cp

/-- **`nat.expNNSlow`, Q-form** (twin of `SlowHyp`; `cost` level-free, e.g. `Q.ExpSlow.costQ sqrCQ mulCQ
(Q.NatDiv.costQ Q.drsCQ)`; `needH` the level twin, the LAST pre conjunct) -/
def SlowHypQ (impl : List Amd64.Segment) (R : RtInv) (ns : List String) (stk above : Nat)
    (need : Nat → Nat → Nat → Nat) (needH : Nat → Nat → Nat) (cost : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (H b : Nat) (L : List (Nat × Nat)) (z zl zc st x xl xc : BitVec 64) (y yl yc m ml mc : Nat),
    Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program fnSlow)
      [z, zl, zc, st, x, xl, xc]
      (fun s => (StkArg s 0 y yl yc ∧ StkArg s 24 m ml mc) ∧
        (CPre R b L stk above z.toNat zl.toNat zc.toNat st.toNat [(x.toNat, xl.toNat), (y, yl), (m, ml)]
          (need xl.toNat yl ml) (cost xl.toNat yl ml + stkR H s.mem st.toNat) s ∧
        0 < natVal s.mem x.toNat xl.toNat ∧ 2 ≤ natVal s.mem y yl ∧ 0 < natVal s.mem m ml ∧
        0 < st.toNat) ∧ XFacts R L x.toNat xl.toNat xc.toNat ∧ stLen s.mem st.toNat + needH xl.toNat ml ≤ H)
      (fun s s' => CPostR0Q R b L stk above z.toNat zc.toNat st.toNat
        (natVal s.mem x.toNat xl.toNat ^ natVal s.mem y yl % natVal s.mem m ml)
        (cost xl.toNat yl ml + stkR H s.mem st.toNat) (stkR H s'.mem st.toNat) s s')

end FvModexp.Amd64.NHyp

namespace FvModexp.Amd64.Q.ExpSlow

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`nat.expNNSlow`**: `SlowHypQ` gives `SlowHyp` at the cost `C xl yl ml + stkRes (ℓ + needH xl ml)` -/
theorem slow_of_Q {impl : List Amd64.Segment} {R : RtInv} {ns : List String} {stk above : Nat}
    {need : Nat → Nat → Nat → Nat} {nH : Nat → Nat → Nat} {C : Nat → Nat → Nat → Nat}
    (h : NHyp.SlowHypQ impl R ns stk above need nH C) (hab : 8 ≤ above := by omega) : NHyp.SlowHyp impl R ns stk above need (slowBr C nH) := by
  intro b L z zl zc st x xl xc y yl yc m ml mc
  refine RemInst.ens_param (fun H => h H b L z zl zc st x xl xc y yl yc m ml mc)
    (fun s => stLen s.mem st.toNat + nH xl.toNat ml) (fun s hp => ?_) (fun s s' hq => ?_) (hinv := by
      intro s ret hs hret hp
      have hslot : Outside (s.regs 4).toNat 8 R.rt := CallEnv.slot hp.2.1.1.1 hab
      simp only [NHyp.StkArg, NHyp.CPre, NHyp.XFacts, forall_mem_pair3] at hp ⊢
      by_cases h2 : 0 < zc.toNat <;> by_cases h3 : 0 < stCap s.mem st.toNat <;>
      janus64_pre_setRet_core s ret hs hret hp [FvModexp.Amd64.CallEnv, FvModexp.Amd64.RunIface.Globals, FvModexp.Amd64.win, FvModexp.Amd64.StackNat.wT, FvModexp.Amd64.EvenHyp.WrOut, FvModexp.Amd64.EvenHyp.RdIn, FvModexp.Amd64.NHyp.freeOf, FvModexp.Amd64.ExpHyp.StackOK', FvModexp.stCap, FvModexp.stW, FvModexp.stLen, FvModexp.Amd64.StackNat.wbA, FvModexp.Amd64.RunIface.gA, FvModexp.Amd64.Callees.adxAddr, FvModexp.Amd64.TlsOK, FvModexp.Amd64.RunIface.wbA, FvModexp.NatLive, FvModexp.StkOK, FvModexp.natVal, FvModexp.Amd64.readLE_setRet_or_zero, FvModexp.Amd64.natNorm_setRet, h2, h3, false_implies, true_implies])
  · obtain ⟨hy, ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, hc, h23, h24, hinv⟩, hX, hY, hM, hS⟩, hXF⟩ := hp
    exact ⟨hy, ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, RemInst.cost_br hc, h23, h24, hinv⟩, hX, hY, hM, hS⟩, hXF, Nat.le_refl _⟩
  · obtain ⟨hf, hd, p, l, cp, e0, e1, e2, L', b', hof, ⟨hLE, hb, hinv⟩, hsb, hfr, hl, hrs⟩ := hq
    exact ⟨hf, hd, p, l, cp, e0, e1, e2, L', b', hof, ⟨hLE, RemInst.bud_br (stkR_le _ _ _) hb, hinv⟩, hsb, hfr, hl,
      hrs⟩

end FvModexp.Amd64.Q.ExpSlow
