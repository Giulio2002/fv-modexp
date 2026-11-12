import FvModexp.Proofs.Arm64.Exp.LibWC
import FvModexp.Proofs.Arm64.Exp.CallW
import FvModexp.Proofs.Arm64.Exp.W4One

/-!
# window-4 prologue (arm64): the call `buf := stk.nat(17n)` (nat.go:1412), `snE → p01`

`(*stack).nat` is a premise in divmc's proved shape (`StackNat.HypL impl R StackNat.names 4208 24`, discharged by
`StackNat.hyp`); the call is made by hand (`Reaches.call_regions` + `LibWC.hypSum`). The continuation gets the callee's
post in memory form.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.W4Pro

open FvModexp.Arm64.W4Loop (Env Inp Buf)

theorem toNat_lt' {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- the free part of the stack's array -/
@[reducible] def stFree (M : Memory) (st : Nat) : Nat × Nat :=
  (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- a stack-nat call of the window-4 frame: the facts at the call (callee window `[sp-4208, sp+24)`) -/
@[reducible] def SnPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp st k : Nat) (M : Memory) : Prop :=
  CallW.CEnv R L g sp 4304 1040 M ∧ RunIface.Serves R ∧ StkOK M R L st ∧ Apart st 24 (sp - 4304) (4304 + 1040) ∧
  (0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 4304) (4304 + 1040) ∧
    Apart (stW M st) (8 * stCap M st) (g + 16) 8) ∧
  k ≤ 2 ^ 16 ∧ stLen M st + k + 3 ≤ 2 ^ 16 ∧ stackNatCost (stLen M st) k ≤ b ∧ R.inv b L g (view R.rt L M) ∧
  M.accessible StackNat.wbA 4 false = true ∧ Apart st 24 StackNat.wbA 4 ∧ Apart st 24 (stFree M st).1 (stFree M st).2

/-- the callee's post in memory form -/
@[reducible] def SnPost (R : RtInv) (b : Nat) (L L' : List (Nat × Nat)) (b' g sp st k : Nat) (M M' : Memory) : Prop :=
  LiveExt R L L' ∧ b - stackNatCost (stLen M st) k ≤ b' ∧ R.inv b' L' g (view R.rt L' M') ∧ StkOK M' R L' st ∧
  stLen M' st = stLen M st + StackNat.rnd k ∧
  (stLen M st + StackNat.rnd k ≤ stCap M st → stW M' st = stW M st ∧ stCap M' st = stCap M st) ∧
  (stCap M st < stLen M st + StackNat.rnd k → InRanges (stW M' st) (8 * stCap M' st) R.rt ∧
    ApartAll (stW M' st) (8 * stCap M' st) L) ∧
  MemFrame M M' (R.rt ++ [(sp - 4208, sp - 8), (sp + 8, sp + 24)] ++ stkWs M st) ∧ LiveFrame M M' L (stkWs M st) ∧
  M'.regions = M.regions ∧
  (stCap M st < stLen M st + StackNat.rnd k → (stW M' st, stW M' st + 8 * stCap M' st) ∈ L')

/-- the stack array after a stack-nat call: kept, or the callee's fresh element of `L'` -/
theorem SnPost.arrIn {R : RtInv} {b : Nat} {L L' : List (Nat × Nat)} {b' g sp st k : Nat} {M M' : Memory}
    (hS : SnPost R b L L' b' g sp st k M M') : ArrIn L' st M M' :=
  ArrIn.of_nat hS.2.2.2.1.2.2.2.2.2.1 hS.2.2.2.2.1 hS.2.2.2.2.2.1 hS.2.2.2.2.2.2.2.2.2.2

set_option maxRecDepth 20000 in
set_option janus.callRegions true in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `buf := stk.nat(17n)`: from the entry of `(*stack).nat` (return address `p01`) to `p01` -/
theorem snCall (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hSN : StackNat.HypL impl R StackNat.names 4208 24)
    (ret : Nat) (hret : RetAddr (LibW.program.link impl) ret) (Q : Outcome → Prop)
    (b : Nat) (L : List (Nat × Nat)) (g sp n st : Nat) (M : Memory) (r18 r29 : BitVec 64)
    (hpre : SnPre R b L g sp st (17 * n) M) (hst : st < 2 ^ 64) (hn : 0 < n)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 snE) (hsp : S.sp = BitVec.ofNat 64 sp)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 (17 * n))
    (h30 : S.regs 30 = BitVec.ofNat 64 p01)
    (h18 : S.regs 18 = r18) (h28 : S.regs 28 = BitVec.ofNat 64 g) (h29 : S.regs 29 = r29) (hmem : S.mem = M)
    (KB : ∀ (S' : State) (M' : Memory) (L' : List (Nat × Nat)) (b' : Nat),
      S'.pc = BitVec.ofNat 64 p01 → S'.sp = BitVec.ofNat 64 sp →
      S'.regs 0 = BitVec.ofNat 64 (stW M' st + 8 * stLen M st) → S'.regs 1 = BitVec.ofNat 64 (17 * n) →
      S'.regs 2 = BitVec.ofNat 64 (17 * n) →
      S'.regs 18 = r18 → S'.regs 28 = BitVec.ofNat 64 g → S'.regs 29 = r29 → S'.mem = M' →
      SnPost R b L L' b' g sp st (17 * n) M M' →
      Reaches ((LibW.program.link impl).withExit ret) S' Q) :
    Reaches ((LibW.program.link impl).withExit ret) S Q := by
  obtain ⟨hce, hserv, hsok, hstw, harr, hk16, hlen, hcost, hinv, hwba, hstwb, hstf⟩ := hpre
  have hce0 := hce
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro⟩ := hce0
  have hns : ∀ x, StackNat.names.contains x = true → LibW.names.contains x = true := MontW.sub_of_all (by decide)
  have hS0 := LibWC.hypSum hap hns (hSN b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 (17 * n)))
  rw [show segAddr Extracted.program StackNat.fn = snE by decide] at hS0
  have tst := toNat_lt' hst
  have tk : (BitVec.ofNat 64 (17 * n)).toNat = 17 * n := toNat_lt' (by omega)
  have tsp : S.sp.toNat = sp := by rw [hsp]; exact toNat_lt' (by omega)
  have tg : (S.regs 28).toNat = g := by rw [h28]; exact toNat_lt' (by omega)
  refine Reaches.call_regions (hS0.withExit hret) hpc ⟨?ra, ?args, ?pre⟩ (fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_)
  case ra =>
    rw [h30, toNat_lt' (by decide)]
    exact CallW.retAddr_restrict hap (cs := Extracted.seg34) (ns := StackNat.names)
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide) 363
      (by decide) (by decide) (by decide)
  case args =>
    simp only [ArgsFrom]
    exact ⟨h0, h1, trivial⟩
  case pre =>
    simp only [StackNat.Pre]
    rw [tst, tk, hmem]
    have hce' := CallW.callEnv_of hce hsp h28 hmem (stk := 4208) (above := 24) (by omega) (by omega)
    simp only [win, tsp, tg]
    unfold Apart at hstw
    refine ⟨hce', hserv, hsok, by simp only [outside_cons, outside_nil, and_true]; omega, fun hc => ?_, hk16, hlen,
      hcost, hinv, hwba, hstwb, hstf⟩
    obtain ⟨a1, a2⟩ := harr hc
    unfold Apart at a1
    exact ⟨by simp only [outside_cons, outside_nil, and_true]; omega, a2⟩
  obtain ⟨hX0, hX1, hX2, L', b', ⟨hLE, hb', hinv'⟩, hsok', hlen', hkept, hfresh, hF, hLF, hmS⟩ := hq
  simp only [tst, tk, hmem, tsp, tg, winA] at hX0 hX1 hX2 hb' hinv' hsok' hlen' hkept hfresh hF hLF hmS
  refine KB s' s'.mem L' b' (hr.trans h30) (e1.trans hsp) (hX0 (by omega)) hX1 hX2 (e4.trans h18) (e2.trans h28) (e3.trans h29)
    rfl ⟨hLE, hb', hinv', hsok', hlen', hkept, hfresh, hF, hLF, by rw [hrg, hmem], hmS⟩

end FvModexp.Arm64.W4Pro
