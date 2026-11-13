import FvModexp.Proofs.Amd64.Exp.W2One
import FvModexp.Proofs.Amd64.Exp.W2ExS
import FvModexp.Proofs.Amd64.Nat.StackNatDefs
import FvModexp.Proofs.Amd64.Nat.Callees2

set_option autoImplicit false

/-!
# window-2 prologue (amd64): `buf := stk.nat(5n)` (nat.go:1549) — the call (agent expmc s50)

Twin of `Arm64.W2Pro.snCall`: from the entry of `(*stack).nat` (`RSP = sp - 8`, return address `p01` at `[sp - 8]`)
to `p01`, through the `StackNat.HypL … 4192 24` summary (callee window `[sp - 4200, sp + 16)`), with the memory-form
facts `SnPost`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp FvModexp.Amd64.Callees
open Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.W2Pro

open FvModexp.Amd64.W2Loop (Env Inp Buf OneIn)

/-- the free part of the stack's array -/
@[reducible] def stFree (M : Memory) (st : Nat) : Nat × Nat :=
  (stW M st + 8 * stLen M st, 8 * (stCap M st - stLen M st))

/-- a stack-nat call of the window-2 frame: the facts at the call -/
@[reducible] def SnPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g fs sp st k : Nat) (M : Memory) : Prop :=
  CallW.CEnv R L g fs (sp - 8) 4288 688 M ∧ RunIface.Serves R ∧ StkOK M R L st ∧
  Apart st 24 (sp - 4296) (4296 + 0x2a8) ∧
  (0 < stCap M st → Apart (stW M st) (8 * stCap M st) (sp - 4296) (4296 + 0x2a8) ∧
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
  MemFrame M M' (R.rt ++ [(sp - 8 - 4192, sp - 8 + 24)] ++ stkWs M st) ∧ LiveFrame M M' L (stkWs M st) ∧
  M'.regions = M.regions ∧
  (stCap M st < stLen M st + StackNat.rnd k → (stW M' st, stW M' st + 8 * stCap M' st) ∈ L')

theorem snE_eq : segAddr Extracted.program StackNat.fn = snE := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- `buf := stk.nat(k)`: from the entry of `(*stack).nat` (return address `p01`) to `p01` -/
theorem snCall {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {R : RtInv}
    (hSN : StackNat.HypL impl R StackNat.names 4192 24)
    {ret : W64} {Q : State → Prop} {b : Nat} {L : List (Nat × Nat)} {g fs sp st k : Nat} {r5 : W64}
    (S : State) (hpre : SnPre R b L g fs sp st k S.mem) (hst : st < 2 ^ 64) (hpc : S.rip = BitVec.ofNat 64 snE) (hsp : S.regs 4 = BitVec.ofNat 64 (sp - 8))
    (hrd : S.mem.readLE (sp - 8) 8 = p01)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h3 : S.regs 3 = BitVec.ofNat 64 k)
    (h5 : S.regs 5 = r5) (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase.toNat = fs) (hx15 : S.xmm 15 = 0)
    (hdf : S.df = false)
    (KB : ∀ (S' : State) (L' : List (Nat × Nat)) (b' : Nat),
      S'.rip = BitVec.ofNat 64 p01 → S'.regs 4 = BitVec.ofNat 64 sp → S'.regs 5 = r5 →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase.toNat = fs → S'.xmm 15 = 0 → S'.df = false →
      (0 < k → S'.regs 0 = BitVec.ofNat 64 (stW S'.mem st + 8 * stLen S.mem st)) →
      S'.regs 1 = BitVec.ofNat 64 k →
      SnPost R b L L' b' g sp st k S.mem S'.mem →
      ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  obtain ⟨hce, hserv, hsok, hstw, harr, hk16, hlen, hcost, hinv, hwba, hstwb, hstf⟩ := hpre
  have hce0 := hce
  obtain ⟨hal, hK, hA, hacc, hg1, hg2, hg3, hrt, hga, hgrt, hLs, hd, hro, f1, f2, f3, f4, f5, f6⟩ := hce0
  have hc : CodeIn64 ((Extracted.program.onlySegments StackNat.names).link impl) (LibW.program.link impl) := by
    rw [LibW.eq_only]; exact A64.codeIn_restrict_mono64 hap (MontW.sub_of_all (by decide))
  have hS := Ensures.toSummaryRegs2 (fun a0 a1 => hSN b L a0 a1) (A64.noExit_restrict64 hap StackNat.names) hc
  rw [snE_eq] at hS
  have tst : (BitVec.ofNat 64 st).toNat = st := MontW.toNat_of hst
  have tk : (BitVec.ofNat 64 k).toNat = k := MontW.toNat_of (by omega)
  have tsp : (S.regs 4).toNat = sp - 8 := by rw [hsp]; exact MontW.toNat_of (by omega)
  have tg : (S.regs 14).toNat = g := by rw [h14]; exact MontW.toNat_of (by omega)
  refine ReachesRet.call_regions hS hpc ⟨?ra, hx15, hdf, ?pre⟩ (fun s' hr hq hrg => ?_)
  case ra =>
    rw [tsp, hrd]
    exact W2Loop.ra_of hap (by decide) 0x852 (by decide)
  case pre =>
    rw [h0, h3]
    simp only [StackNat.Pre]
    rw [tst, tk]
    have hce' := CallW.callEnv_of hce tsp tg hfs rfl (stk := 4192) (above := 24) (by omega) (by omega) (by omega)
    simp only [win, tsp, tg]
    unfold Apart at hstw
    refine ⟨hce', hserv, hsok, by simp only [outside_cons, outside_nil, and_true]; omega, fun hc => ?_, hk16, hlen,
      hcost, hinv, hwba, hstwb, hstf⟩
    obtain ⟨a1, a2⟩ := harr hc
    unfold Apart at a1
    exact ⟨by simp only [outside_cons, outside_nil, and_true]; omega, a2⟩
  obtain ⟨⟨e4, e5, e14, e15⟩, hq⟩ := hq
  rw [h0, h3] at hq
  obtain ⟨efs, edf, hX0, hX3, hX1, L', b', ⟨hLE, hb', hinv'⟩, hsok', hlen', hkept, hfresh, hF, hLF, hmS⟩ := hq
  simp only [tst, tk, tsp, tg, win] at hX0 hX1 hb' hinv' hsok' hlen' hkept hfresh hF hLF hmS
  refine KB s' L' b' (by rw [hr, retAddrOf_eq, tsp, hrd]) (by rw [e4, hsp]; exact W2Loop.sp_add8 (by omega) (by omega))
    (e5.trans h5) (e14.trans h14) (by rw [efs, hfs]) (by rw [e15, hx15]) (by rw [edf, hdf]) hX0 hX1
    ⟨hLE, hb', hinv', hsok', hlen', hkept, hfresh, by simpa only [List.append_assoc] using hF, hLF, hrg, hmS⟩

end FvModexp.Amd64.W2Pro
