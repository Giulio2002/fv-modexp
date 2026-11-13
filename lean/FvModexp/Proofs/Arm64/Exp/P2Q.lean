import FvModexp.Proofs.Arm64.Exp.LibCallsQ
import FvModexp.Proofs.Arm64.Nat.StackNatX

set_option autoImplicit false

/-!
# Q-form helpers for the `P2` chain (`buildPrecomputationWindowModPower2`, `expNNPowerOfTwoWindowSize{2,4}`; arm64; divmc s42)

TIGHT COSTS (NOTES-conventions "[divmc s42] P2 Q-form conversion"): the P2 functions keep an EFFECTIVE budget `b1` in their
contexts, the invariant holding at `b1 + stkR H M st` (the unheld part of the stack reserve `stkRes H` on top).
* `stkNatCallQ`: `LibCalls.stkNatCallL` for divmc's Q-form `StackNatX.HypQ` (no charge; the reserve pays a growth).
* `inv_eff`: an invariant at a real budget `b' ≥ r` is one at the effective budget `b' - r` plus `r`.
* `qstep` / `lstep`: the effective budget step after a Q-form callee (`sqr`/`mul`/`stk.nat`) / after a callee that
  keeps the stack header (`trunc`, `memmove`, write barriers; `stCap` unchanged).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.LibCalls

set_option maxRecDepth 20000 in
/-- `stkNatCallL` for the Q-form `(*stack).nat` (`StackNatX.HypQ`, reserve level `H`) -/
theorem stkNatCallQ {impl : List Segment} (hap : ImplApart Extracted.program impl) {R : RtInv} {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {stk above : Nat}
    (hsn : StackNatX.HypQ impl R ns stk above) (H : Nat) {b : Nat} {L : List (Nat × Nat)} {st n : Nat}
    {S : State} {ret : BitVec 64} {Q : State → Prop} {ra : Nat}
    (hra : RetAddr ((Extracted.program.onlySegments ns).link impl) ra)
    (hpc : S.pc = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn)) (h30 : S.regs 30 = BitVec.ofNat 64 ra)
    (h0 : S.regs 0 = BitVec.ofNat 64 st) (h1 : S.regs 1 = BitVec.ofNat 64 n)
    (bst : st < 2 ^ 64) (bn : n < 2 ^ 64) (bra : ra < 2 ^ 64)
    (hpre : StackNatX.PreQ R b L H stk above st n S)
    (K : ∀ s', s'.pc = BitVec.ofNat 64 ra → s'.sp = S.sp → s'.regs 28 = S.regs 28 → s'.regs 29 = S.regs 29 →
      s'.regs 18 = S.regs 18 → s'.mem.regions = S.mem.regions → StackNatX.PostQ R b L H stk above st n S s' →
      ReachesRet (LibW.program.link impl) ret s' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  have hS := CallWW.hypSum hap hns (hsn H b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 n))
  refine ReachesRet.call_regions hS hpc ⟨?_, ?_, ?_⟩ fun s' hr ⟨⟨e1, e2, e3, e4⟩, hq⟩ hrg => ?_
  · rw [h30, LibCalls.tN bra]; exact hra
  · simp only [ArgsFrom]; exact ⟨h0, h1, trivial⟩
  · rw [LibCalls.tN bst, LibCalls.tN bn]; exact hpre
  · rw [LibCalls.tN bst, LibCalls.tN bn] at hq
    exact K s' (hr.trans h30) e1 e2 e3 e4 hrg hq

end FvModexp.Arm64.LibCalls

namespace FvModexp.Arm64.P2Q

/-- an invariant at the real budget `b'` is one at the effective budget `b' - r` (reserve part `r ≤ b'`) -/
theorem inv_eff {R : RtInv} {b' r : Nat} {L : List (Nat × Nat)} {g : Nat} {v : Memory}
    (h : R.inv b' L g v) (hr : r ≤ b') : R.inv (b' - r + r) L g v := by
  rwa [Nat.sub_add_cancel hr]

/-- the effective step after a Q-form callee charged `C` (pre `C + r ≤ b1 + r`, post `b1 + r - (C + r) + r' ≤ b'`) -/
theorem qstep {b1 C r r' b' : Nat} (h : b1 + r - (C + r) + r' ≤ b') (hc : C ≤ b1) :
    b1 - C ≤ b' - r' ∧ r' ≤ b' := by omega

/-- the effective step after a callee that keeps the stack capacity (`r` unchanged) charged `c` -/
theorem lstep {b1 c r b' : Nat} (h : b1 + r - c ≤ b') (hc : c ≤ b1) : b1 - c ≤ b' - r ∧ r ≤ b' := by omega

/-- `stkR` at a memory whose stack capacity is unchanged -/
theorem stkR_eq {H : Nat} {M M' : Memory} {st : Nat} (h : stCap M' st = stCap M st) : stkR H M' st = stkR H M st :=
  stkR_congr h

end FvModexp.Arm64.P2Q

namespace FvModexp.Arm64.P2Q

/-- the effective budget after a callee that keeps the stack capacity (`r' = r`), charged `c ≤ b1` -/
theorem effL {R : RtInv} {b1 c r r' b' : Nat} {L : List (Nat × Nat)} {g : Nat} {v : Memory} (hinv : R.inv b' L g v)
    (h : b1 + r - c ≤ b') (hc : c ≤ b1) (hr : r' = r) : ∃ b2, R.inv (b2 + r') L g v ∧ b1 - c ≤ b2 :=
  ⟨b' - r, by rw [hr, Nat.sub_add_cancel (by omega)]; exact hinv, by omega⟩

/-- the effective budget after a Q-form callee charged `C ≤ b1` (reserve `r` before, `r'` after) -/
theorem effQ {R : RtInv} {b1 C r r' b' : Nat} {L : List (Nat × Nat)} {g : Nat} {v : Memory} (hinv : R.inv b' L g v)
    (h : b1 + r - (C + r) + r' ≤ b') (hc : C ≤ b1) : ∃ b2, R.inv (b2 + r') L g v ∧ b1 - C ≤ b2 :=
  ⟨b' - r', by rw [Nat.sub_add_cancel (by omega)]; exact hinv, by omega⟩

end FvModexp.Arm64.P2Q
