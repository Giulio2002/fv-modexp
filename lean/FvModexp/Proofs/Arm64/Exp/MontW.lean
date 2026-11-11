import FvModexp.Proofs.Arm64.Exp.Mont
import FvModexp.Proofs.Arm64.Exp.LibExp
import FvModexp.Proofs.Common.Link

/-!
# `nat.montgomery` as a callee of the windowed exponentiations (arm64)

`Mont.ens` moved into `LibExp.program` (the exp layer's restricted program, names = `RunIface.namesExp`) with a
call-site precondition that a caller's executor discharges cheaply: the static facts `MCall` about an anchor memory `M0`
(proved once per loop, pure Lean), `MemFrame M0 s.mem W` (the executor's frame closer, through the caller's stores) and the
invariant on the current memory. Values in `Nat`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.MontW

/-- An input array `p[0:n]` of a montgomery call at the anchor memory `M0` (stack pointer `sp` of the caller). -/
@[reducible] def MIn (R : RtInv) (L : List (Nat × Nat)) (sp : Nat) (M0 : Memory) (p n : Nat) : Prop :=
  M0.accessible p (8 * n) false = true ∧ p + 8 * n ≤ 2 ^ 48 ∧ (InRanges p (8 * n) L ∨ Outside p (8 * n) R.rt) ∧ Apart p (8 * n) (sp - 4288) (4288 + 120)

/-- The static facts of a call `r.montgomery(x, y, m, k, n)` at the anchor memory `M0`. -/
def MCall (R : RtInv) (L : List (Nat × Nat)) (g sp n mp mc rp rc xp yp : Nat) (M0 : Memory) : Prop :=
  sp % 16 = 0 ∧ 4288 ≤ sp ∧ sp + 120 ≤ 2 ^ 48 ∧ M0.accessible (sp - 4288) (4288 + 120) true = true ∧
  g + 24 ≤ 2 ^ 48 ∧ M0.accessible (g + 16) 8 false = true ∧ M0.readLE (g + 16) 8 + 4288 < sp ∧
  Outside (sp - 4288) (4288 + 120) R.rt ∧ Apart (g + 16) 8 (sp - 4288) (4288 + 120) ∧ Outside (g + 16) 8 R.rt ∧
  LiveSep L [(sp - 4288, sp + 120)] ∧
  0 < n ∧ 2 * n ≤ rc ∧ rc < 2 ^ 40 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  M0.accessible rp (8 * rc) true = true ∧ rp + 8 * rc ≤ 2 ^ 48 ∧ (InRanges rp (8 * rc) L ∨ Outside rp (8 * rc) R.rt) ∧
  Apart rp (8 * rc) (sp - 4288) (4288 + 120) ∧ Apart (g + 16) 8 rp (8 * rc) ∧
  MIn R L sp M0 xp n ∧ MIn R L sp M0 yp n ∧ MIn R L sp M0 mp n ∧
  Apart rp (8 * rc) xp (8 * n) ∧ Apart rp (8 * rc) yp (8 * n) ∧ Apart rp (8 * rc) mp (8 * n) ∧
  R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
  R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, 8 * n]

/-- what a caller learns (values of the pre-call memory) -/
@[reducible] def MPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g sp n mp rp rc xp yp k : Nat) (s s' : State) : Prop :=
  (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
  s'.regs 0 = BitVec.ofNat 64 rp ∧ s'.regs 1 = BitVec.ofNat 64 n ∧ s'.regs 2 = BitVec.ofNat 64 rc ∧
  s'.mem.readLE rp (8 * n) =
    Exp.montgomery n (s.mem.readLE xp (8 * n)) (s.mem.readLE yp (8 * n)) (s.mem.readLE mp (8 * n)) k ∧
  R.inv b L g (view R.rt L s'.mem) ∧
  MemFrame s.mem s'.mem (R.rt ++ [(sp - 4288, sp + 120)] ++ [(rp, rp + 8 * rc)]) ∧
  LiveFrame s.mem s'.mem L [(rp, rp + 8 * rc)]

theorem sub_of_all {ns ms : List String} (h : ns.all ms.contains = true) :
    ∀ x, ns.contains x = true → ms.contains x = true := by
  intro x hx
  rw [List.all_eq_true] at h
  exact h x (by simpa using hx)

theorem toNat_of {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- the montgomery call summary in `LibExp` -/
theorem sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc rp rc xp yp k : Nat) (zl xc yc : BitVec 64)
    (M0 : Memory) (W : List (Nat × Nat)) (hc : MCall R L g sp n mp mc rp rc xp yp M0) (hk : k < 2 ^ 64)
    (hgW : Outside (g + 16) 8 W) :
    Summary (LibExp.program.link impl) (segAddr LibExp.program MontHyp.fn)
      (fun s => RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [BitVec.ofNat 64 rp, zl, BitVec.ofNat 64 rc, BitVec.ofNat 64 xp, BitVec.ofNat 64 n, xc,
          BitVec.ofNat 64 yp, BitVec.ofNat 64 n, yc, BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc,
          BitVec.ofNat 64 k, BitVec.ofNat 64 n] ∧
        s.sp = BitVec.ofNat 64 sp ∧ s.regs 28 = BitVec.ofNat 64 g ∧ MemFrame M0 s.mem W ∧
        R.inv b L g (view R.rt L s.mem))
      (MPost R b L g sp n mp rp rc xp yp k) := by
  obtain ⟨hal, hsp1, hsp2, hwacc, hg1, hg2, hg3, hwrt, hgw, hgrt, hLs, hn, hrc, hrc', hmc, hmc', hracc, hrp, hrh,
    hrw, hgr, hx, hy, hm, hrx, hry, hrm, hok1, hok2⟩ := hc
  have hsub : ∀ x, LibMont.names.contains x = true → LibExp.names.contains x = true :=
    sub_of_all (by decide)
  have hS := Ensures.toSummaryIn (Mont.ens impl hap R hclr hmv b L (BitVec.ofNat 64 rp) zl (BitVec.ofNat 64 rc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 n) xc (BitVec.ofNat 64 yp) (BitVec.ofNat 64 n) yc (BitVec.ofNat 64 mp)
    (BitVec.ofNat 64 n) (BitVec.ofNat 64 mc) (BitVec.ofNat 64 k) (BitVec.ofNat 64 n))
    (noExit_restrict hap LibMont.names) (codeIn_restrict_mono hap hsub)
  rw [← LibExp.eq_only] at hS
  have e1 : segAddr Extracted.program MontHyp.fn = segAddr LibExp.program MontHyp.fn := by decide
  rw [e1] at hS
  have b48 : ∀ x, x ≤ 2 ^ 48 → x < 2 ^ 64 := fun x h => by omega
  have tn := toNat_of (b48 n (by omega))
  have trp := toNat_of (b48 rp (by omega))
  have trc := toNat_of (b48 rc (by omega))
  have txp := toNat_of (b48 xp (by unfold MIn at hx; omega))
  have typ := toNat_of (b48 yp (by unfold MIn at hy; omega))
  have tmp := toNat_of (b48 mp (by unfold MIn at hm; omega))
  have tmc := toNat_of (b48 mc (by omega))
  have tk := toNat_of hk
  refine Summary.mono hS (fun s ⟨hr, ha, hs, h28, hF, hinv⟩ => ⟨hr, ha, ?_⟩) (fun s s' ⟨hr, ha, hs, h28, hF, hinv⟩ hp => ?_)
  · have eA : ∀ a k w, s.mem.accessible a k w = M0.accessible a k w := hF.accessible
    have hsp : s.sp.toNat = sp := by rw [hs]; exact toNat_of (b48 sp (by omega))
    have hg : (s.regs 28).toNat = g := by rw [h28]; exact toNat_of (b48 g (by omega))
    have hgv : s.mem.readLE (g + 16) 8 = M0.readLE (g + 16) 8 := hF.readLE _ _ hgW
    unfold Mont.Pre Mont.Env Mont.Input GuardOK StackOK
    rw [hsp, hg, trp, trc, txp, typ, tmp, tmc, tn, eA, eA, eA, eA, eA, eA, hgv]
    unfold MIn at hx hy hm
    exact ⟨⟨⟨by omega, hg2, by omega⟩, ⟨hal, by omega, hsp2, hwacc⟩, hwrt, hgw, hgrt, hLs⟩,
      rfl, rfl, rfl, hn, hrc, hrc', hmc, hmc', hracc, hrp, hrh, hrw, hgr, hx, hy, hm, hrx, hry, hrm, hinv, hok1, hok2⟩
  · obtain ⟨hregs, hp⟩ := hp
    have hsp : s.sp.toNat = sp := by rw [hs]; exact toNat_of (b48 sp (by omega))
    have hg : (s.regs 28).toNat = g := by rw [h28]; exact toNat_of (b48 g (by omega))
    unfold Mont.Post at hp
    rw [hsp, hg, trp, trc, txp, typ, tmp, tk, tn] at hp
    obtain ⟨e0, e1, e2, ev, L', b', rfl, rfl, hi, hf, hl⟩ := hp
    exact ⟨hregs, e0, e1, e2, ev, hi, hf, hl⟩

end FvModexp.Arm64.MontW
