import FvModexp.Proofs.Arm64.Exp.LibW
import FvModexp.Proofs.Arm64.Exp.CallW
import FvModexp.Proofs.Arm64.Exp.MontW
import FvModexp.Proofs.Arm64.Exp.DeferW
import FvModexp.Proofs.Arm64.Exp.CmpW

/-!
# The window layer's callees in `LibW` (arm64)

`LibW` = `LibExp` without the window layer's callers (`nat.expNNOdd`, `nat.expNN`, `nat.expNNEven`, `(*Int).exp`), so a
return address inside a caller is a `RetAddr` of the windows' program. Copies of `CallW.hypSum`, `MontW.sum`,
`DeferW.sum`, `CmpW.codeIn/sum` for `LibW.program`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.LibWC

theorem hypSum {impl : List Segment} (hap : ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {f : String} {args : List (BitVec 64)}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibW.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.regs 30).toNat ∧ ArgsFrom s 0 args ∧ pre s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        post s s') := by
  have hS := Ensures.toSummaryIn h (noExit_restrict hap ns) (codeIn_restrict_mono hap hns)
  rw [← LibW.eq_only] at hS
  exact hS

/-- the montgomery call summary in `LibW` -/
theorem montSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (g sp n mp mc rp rc xp yp k : Nat) (zl xc yc : BitVec 64)
    (gv : Nat) (hc : MontW.MCall R L g gv sp n mp mc rp rc xp yp) (hk : k < 2 ^ 64) :
    Summary (LibW.program.link impl) (segAddr LibW.program MontHyp.fn)
      (fun s => RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [BitVec.ofNat 64 rp, zl, BitVec.ofNat 64 rc, BitVec.ofNat 64 xp, BitVec.ofNat 64 n, xc,
          BitVec.ofNat 64 yp, BitVec.ofNat 64 n, yc, BitVec.ofNat 64 mp, BitVec.ofNat 64 n, BitVec.ofNat 64 mc,
          BitVec.ofNat 64 k, BitVec.ofNat 64 n] ∧
        s.sp = BitVec.ofNat 64 sp ∧ s.regs 28 = BitVec.ofNat 64 g ∧
        s.mem.accessible (sp - 4288) (4288 + 120) true = true ∧ s.mem.accessible (g + 16) 8 false = true ∧
        s.mem.readLE (g + 16) 8 = gv ∧ s.mem.accessible rp (8 * rc) true = true ∧
        s.mem.accessible xp (8 * n) false = true ∧ s.mem.accessible yp (8 * n) false = true ∧
        s.mem.accessible mp (8 * n) false = true ∧ R.inv b L g (view R.rt L s.mem))
      (MontW.MPost R b L g sp n mp rp rc xp yp k) := by
  obtain ⟨hal, hsp1, hsp2, hg1, hg3, hwrt, hgw, hgrt, hLs, hn, hrc, hrc', hmc, hmc', hrp, hrh,
    hrw, hgr, hx, hy, hm, hrx, hry, hrm, hok1, hok2⟩ := hc
  have hsub : ∀ x, LibMont.names.contains x = true → LibW.names.contains x = true :=
    MontW.sub_of_all (by decide)
  have hS := Ensures.toSummaryIn (Mont.ens impl hap R hclr hmv b L (BitVec.ofNat 64 rp) zl (BitVec.ofNat 64 rc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 n) xc (BitVec.ofNat 64 yp) (BitVec.ofNat 64 n) yc (BitVec.ofNat 64 mp)
    (BitVec.ofNat 64 n) (BitVec.ofNat 64 mc) (BitVec.ofNat 64 k) (BitVec.ofNat 64 n))
    (noExit_restrict hap LibMont.names) (codeIn_restrict_mono hap hsub)
  rw [← LibW.eq_only] at hS
  have e1 : segAddr Extracted.program MontHyp.fn = segAddr LibW.program MontHyp.fn := by decide
  rw [e1] at hS
  have b48 : ∀ x, x ≤ 2 ^ 48 → x < 2 ^ 64 := fun x h => by omega
  have tn := MontW.toNat_of (b48 n (by omega))
  have trp := MontW.toNat_of (b48 rp (by omega))
  have trc := MontW.toNat_of (b48 rc (by omega))
  have txp := MontW.toNat_of (b48 xp (by unfold MontW.MIn at hx; omega))
  have typ := MontW.toNat_of (b48 yp (by unfold MontW.MIn at hy; omega))
  have tmp := MontW.toNat_of (b48 mp (by unfold MontW.MIn at hm; omega))
  have tmc := MontW.toNat_of (b48 mc (by omega))
  have tk := MontW.toNat_of hk
  refine Summary.mono hS (fun s ⟨hr, ha, hs, h28, hwacc, hg2, hgv, hracc, hxa, hya, hma, hinv⟩ => ⟨hr, ha, ?_⟩)
    (fun s s' ⟨hr, ha, hs, h28, _⟩ hp => ?_)
  · have hsp : s.sp.toNat = sp := by rw [hs]; exact MontW.toNat_of (b48 sp (by omega))
    have hg : (s.regs 28).toNat = g := by rw [h28]; exact MontW.toNat_of (b48 g (by omega))
    unfold Mont.Pre Mont.Env Mont.Input GuardOK StackOK
    rw [hsp, hg, trp, trc, txp, typ, tmp, tmc, tn, hgv]
    unfold MontW.MIn at hx hy hm
    exact ⟨⟨⟨by omega, hg2, by omega⟩, ⟨hal, by omega, hsp2, hwacc⟩, hwrt, hgw, hgrt, hLs⟩,
      rfl, rfl, rfl, hn, hrc, hrc', hmc, hmc', hracc, hrp, hrh, hrw, hgr, ⟨hxa, hx⟩, ⟨hya, hy⟩, ⟨hma, hm⟩, hrx, hry, hrm,
      hinv, hok1, hok2⟩
  · obtain ⟨hregs, hp⟩ := hp
    have hsp : s.sp.toNat = sp := by rw [hs]; exact MontW.toNat_of (b48 sp (by omega))
    have hg : (s.regs 28).toNat = g := by rw [h28]; exact MontW.toNat_of (b48 g (by omega))
    unfold Mont.Post at hp
    rw [hsp, hg, trp, trc, txp, typ, tmp, tk, tn] at hp
    obtain ⟨e0, e1, e2, ev, L', b', rfl, rfl, hi, hf, hl⟩ := hp
    exact ⟨hregs, e0, e1, e2, ev, hi, hf, hl⟩

theorem deferSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (fn : String)
    (hfn : fn ∈ ["github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNEven.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize4.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNOddMontgomeryWindowSize2.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize4.deferwrap1",
      "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.expNNPowerOfTwoWindowSize2.deferwrap1"]) :
    Summary (LibW.program.link impl) (segAddr LibW.program fn) Defer.Pre Defer.Post := by
  have hsub : ∀ x, LibDefer.names.contains x = true → LibW.names.contains x = true :=
    MontW.sub_of_all (by decide)
  have hc := codeIn_restrict_mono hap hsub
  rw [← LibDefer.eq_only, ← LibW.eq_only] at hc
  have h := Janus.Contracts.EqHashModel.Summary.of_codeIn hc (Defer.sum impl fn hfn)
  have e : segAddr LibDefer.program fn = segAddr LibW.program fn := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfn
    rcases hfn with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [e] at h
  exact h

set_option maxRecDepth 100000 in
theorem cmpCodeIn (impl : List Segment) : Janus.Contracts.EqHashModel.CodeIn FvModexp.Lib.CmpA64.program (LibW.program.link impl) :=
  MontAsm.codeIn_single [Extracted.seg3, Extracted.seg6, Extracted.seg7, Extracted.seg8, Extracted.seg9, Extracted.seg10, Extracted.seg12, Extracted.seg13, Extracted.seg14]
    [Extracted.seg16, Extracted.seg17, Extracted.seg18, Extracted.seg19, Extracted.seg20, Extracted.seg22, Extracted.seg24, Extracted.seg25, Extracted.seg26, Extracted.seg27, Extracted.seg28, Extracted.seg29, Extracted.seg30, Extracted.seg31, Extracted.seg32, Extracted.seg33, Extracted.seg34, Extracted.seg35, Extracted.seg36, Extracted.seg37, Extracted.seg38, Extracted.seg39, Extracted.seg40, Extracted.seg41, Extracted.seg42, Extracted.seg43, Extracted.seg44, Extracted.seg45, Extracted.seg46, Extracted.seg47, Extracted.seg48, Extracted.seg49, Extracted.seg50, Extracted.seg51, Extracted.seg52, Extracted.seg53, Extracted.seg54, Extracted.seg55, Extracted.seg56, Extracted.seg57, Extracted.seg58, Extracted.seg59, Extracted.seg60, Extracted.seg61, Extracted.seg63, Extracted.seg64, Extracted.seg65, Extracted.seg67, Extracted.seg68, Extracted.seg69, Extracted.seg70, Extracted.seg71, Extracted.seg72, Extracted.seg73, Extracted.seg74, Extracted.seg75, Extracted.seg76, Extracted.seg77, Extracted.seg78, Extracted.seg79, Extracted.seg80, Extracted.seg81, Extracted.seg82, Extracted.seg83] impl (S := Extracted.seg15) rfl rfl (by decide) (by decide)

theorem cmpSum (impl : List Segment) :
    Summary (LibW.program.link impl) 1782608 CmpSum.Pre CmpSum.Post :=
  Janus.Contracts.EqHashModel.Summary.of_codeIn (cmpCodeIn impl) CmpSum.cmp_summary

end FvModexp.Arm64.LibWC
