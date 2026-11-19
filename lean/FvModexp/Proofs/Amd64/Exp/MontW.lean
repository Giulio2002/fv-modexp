import FvModexp.Proofs.Amd64.Exp.Mont
import FvModexp.Proofs.Amd64.Exp.LibW
import FvModexp.Proofs.Common.Link

/-!
# `nat.montgomery` as a callee of the windowed exponentiations (amd64) — twin of `Arm64.MontW` + `Arm64.LibWC.montSum`

`Mont.ens` moved into `LibW.program` (the window layer's restricted program) with a call-site precondition that a caller's
executor discharges cheaply: the static facts `MCall` about the call (proved once per loop, pure Lean; `r` = the callee's
`RSP`, i.e. the caller's `SP - 8` after the `CALL` push), and the dynamic facts on the current state (registers, the five
stack words `m`, `len m`, `cap m`, `k`, `n` at `r+8 … r+40`, the invariant). Values in `Nat`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

set_option autoImplicit false

namespace FvModexp.Amd64.MontW

/-- An input array `p[0:n]` of a montgomery call with callee `RSP = r`. -/
@[reducible] def MIn (R : RtInv) (L : List (Nat × Nat)) (r : Nat) (p n : Nat) : Prop :=
  p + 8 * n ≤ 2 ^ 48 ∧ (InRanges p (8 * n) L ∨ Outside p (8 * n) R.rt) ∧ Apart p (8 * n) (r - 4288) (4288 + 104)

/-- The static facts of a call `rp.montgomery(x, y, m, k, n)` (callee `RSP = r`, `g = R14`, TLS base `fs`). -/
def MCall (R : RtInv) (L : List (Nat × Nat)) (g gv fs r n mp mc rp rc xp yp : Nat) : Prop :=
  r % 8 = 0 ∧ 4288 ≤ r ∧ r + 104 ≤ 2 ^ 48 ∧
  g + 24 ≤ 2 ^ 48 ∧ gv + 4288 < r ∧
  Outside (r - 4288) (4288 + 104) R.rt ∧ Apart (g + 16) 8 (r - 4288) (4288 + 104) ∧ Outside (g + 16) 8 R.rt ∧
  LiveSep L [(r - 4288, r + 104)] ∧
  (8 ≤ fs ∧ fs ≤ 2 ^ 48) ∧ Apart (fs - 8) 8 (r - 4288) (4288 + 104) ∧ Outside (fs - 8) 8 R.rt ∧
  0 < n ∧ 2 * n ≤ rc ∧ rc < 2 ^ 40 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  rp + 8 * rc ≤ 2 ^ 48 ∧ (InRanges rp (8 * rc) L ∨ Outside rp (8 * rc) R.rt) ∧
  Apart rp (8 * rc) (r - 4288) (4288 + 104) ∧ Apart (g + 16) 8 rp (8 * rc) ∧ Apart (fs - 8) 8 rp (8 * rc) ∧
  MIn R L r xp n ∧ MIn R L r yp n ∧ MIn R L r mp n ∧
  Apart rp (8 * rc) xp (8 * n) ∧ Apart rp (8 * rc) yp (8 * n) ∧ Apart rp (8 * rc) mp (8 * n) ∧
  R.ok (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") [rp, 16 * n] ∧
  R.ok (Extracted.program.contractAddr "runtime.memmove") [rp, rp + n * 8, n * 8]

/-- the dynamic facts at the callee's entry `s` -/
@[reducible] def MDyn (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g gv fs r n mp mc rp rc xp yp k : Nat)
    (s : State) : Prop :=
  (s.regs 4).toNat = r ∧ (s.regs 14).toNat = g ∧ s.fsBase.toNat = fs ∧
  s.mem.accessible (r - 4288) (4288 + 104) true = true ∧ s.mem.accessible (g + 16) 8 false = true ∧
  s.mem.readLE (g + 16) 8 = gv ∧ s.mem.accessible (fs - 8) 8 false = true ∧ s.mem.readLE (fs - 8) 8 = g ∧
  s.mem.readLE (r + 8) 8 = mp ∧ s.mem.readLE (r + 16) 8 = n ∧ s.mem.readLE (r + 24) 8 = mc ∧
  s.mem.readLE (r + 32) 8 = k ∧ s.mem.readLE (r + 40) 8 = n ∧
  s.mem.accessible rp (8 * rc) true = true ∧ s.mem.accessible xp (8 * n) false = true ∧
  s.mem.accessible yp (8 * n) false = true ∧ s.mem.accessible mp (8 * n) false = true ∧
  s.mem.accessible MontHyp.hasADX 1 false = true ∧ R.inv b L g (view R.rt L s.mem)

/-- what a caller learns (values of the pre-call memory) -/
@[reducible] def MPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (g r n mp rp rc xp yp k : Nat) (s s' : State) :
    Prop :=
  (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  s'.regs 0 = BitVec.ofNat 64 rp ∧ s'.regs 3 = BitVec.ofNat 64 n ∧ s'.regs 1 = BitVec.ofNat 64 rc ∧
  s'.mem.readLE rp (8 * n) =
    Exp.montgomery n (s.mem.readLE xp (8 * n)) (s.mem.readLE yp (8 * n)) (s.mem.readLE mp (8 * n)) k ∧
  R.inv b L g (view R.rt L s'.mem) ∧
  MemFrame s.mem s'.mem (R.rt ++ [(r - 4288, r + 104)] ++ [(rp, rp + 8 * rc)]) ∧
  LiveFrame s.mem s'.mem L [(rp, rp + 8 * rc)]

theorem sub_of_all {ns ms : List String} (h : ns.all ms.contains = true) :
    ∀ x, ns.contains x = true → ms.contains x = true := by
  intro x hx
  rw [List.all_eq_true] at h
  exact h x (by simpa using hx)

theorem toNat_of {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- the montgomery call summary in `LibW` (amd64) -/
theorem sum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (g gv fs r n mp mc rp rc xp yp k : Nat) (zl xc yc : BitVec 64)
    (hc : MCall R L g gv fs r n mp mc rp rc xp yp) (hk : k < 2 ^ 64) :
    Summary (LibW.program.link impl) (segAddr LibW.program MontHyp.fn)
      (fun s => RetAddr ((Extracted.program.onlySegments LibMont.names).link impl) (s.mem.readLE (s.regs 4).toNat 8) ∧
        s.xmm 15 = 0 ∧ ArgsFrom64 s 0 [BitVec.ofNat 64 rp, zl, BitVec.ofNat 64 rc, BitVec.ofNat 64 xp,
          BitVec.ofNat 64 n, xc, BitVec.ofNat 64 yp, BitVec.ofNat 64 n, yc] ∧ s.df = false ∧
        MDyn R b L g gv fs r n mp mc rp rc xp yp k s)
      (MPost R b L g r n mp rp rc xp yp k) := by
  obtain ⟨hal, hsp1, hsp2, hg1, hg3, hwrt, hgw, hgrt, hLs, hfs, htw, htrt, hn, hrc, hrc', hmc, hmc', hrp, hrh,
    hrw, hgr, htr, hx, hy, hm, hrx, hry, hrm, hok1, hok2⟩ := hc
  have hsub : ∀ x, LibMont.names.contains x = true → LibW.names.contains x = true :=
    sub_of_all (by decide)
  have b48 : ∀ x, x ≤ 2 ^ 48 → x < 2 ^ 64 := fun x h => by omega
  have hS := Ensures.toSummaryIn (Mont.ens impl hap R hclr hmv b L (BitVec.ofNat 64 rp) zl (BitVec.ofNat 64 rc)
    (BitVec.ofNat 64 xp) (BitVec.ofNat 64 n) xc (BitVec.ofNat 64 yp) (BitVec.ofNat 64 n) yc mp n mc k n)
    (A64.noExit_restrict64 hap LibMont.names) (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)
  rw [← LibW.eq_only] at hS
  have e1 : segAddr Extracted.program MontHyp.fn = segAddr LibW.program MontHyp.fn := by decide
  rw [e1] at hS
  have tn := toNat_of (b48 n (by omega))
  have trp := toNat_of (b48 rp (by omega))
  have trc := toNat_of (b48 rc (by omega))
  have txp := toNat_of (b48 xp (by unfold MIn at hx; omega))
  have typ := toNat_of (b48 yp (by unfold MIn at hy; omega))
  refine Summary.mono hS (fun s ⟨hr, hx15, ha, hdf, hd⟩ => ⟨hr, hx15, ha, hdf, ?_⟩)
    (fun s s' ⟨hr, hx15, ha, hdf, hd⟩ hp => ?_)
  · obtain ⟨hsp, hg, hfs', hwacc, hg2, hgv, htacc, htg, rm, rn, rmc, rk, rn', hracc, hxa, hya, hma, hadx, hinv⟩ := hd
    unfold Mont.Pre Mont.Env Mont.Input
    rw [hsp, hg, trp, trc, txp, typ, tn]
    unfold MIn at hx hy hm
    refine ⟨⟨⟨by simp only [regG, stackguard0Offset]; omega, by simp only [regG, stackguard0Offset, hg]; exact hg2,
        by simp only [stackguard0, stackguard0Offset, regG, regSP, hsp, hg, hgv]; omega,
        by simp only [regG, regSP, stackguard0Offset, hsp, hg]; unfold Apart at hgw; omega⟩,
      ⟨by simp only [regSP, hsp]; omega, by simp only [regSP, hsp]; omega, by simp only [regSP, hsp]; exact hwacc⟩,
      hal, hwrt, hgw, hgrt, hLs, hx15, hdf, ⟨by rw [hfs']; exact hfs, by rw [hfs']; exact htacc,
        by rw [hfs', htg, regG, hg]⟩, by rw [hfs']; exact htw, by rw [hfs']; exact htrt⟩,
      rm, rn, rmc, rk, rn', rfl, rfl, rfl, hn, hrc, hrc', hmc, hmc', hracc, hrp, hrh, hrw, hgr, by rw [hfs']; exact htr,
      hadx, ⟨hxa, hx⟩, ⟨hya, hy⟩, ⟨hma, hm⟩, hrx, hry, hrm, hinv, hok1, hok2⟩
  · obtain ⟨hregs, hp⟩ := hp
    obtain ⟨hsp, hg, -⟩ := hd
    unfold Mont.Post at hp
    rw [hsp, hg, trp, trc, txp, typ] at hp
    obtain ⟨efs, edf, e0, e1, e2, ev, L', b', rfl, rfl, hi, hf, hl⟩ := hp
    exact ⟨hregs, efs, edf, e0, by rw [← tn] at e1; exact BitVec.eq_of_toNat_eq e1, e2, ev, hi, hf, hl⟩

end FvModexp.Amd64.MontW
