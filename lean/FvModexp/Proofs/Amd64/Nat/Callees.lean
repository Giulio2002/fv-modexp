import FvModexp.Proofs.Amd64.Conv
import FvModexp.Proofs.Common.DivmcMem

/-!
# Callees of the mul/div layer owned by other agents (amd64): the statements divmc assumes

The amd64 twin of `FvModexp.Arm64.Callees` (see there and /srv/fv-modexp-ops/NOTES-divmc.md). Go ABIInternal on amd64:
arguments in `RAX, RBX, RCX, RDI, RSI, R8, R9, R10, R11` (`s.regs 0, 3, 1, 7, 6, 8, 9, 10, 11`), `g = R14`,
`RSP = s.regs 4`; a summary's stack window `[RSP - stk, RSP + above)` includes the return-address slot.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Contracts
open Janus.Contracts.EqHashModel


namespace FvModexp.Amd64.Callees

/-- `CallEnv` without `DataLoaded` (see the arm64 twin), WITH the TLS slot (`TlsG`: Go code reloads `R14` from
`FS:-8` after every ABI0 call; PROPOSAL to top, NOTES-divmc.md): readable, holding `g`, outside `R.rt`, apart from
the window. -/
abbrev CallEnvND (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above : Nat) : Prop :=
  StackGuardOK s stk ∧ StackWritable s stk above ∧ (s.regs 4).toNat % 8 = 0 ∧
    Outside ((s.regs 4).toNat - stk) (stk + above) R.rt ∧
    Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - stk) (stk + above) ∧
    Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    LiveSep L (win s stk above) ∧
    TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 R.rt ∧ Apart (s.fsBase.toNat - 8) 8 ((s.regs 4).toNat - stk) (stk + above)

/-- The name inclusion of `codeIn_restrict_mono64`, from a decidable check. -/
theorem sub_of_all {ns ms : List String} (h : ns.all ms.contains = true) :
    ∀ x, ns.contains x = true → ms.contains x = true := by
  intro x hx
  simp only [List.all_eq_true] at h
  exact h x (by simpa using hx)

/-- A fetch from one segment of a pairwise-apart code layout is a fetch from the layout (amd64). -/
theorem fetchIn_of_mem {segs : List Amd64.Segment} {seg : Amd64.Segment}
    (hp : segs.Pairwise Amd64.Segment.Apart) (hm : seg ∈ segs) {pc : Nat} {w : List Nat}
    (h : Amd64.Program.fetchIn [seg] pc = some w) : Amd64.Program.fetchIn segs pc = some w := by
  have hin : seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length := by
    simp only [Amd64.Program.fetchIn] at h; split at h
    · assumption
    · simp at h
  induction segs with
  | nil => simp at hm
  | cons x rest ih =>
    rcases List.mem_cons.1 hm with rfl | hm'
    · simp only [Amd64.Program.fetchIn] at h ⊢; rw [if_pos hin] at h ⊢; exact h
    · have hap := (List.pairwise_cons.1 hp).1 seg hm'
      unfold Amd64.Segment.Apart at hap
      simp only [Amd64.Program.fetchIn]; rw [if_neg (by omega)]
      exact ih (List.pairwise_cons.1 hp).2 hm'

/-- A one-segment library program (agent asm's `Lib.*Amd64`) is code of a restricted program containing that segment. -/
theorem codeIn_single {P lp : Amd64.Program} {impl : List Amd64.Segment} (hap : Amd64.ImplApart P impl)
    {ns : List String} {seg : Amd64.Segment} (hl : lp.segments = [seg]) (hm : seg ∈ P.segments)
    (hn : ns.contains seg.name = true) : CodeIn64 lp ((P.onlySegments ns).link impl) := by
  intro pc w hf
  have hf' : Amd64.Program.fetchIn [seg] pc = some w := by rw [← hl]; exact hf
  have hin : seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length := by
    simp only [Amd64.Program.fetchIn] at hf'; split at hf'
    · assumption
    · simp at hf'
  have hmem : seg ∈ (P.segments.filter fun s => ns.contains s.name) ++ impl :=
    List.mem_append_left _ (List.mem_filter.2 ⟨hm, hn⟩)
  have hpw : ((P.segments.filter fun s => ns.contains s.name) ++ impl).Pairwise Amd64.Segment.Apart :=
    hap.1.sublist ((List.filter_sublist).append_right impl)
  obtain ⟨h1, h2⟩ := hap.2 seg (List.mem_append_left _ hm) (pc - seg.base) (by omega)
  rw [show seg.base + (pc - seg.base) = pc by omega] at h1 h2
  exact ⟨fetchIn_of_mem hpw hmem hf', h1, h2⟩

theorem Ensures.toSummaryRegs7 {p0 P : Amd64.Program} {entry : Nat}
    {pre : W64 → W64 → W64 → W64 → W64 → W64 → W64 → State → Prop}
    {post : W64 → W64 → W64 → W64 → W64 → W64 → W64 → State → State → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6, Ensures p0 entry [a0, a1, a2, a3, a4, a5, a6] (pre a0 a1 a2 a3 a4 a5 a6)
      (post a0 a1 a2 a3 a4 a5 a6))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn64 p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.mem.readLE (s.regs regSP).toNat 8) ∧ s.xmm xmmZero = 0 ∧ s.df = false ∧
        pre (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9) s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧
        s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        post (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9) s s') := by
  intro s hpc ⟨hret, hz, hdf, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (s.regs 6) (s.regs 8) (s.regs 9))
    hx (by simp [numIntRegs]) hc s hpc ⟨hret, hz, by simp [ArgsFrom64, argReg, intArgRegs], hdf, hpre⟩

/-- An ABI0 leaf whose writes `rs s` are held keeps the runtime invariant and the stack-guard word. -/
theorem Summary0.live {p : Amd64.Program} {e : Nat} {pre : State → Prop} {Q : State → Memory → Prop}
    (h : Summary0 p e pre Q) (rs : State → List (Nat × Nat))
    (hrs : ∀ s m, pre s → Q s m → MemFrame s.mem m (rs s)) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) :
    Summary0 p e (fun s => pre s ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ rs s, Outside r.1 (r.2 - r.1) R.rt ∨ InRanges r.1 (r.2 - r.1) L) ∧
        Outside ((s.regs 14).toNat + 16) 8 (rs s) ∧ Outside (s.fsBase.toNat - 8) 8 (rs s))
      (fun s m => Q s m ∧ R.inv b L (s.regs 14).toNat (view R.rt L m) ∧
        m.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 ∧
        m.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8) :=
  Summary0.mono h (fun _ hp => hp.1) fun s m ⟨hp, hi, hh, hg, ht⟩ hq =>
    ⟨hq, RtInv.inv_frame' (hrs s m hp hq) hh hi, (hrs s m hp hq).readLE _ _ hg, (hrs s m hp hq).readLE _ _ ht⟩

/-! ## `addVV.abi0` (asm; `FvModexp.Amd64.AddVVSum.addVV_summary`) -/

def addVVfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addVV.abi0"

/-- = asm `AddVVSum.Ctx` (amd64: frame words above the return address). -/
structure VVCtx (s : State) (z x y n : Nat) : Prop where
  hz : s.mem.readLE ((s.regs 4).toNat + 8) 8 = z
  hn : s.mem.readLE ((s.regs 4).toNat + 16) 8 = n
  hx : s.mem.readLE ((s.regs 4).toNat + 32) 8 = x
  hy : s.mem.readLE ((s.regs 4).toNat + 56) 8 = y
  hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  fb : (s.regs 4).toNat + 88 ≤ 2 ^ 48
  facc : s.mem.accessible (s.regs 4).toNat 88 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  accy : s.mem.accessible y (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  aly : z = y ∨ Apart z (8 * n) y (8 * n)
  azf : Apart z (8 * n) (s.regs 4).toNat 88

/-- = asm `AddVVSum.Pre`. -/
def VVPre (s : State) : Prop :=
  VVCtx s (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 32) 8)
    (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)

/-- = asm `AddVVSum.Q` (`lv` = `natVal`). -/
abbrev VVQ (s : State) (m : Memory) : Prop :=
  natVal m (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) =
      (natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) +
        natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)) %
        2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  m.readLE ((s.regs 4).toNat + 80) 8 =
      (natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) +
        natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)) /
        2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)]

def AddVVHyp (impl : List Amd64.Segment) : Prop :=
  Summary0 ((Extracted.program.onlySegments [addVVfn]).link impl) (segAddr Extracted.program addVVfn) VVPre VVQ

abbrev VVLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  VVPre s ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
    Outside ((s.regs 4).toNat + 80) 8 R.rt ∧
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      ((s.regs 14).toNat + 16) 8 ∧
    Apart ((s.regs 4).toNat + 80) 8 ((s.regs 14).toNat + 16) 8 ∧
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.fsBase.toNat - 8) 8 ∧
    Apart ((s.regs 4).toNat + 80) 8 (s.fsBase.toNat - 8) 8

abbrev VVLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  VVQ s m ∧ R.inv b L (s.regs 14).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 ∧
    m.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8

theorem AddVVHyp.live {P : Amd64.Program} (h : Summary0 P (segAddr Extracted.program addVVfn) VVPre VVQ) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) :
    Summary0 P (segAddr Extracted.program addVVfn) (VVLPre R b L) (VVLQ R b L) := by
  refine Summary0.mono (Summary0.live h (fun s => [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)]) (fun s m _ hq => hq.2.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2, ha3, ha4⟩
  refine ⟨hp, hi, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega
  · simp only [Outside, and_true]; unfold Apart at ha3 ha4; omega

/-! ## `subVV.abi0` (asm; `FvModexp.Amd64.SubVVSum.subVV_summary`) -/

def subVVfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.subVV.abi0"

abbrev SubVVQ (s : State) (m : Memory) : Prop :=
  natVal m (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) +
      natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) =
    natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) +
      2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) * m.readLE ((s.regs 4).toNat + 80) 8 ∧
  m.readLE ((s.regs 4).toNat + 80) 8 =
    (if natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) <
        natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) then 1 else 0) ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)]

def SubVVHyp (impl : List Amd64.Segment) : Prop :=
  Summary0 ((Extracted.program.onlySegments [subVVfn]).link impl) (segAddr Extracted.program subVVfn) VVPre SubVVQ

abbrev SubVVLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  SubVVQ s m ∧ R.inv b L (s.regs 14).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 ∧
    m.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8

theorem SubVVHyp.live {P : Amd64.Program} (h : Summary0 P (segAddr Extracted.program subVVfn) VVPre SubVVQ) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) :
    Summary0 P (segAddr Extracted.program subVVfn) (VVLPre R b L) (SubVVLQ R b L) := by
  refine Summary0.mono (Summary0.live h (fun s => [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 80, (s.regs 4).toNat + 88)]) (fun s m _ hq => hq.2.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2, ha3, ha4⟩
  refine ⟨hp, hi, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega
  · simp only [Outside, and_true]; unfold Apart at ha3 ha4; omega

/-! ## `addMulVVWW.abi0` (asm; `FvModexp.Amd64.AddMulVVWWSum`, asm work in progress 2026-11-11) -/

def addMulVVWWfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addMulVVWW.abi0"

/-- `math/big.hasADX` (asm `AddMulVVWWSum.adxAddr`): the byte the function reads to pick its code path. -/
abbrev adxAddr : Nat := 0xbb6b8a

/-- = asm `AddMulVVWWSum.Ctx` (amd64). -/
structure VVWWCtx (s : State) (z x y n m a : Nat) : Prop where
  hz : s.mem.readLE ((s.regs 4).toNat + 8) 8 = z
  hn : s.mem.readLE ((s.regs 4).toNat + 16) 8 = n
  hx : s.mem.readLE ((s.regs 4).toNat + 32) 8 = x
  hy : s.mem.readLE ((s.regs 4).toNat + 56) 8 = y
  hm : s.mem.readLE ((s.regs 4).toNat + 80) 8 = m
  ha : s.mem.readLE ((s.regs 4).toNat + 88) 8 = a
  hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47
  fb : (s.regs 4).toNat + 104 ≤ 2 ^ 48
  facc : s.mem.accessible (s.regs 4).toNat 104 true = true
  adx : s.mem.accessible adxAddr 1 false = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  accy : s.mem.accessible y (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  aly : z = y ∨ Apart z (8 * n) y (8 * n)
  azf : Apart z (8 * n) (s.regs 4).toNat 104

def VVWWPre (s : State) : Prop :=
  VVWWCtx s (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 32) 8)
    (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8)
    (s.mem.readLE ((s.regs 4).toNat + 80) 8) (s.mem.readLE ((s.regs 4).toNat + 88) 8)

abbrev VVWWQ (s : State) (m : Memory) : Prop :=
  natVal m (s.mem.readLE ((s.regs 4).toNat + 8) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) +
      2 ^ (64 * s.mem.readLE ((s.regs 4).toNat + 16) 8) * m.readLE ((s.regs 4).toNat + 96) 8 =
    natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 32) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) +
      natVal s.mem (s.mem.readLE ((s.regs 4).toNat + 56) 8) (s.mem.readLE ((s.regs 4).toNat + 16) 8) *
        s.mem.readLE ((s.regs 4).toNat + 80) 8 + s.mem.readLE ((s.regs 4).toNat + 88) 8 ∧
  MemFrame s.mem m [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 96, (s.regs 4).toNat + 104)]

def AddMulVVWWHyp (impl : List Amd64.Segment) : Prop :=
  Summary0 ((Extracted.program.onlySegments [addMulVVWWfn]).link impl) (segAddr Extracted.program addMulVVWWfn)
    VVWWPre VVWWQ

abbrev VVWWLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  VVWWPre s ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8) ∧
    Outside ((s.regs 4).toNat + 96) 8 R.rt ∧
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      ((s.regs 14).toNat + 16) 8 ∧
    Apart ((s.regs 4).toNat + 96) 8 ((s.regs 14).toNat + 16) 8 ∧
    Apart (s.mem.readLE ((s.regs 4).toNat + 8) 8) (8 * s.mem.readLE ((s.regs 4).toNat + 16) 8)
      (s.fsBase.toNat - 8) 8 ∧
    Apart ((s.regs 4).toNat + 96) 8 (s.fsBase.toNat - 8) 8

abbrev VVWWLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  VVWWQ s m ∧ R.inv b L (s.regs 14).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 ∧
    m.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8

theorem AddMulVVWWHyp.live {P : Amd64.Program}
    (h : Summary0 P (segAddr Extracted.program addMulVVWWfn) VVWWPre VVWWQ) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) :
    Summary0 P (segAddr Extracted.program addMulVVWWfn) (VVWWLPre R b L) (VVWWLQ R b L) := by
  refine Summary0.mono (Summary0.live h (fun s => [(s.mem.readLE ((s.regs 4).toNat + 8) 8,
      s.mem.readLE ((s.regs 4).toNat + 8) 8 + 8 * s.mem.readLE ((s.regs 4).toNat + 16) 8),
      ((s.regs 4).toNat + 96, (s.regs 4).toNat + 104)]) (fun s m _ hq => hq.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2, ha3, ha4⟩
  refine ⟨hp, hi, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega
  · simp only [Outside, and_true]; unfold Apart at ha3 ha4; omega

/-! ## `addVW` (asm; Go ABIInternal; PLANNED shape, as arm64) -/

def addVWfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addVW"

def VWMoves (R : RtInv) (zp zl zc xp xc : Nat) : Prop :=
  ∀ j, 1 ≤ j → j ≤ zl →
    R.ok (cA "runtime.memmove") [if j < zc then zp + 8 * j else zp, if j < xc then xp + 8 * j else xp, 8 * (zl - j)]

/- `addVW` itself: asm's `FvModexp.<Isa>.AddVW.ens` (Proofs/<Isa>/Nat/AddVW.lean), used directly by the callers. -/

end FvModexp.Amd64.Callees
