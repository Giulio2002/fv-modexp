import FvModexp.Proofs.Arm64.Conv
import FvModexp.Proofs.Common.DivmcMem

/-!
# Callees of the mul/div layer owned by other agents (arm64): the statements divmc assumes

Hypothesis-first (CONVENTIONS §4): until the owners' theorems land, the divmc summaries take the callees' theorems
as premises with the shape below. Each is the statement the owner's theorem has (asm: `addVV.abi0` …, copied
from /srv/fv-modexp-asm `Proofs/Arm64/AddVVSum.lean` with `lv` = `natVal`, definitionally equal) or, where the
owner has not written one yet, the shape divmc needs (marked PLANNED; recorded in /srv/fv-modexp-ops/NOTES-divmc.md).

Also: `Ensures.toSummaryRegs6/7` — an internal callee's `Ensures` (for all argument words) as a `Summary` whose
argument words are the call state's registers, so `janus_run … calls [S]` needs no explicit arguments.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.Callees

/-- `CallEnv` without `DataLoaded` (PROPOSAL to top, NOTES-divmc.md): a summary's postcondition gives only a
`MemFrame`, which keeps accessibility but not the region list `DataLoaded` is about, so a caller cannot re-establish
`DataLoaded` after its first call. The mul/div functions read no read-only data on their non-panicking paths. -/
abbrev CallEnvND (R : RtInv) (L : List (Nat × Nat)) (s : State) (stk above : Nat) : Prop :=
  GuardOK s stk ∧ StackOK s stk above ∧
    Outside (s.sp.toNat - stk) (stk + above) R.rt ∧
    Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - stk) (stk + above) ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    LiveSep L (win s stk above)

/-- A fetch from one segment of a pairwise-apart code layout is a fetch from the layout. -/
theorem fetchIn_of_mem {segs : List Segment} {seg : Segment} (hp : segs.Pairwise Segment.Apart)
    (hm : seg ∈ segs) {pc w : Nat} (h : Program.fetchIn [seg] pc = some w) : Program.fetchIn segs pc = some w := by
  obtain ⟨s1, hs1, i, hi, hpc⟩ := Program.fetchIn_index h
  have e : s1 = seg := by simpa using hs1
  rw [e] at hi hpc; subst hpc
  induction segs with
  | nil => simp at hm
  | cons x rest ih =>
    rcases List.mem_cons.1 hm with rfl | hm'
    · rw [Program.fetchIn_cons]; rw [Program.fetchIn_cons] at h
      rw [if_pos (by omega)] at h ⊢
      cases hw : seg.words[(seg.base + 4 * i - seg.base) / 4]? with
      | none => rw [hw] at h; simp [Program.fetchIn] at h
      | some v => rw [hw] at h; exact h
    · have hap := (List.pairwise_cons.1 hp).1 seg hm'
      unfold Segment.Apart at hap
      rw [Program.fetchIn_cons_miss (by omega)]
      exact ih (List.pairwise_cons.1 hp).2 hm'

/-- **A one-segment library program (agent asm's `Lib.*`) is code of a restricted program containing that segment.** -/
theorem codeIn_single {P lp : Program} {impl : List Segment} (hap : ImplApart P impl) {ns : List String}
    {seg : Segment} (hl : lp.segments = [seg]) (hm : seg ∈ P.segments) (hn : ns.contains seg.name = true) :
    CodeIn lp ((P.onlySegments ns).link impl) := by
  intro pc w hf
  have hf' : Program.fetchIn [seg] pc = some w := by rw [← hl]; exact hf
  obtain ⟨s1, hs1, i, hi, hpc⟩ := Program.fetchIn_index hf'
  have e : s1 = seg := by simpa using hs1
  rw [e] at hi hpc
  have hmem : seg ∈ (P.segments.filter fun s => ns.contains s.name) ++ impl :=
    List.mem_append_left _ (List.mem_filter.2 ⟨hm, hn⟩)
  have hpw : ((P.segments.filter fun s => ns.contains s.name) ++ impl).Pairwise Segment.Apart :=
    hap.1.sublist ((List.filter_sublist).append_right impl)
  obtain ⟨h1, h2⟩ := hap.2 seg (List.mem_append_left _ hm) i hi
  subst hpc
  exact ⟨fetchIn_of_mem hpw hmem hf', h1, h2⟩

/-! ## Internal calls with the argument words read from the registers -/

/-- The name inclusion of `codeIn_restrict_mono`, from a decidable check. -/
theorem sub_of_all {ns ms : List String} (h : ns.all ms.contains = true) :
    ∀ x, ns.contains x = true → ms.contains x = true := by
  intro x hx
  simp only [List.all_eq_true] at h
  exact h x (by simpa using hx)

theorem Ensures.toSummaryRegs6 {p0 P : Program} {entry : Nat}
    {pre : W64 → W64 → W64 → W64 → W64 → W64 → State → Prop}
    {post : W64 → W64 → W64 → W64 → W64 → W64 → State → State → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5, Ensures p0 entry [a0, a1, a2, a3, a4, a5] (pre a0 a1 a2 a3 a4 a5)
      (post a0 a1 a2 a3 a4 a5))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.regs 30).toNat ∧
        pre (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 18 = s.regs 18) ∧
        post (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) s s') := by
  intro s hpc ⟨hret, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5)) hx hc s hpc
    ⟨hret, by simp [ArgsFrom], hpre⟩

theorem Ensures.toSummaryRegs7 {p0 P : Program} {entry : Nat}
    {pre : W64 → W64 → W64 → W64 → W64 → W64 → W64 → State → Prop}
    {post : W64 → W64 → W64 → W64 → W64 → W64 → W64 → State → State → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6, Ensures p0 entry [a0, a1, a2, a3, a4, a5, a6] (pre a0 a1 a2 a3 a4 a5 a6)
      (post a0 a1 a2 a3 a4 a5 a6))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.regs 30).toNat ∧
        pre (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6) s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 18 = s.regs 18) ∧
        post (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6) s s') := by
  intro s hpc ⟨hret, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6))
    hx hc s hpc ⟨hret, by simp [ArgsFrom], hpre⟩

/-! ## `addVV.abi0` (asm; `FvModexp.Arm64.AddVVSum.addVV_summary`) -/

def addVVfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addVV.abi0"

/-- = asm `AddVVSum.Ctx` (frame words `z, len, cap, x, len, cap, y, len, cap, c` at `SP + 8 …`). -/
structure VVCtx (s : State) (z x y n : Nat) : Prop where
  hz : s.mem.readLE (s.sp.toNat + 8) 8 = z
  hn : s.mem.readLE (s.sp.toNat + 16) 8 = n
  hx : s.mem.readLE (s.sp.toNat + 32) 8 = x
  hy : s.mem.readLE (s.sp.toNat + 56) 8 = y
  lr4 : (s.regs 30).toNat % 4 = 0
  lr56 : (s.regs 30).toNat < 2 ^ 56
  al : s.sp.toNat % 16 = 0
  fb : s.sp.toNat + 88 ≤ 2 ^ 48
  facc : s.mem.accessible (s.sp.toNat + 8) 80 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  accy : s.mem.accessible y (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  aly : z = y ∨ Apart z (8 * n) y (8 * n)
  azr : Apart z (8 * n) (s.sp.toNat + 80) 8

/-- = asm `AddVVSum.Pre`. -/
def VVPre (s : State) : Prop :=
  VVCtx s (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 56) 8)
    (s.mem.readLE (s.sp.toNat + 16) 8)

/-- = asm `AddVVSum.Q` (`lv` = `natVal`). -/
abbrev VVQ (s : State) (m : Memory) : Prop :=
  natVal m (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) =
      (natVal s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) +
        natVal s.mem (s.mem.readLE (s.sp.toNat + 56) 8) (s.mem.readLE (s.sp.toNat + 16) 8)) %
        2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  m.readLE (s.sp.toNat + 80) 8 =
      (natVal s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) +
        natVal s.mem (s.mem.readLE (s.sp.toNat + 56) 8) (s.mem.readLE (s.sp.toNat + 16) 8)) /
        2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
  MemFrame s.mem m [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8),
      (s.sp.toNat + 80, s.sp.toNat + 88)]

/-- An ABI0 leaf (no runtime call) whose writes `rs s` are held keeps the runtime invariant and the goroutine's
stack-guard word (outside `rs s`): the facts a caller needs to make its next call. -/
theorem Summary0.live {p : Program} {e : Nat} {pre : State → Prop} {Q : State → Memory → Prop}
    (h : Summary0 p e pre Q) (rs : State → List (Nat × Nat))
    (hrs : ∀ s m, pre s → Q s m → MemFrame s.mem m (rs s)) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) :
    Summary0 p e (fun s => pre s ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ rs s, Outside r.1 (r.2 - r.1) R.rt ∨ InRanges r.1 (r.2 - r.1) L) ∧
        Outside ((s.regs 28).toNat + 16) 8 (rs s))
      (fun s m => Q s m ∧ R.inv b L (s.regs 28).toNat (view R.rt L m) ∧
        m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8) :=
  Summary0.mono h (fun _ hp => hp.1) fun s m ⟨hp, hi, hh, hg⟩ hq =>
    ⟨hq, RtInv.inv_frame' (hrs s m hp hq) hh hi, (hrs s m hp hq).readLE _ _ hg⟩

/-- The premise: asm's library summary, moved to `addVV.abi0`'s own code (+ runtime). -/
def AddVVHyp (impl : List Segment) : Prop :=
  Summary0 ((Extracted.program.onlySegments [addVVfn]).link impl) (segAddr Extracted.program addVVfn) VVPre VVQ

/-- `addVV.abi0` with the runtime invariant and the stack guard carried over (`Summary0.live`): the pre adds the
invariant, `z[0:n]` held, the result word outside `R.rt`, both apart from the guard word. -/
abbrev VVLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  VVPre s ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
    Outside (s.sp.toNat + 80) 8 R.rt ∧
    Apart (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ((s.regs 28).toNat + 16) 8 ∧
    Apart (s.sp.toNat + 80) 8 ((s.regs 28).toNat + 16) 8

abbrev VVLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  VVQ s m ∧ R.inv b L (s.regs 28).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8

theorem AddVVHyp.live {P : Program} (h : Summary0 P (segAddr Extracted.program addVVfn) VVPre VVQ) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) :
    Summary0 P (segAddr Extracted.program addVVfn) (VVLPre R b L) (VVLQ R b L) := by
  refine Summary0.mono (Summary0.live h (fun s => [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8),
      (s.sp.toNat + 80, s.sp.toNat + 88)]) (fun s m _ hq => hq.2.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2⟩
  refine ⟨hp, hi, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega

/-! ## `addMulVVWW.abi0` (asm; `FvModexp.Arm64.AddMulVVWWSum`, asm commit 3aa118e) -/

def addMulVVWWfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addMulVVWW.abi0"

/-- = asm `AddMulVVWWSum.Ctx` (frame words `z, len, cap, x, len, cap, y, len, cap, m, a, c` at `SP + 8 …`). -/
structure VVWWCtx (s : State) (z x y n m a : Nat) : Prop where
  hz : s.mem.readLE (s.sp.toNat + 8) 8 = z
  hn : s.mem.readLE (s.sp.toNat + 16) 8 = n
  hx : s.mem.readLE (s.sp.toNat + 32) 8 = x
  hy : s.mem.readLE (s.sp.toNat + 56) 8 = y
  hm : s.mem.readLE (s.sp.toNat + 80) 8 = m
  ha : s.mem.readLE (s.sp.toNat + 88) 8 = a
  lr4 : (s.regs 30).toNat % 4 = 0
  lr56 : (s.regs 30).toNat < 2 ^ 56
  al : s.sp.toNat % 16 = 0
  fb : s.sp.toNat + 104 ≤ 2 ^ 48
  facc : s.mem.accessible (s.sp.toNat + 8) 96 true = true
  accz : s.mem.accessible z (8 * n) true = true
  accx : s.mem.accessible x (8 * n) false = true
  accy : s.mem.accessible y (8 * n) false = true
  alx : z = x ∨ Apart z (8 * n) x (8 * n)
  aly : z = y ∨ Apart z (8 * n) y (8 * n)
  azr : Apart z (8 * n) (s.sp.toNat + 96) 8

/-- = asm `AddMulVVWWSum.Pre`. -/
def VVWWPre (s : State) : Prop :=
  VVWWCtx s (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 56) 8)
    (s.mem.readLE (s.sp.toNat + 16) 8) (s.mem.readLE (s.sp.toNat + 80) 8) (s.mem.readLE (s.sp.toNat + 88) 8)

/-- = asm `AddMulVVWWSum.Q` (`lv` = `natVal`): `Z' + 2^(64 n)·c = X + Y·m + a`. -/
abbrev VVWWQ (s : State) (m : Memory) : Prop :=
  natVal m (s.mem.readLE (s.sp.toNat + 8) 8) (s.mem.readLE (s.sp.toNat + 16) 8) +
      2 ^ (64 * s.mem.readLE (s.sp.toNat + 16) 8) * m.readLE (s.sp.toNat + 96) 8 =
    natVal s.mem (s.mem.readLE (s.sp.toNat + 32) 8) (s.mem.readLE (s.sp.toNat + 16) 8) +
      natVal s.mem (s.mem.readLE (s.sp.toNat + 56) 8) (s.mem.readLE (s.sp.toNat + 16) 8) *
        s.mem.readLE (s.sp.toNat + 80) 8 + s.mem.readLE (s.sp.toNat + 88) 8 ∧
  MemFrame s.mem m [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8), (s.sp.toNat + 96, s.sp.toNat + 104)]

def AddMulVVWWHyp (impl : List Segment) : Prop :=
  Summary0 ((Extracted.program.onlySegments [addMulVVWWfn]).link impl) (segAddr Extracted.program addMulVVWWfn)
    VVWWPre VVWWQ

abbrev VVWWLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  VVWWPre s ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
    Outside (s.sp.toNat + 96) 8 R.rt ∧
    Apart (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ((s.regs 28).toNat + 16) 8 ∧
    Apart (s.sp.toNat + 96) 8 ((s.regs 28).toNat + 16) 8

abbrev VVWWLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  VVWWQ s m ∧ R.inv b L (s.regs 28).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8

theorem AddMulVVWWHyp.live {P : Program}
    (h : Summary0 P (segAddr Extracted.program addMulVVWWfn) VVWWPre VVWWQ) (R : RtInv)
    (b : Nat) (L : List (Nat × Nat)) :
    Summary0 P (segAddr Extracted.program addMulVVWWfn) (VVWWLPre R b L) (VVWWLQ R b L) := by
  refine Summary0.mono (Summary0.live h (fun s => [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8),
      (s.sp.toNat + 96, s.sp.toNat + 104)]) (fun s m _ hq => hq.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2⟩
  refine ⟨hp, hi, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega

/-! ## `addVW` (asm; Go ABIInternal; PLANNED shape) -/

def addVWfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addVW"

/-- The `memmove` requests `addVW(z, x, y)` may make when `z ≠ x` (`copy(z[j:], x[j:])`, `1 ≤ j ≤ len z`; Go keeps
a slice pointer in its array: `z[j:]` points at `z + 8j` only when `j < cap z`). -/
def VWMoves (R : RtInv) (zp zl zc xp xc : Nat) : Prop :=
  ∀ j, 1 ≤ j → j ≤ zl →
    R.ok (cA "runtime.memmove") [if j < zc then zp + 8 * j else zp, if j < xc then xp + 8 * j else xp, 8 * (zl - j)]

/- `addVW` itself: asm's `FvModexp.<Isa>.AddVW.ens` (Proofs/<Isa>/Nat/AddVW.lean), used directly by the callers. -/

end FvModexp.Arm64.Callees
