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

/-- The bytes of the stack a summary may write (arm64): its frames below `SP - 8` and the spill slots above `SP + 8`,
but NOT the words at `SP - 8` (the caller's saved `X29`, stored below the caller's `SP`) and at `SP` (the caller's
saved `X30`), which the caller reloads after the call — as the runtime contracts' `calleeStack`. PROPOSAL to top
(NOTES-divmc.md): CONVENTIONS' `win s stk above = [(SP - stk, SP + above)]` in a `MemFrame` loses both. -/
@[reducible] def winA (s : State) (stk above : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - stk, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + above)]

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

/-! ## `addVW` (asm; Go ABIInternal; PLANNED shape) -/

def addVWfn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.addVW"

/-- The `memmove` requests `addVW(z, x, y)` may make when `z ≠ x` (`copy(z[j:], x[j:])`, `1 ≤ j ≤ len z`; Go keeps
a slice pointer in its array: `z[j:]` points at `z + 8j` only when `j < cap z`). -/
def VWMoves (R : RtInv) (zp zl zc xp xc : Nat) : Prop :=
  ∀ j, 1 ≤ j → j ≤ zl →
    R.ok (cA "runtime.memmove") [if j < zc then zp + 8 * j else zp, if j < xc then xp + 8 * j else xp, 8 * (zl - j)]

/-- `addVW(z, x []Word, y Word) (c Word)` (arith.go:103): `z = x + y` over `len z = len x` limbs, carry out. Frame 48,
`memmove` (4096) → `stk = 4144`; spills `X0`, `X3` (`above = 32`). -/
def AddVWEns (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc y : W64) : Prop :=
  Ensures ((Extracted.program.onlySegments [addVWfn]).link impl) (segAddr Extracted.program addVWfn)
    [zp, zl, zc, xp, xl, xc, y]
    (fun s => CallEnvND R L s 4144 32 ∧ xl = zl ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat ≤ xc.toNat ∧
      NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4144 32) ∧
      s.mem.accessible xp.toNat (8 * zl.toNat) false = true ∧ xp.toNat + 8 * zl.toNat ≤ 2 ^ 48 ∧
      Held R L xp.toNat (8 * zl.toNat) ∧ Outside xp.toNat (8 * zl.toNat) (win s 4144 32) ∧
      (zp = xp ∨ Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * zl.toNat)) ∧
      R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
      (if zp = xp then True else VWMoves R zp.toNat zl.toNat zc.toNat xp.toNat xc.toNat))
    (fun s s' => (s'.regs 0).toNat = (natVal s.mem xp.toNat zl.toNat + y.toNat) / 2 ^ (64 * zl.toNat) ∧
      natVal s'.mem zp.toNat zl.toNat = (natVal s.mem xp.toNat zl.toNat + y.toNat) % 2 ^ (64 * zl.toNat) ∧
      ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
        R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
        MemFrame s.mem s'.mem (R.rt ++ winA s 4144 32 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
        LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)])

end FvModexp.Arm64.Callees
