import FvModexp.Proofs.Arm64.Nat.LibMulAddWW
import FvModexp.Proofs.Arm64.Nat.NatAddMid
import FvModexp.Proofs.Arm64.MulAddVWWSum

/-!
# `nat.mulAddWW` (go-bigmodexpfix natmul.go:136), arm64: statement, callee, segment-boundary facts

```go
func (z nat) mulAddWW(x nat, y, r Word) nat {
	m := len(x)
	if m == 0 || y == 0 {
		return z.setWord(r) // result is r
	}
	z = z.make(m + 1)
	z[m] = mulAddVWW(z[0:m], x, y, r)
	return z.norm()
}
```
(`setWord`, `make`, `norm` nat.go:49-78 are inlined.) Arguments `R0..R2 = z`, `R3..R5 = x`, `R6 = y`, `R7 = r`.
Frame 112 (`MOVD.W R30, -112(RSP)`; entry `SP`, `SP' = SP - 112`): saved `X30` at `SP - 112`, `X29` at `SP - 120`;
locals `80(RSP') = SP - 32` (cap), `88(RSP') = SP - 24` (`m + 1`), `96(RSP') = SP - 16` (p); spills
`120, 144, 152, 160, 168, 176(RSP')` = `SP + 8, 32, 40, 48, 56, 64` (`above = 72`). Calls: `runtime.makeslice`
(`make(nat, m + 1, m + 5)` / `make(nat, 1)`, contract stack 4096 below `SP'`: `stk = 112 + 4096 = 4208`) and
`mulAddVWW.abi0` (asm, NOSPLIT, frame words `8 … 72(RSP')`, result `72(RSP') = SP - 40`).

The real call site: `nat.mul` natmul.go:26 `z.mulAddWW(x, y[0], 0)` BEFORE `nat.mul`'s alias check, so `z` may be `x`
(same array): the precondition allows `zp = xp` or `z`'s array apart from `x`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)

namespace FvModexp.Arm64.MulAddWW

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mulAddWW"
def vwwFn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.mulAddVWW.abi0"
def names : List String := LibMulAddWW.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- The capacity `mulAddWW` needs: `m + 1` (`make(m + 1)`), or `setWord(r)`'s `1` (`0` for `r = 0`). -/
@[reducible] def need (xl y r : BitVec 64) : Nat :=
  if xl.toNat = 0 ∨ y.toNat = 0 then (if r.toNat = 0 then 0 else 1) else xl.toNat + 1

/-- The precondition (the one `makeslice` request when `z` is too small). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4208 72 ∧ Outside wordT 16 R.rt ∧ xl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    Outside zp.toNat (8 * zc.toNat) (win s 4208 72) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4208 72) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < need xl y r → R.ok (cA "runtime.makeslice") [wordT, need xl y r, makeCap (need xl y r)] ∧
      makeCost (need xl y r) ≤ b)

/-- The postcondition: a normalised nat `(p', n', c')` holding `X·y + r`, `z`'s array or a fresh one. -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y r : BitVec 64) (s s' : State) :
    Prop :=
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 1).toNat = n' ∧ (s'.regs 2).toNat = c' ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ xl.toNat + 1 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost (need xl y r) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

/-- The registers every path keeps. -/
@[reducible] def Keep (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18

/-! ## The callee `mulAddVWW.abi0`, moved into the restricted program -/

theorem fetchIn_cons_cases {A : Segment} {rest : List Segment} {pc w : Nat}
    (h : Program.fetchIn (A :: rest) pc = some w) :
    Program.fetchIn [A] pc = some w ∨ Program.fetchIn rest pc = some w := by
  rw [Program.fetchIn_cons] at h
  rw [Program.fetchIn_cons]
  split at h
  · rename_i hc
    rw [if_pos hc]
    split at h
    · left; exact h
    · right; exact h
  · right; exact h

theorem fetchIn_some_mem : ∀ {segs : List Segment} {pc w : Nat}, Program.fetchIn segs pc = some w →
    ∃ seg ∈ segs, Program.fetchIn [seg] pc = some w
  | [], _, _, h => by simp [Program.fetchIn] at h
  | A :: rest, _, _, h => by
    rcases fetchIn_cons_cases h with h1 | h1
    · exact ⟨A, List.mem_cons_self .., h1⟩
    · obtain ⟨seg, hm, hs⟩ := fetchIn_some_mem h1
      exact ⟨seg, List.mem_cons_of_mem _ hm, hs⟩

theorem codeIn_lib (impl : List Segment) (hap : ImplApart Extracted.program impl) {lp : Program}
    (hm : ∀ seg ∈ lp.segments, seg ∈ Extracted.program.segments ∧ names.contains seg.name = true) :
    CodeIn lp (LibMulAddWW.program.link impl) := by
  rw [LibMulAddWW.eq_only]
  intro pc w hf
  obtain ⟨seg, hseg, hf'⟩ := fetchIn_some_mem (segs := lp.segments) hf
  obtain ⟨hm1, hm2⟩ := hm seg hseg
  exact Callees.codeIn_single (lp := { lp with segments := [seg] }) hap rfl hm1 hm2 pc w hf'

set_option maxRecDepth 100000 in
theorem codeIn_vww (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    CodeIn FvModexp.Lib.MulAddVWWA64.program (LibMulAddWW.program.link impl) := by
  refine codeIn_lib impl hap ?_
  have e : FvModexp.Lib.MulAddVWWA64.program.segments = [Extracted.seg64] := rfl
  rw [e]; intro seg hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
  exact ⟨List.getElem_mem (l := Extracted.program.segments) (n := 64) (by decide), by decide⟩

/-- `mulAddVWW.abi0` with the runtime invariant and the stack guard carried over: `z[0:n]` held, the result word
outside `R.rt`, both apart from the guard word. -/
abbrev VLPre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) : Prop :=
  MulAddVWWSum.Pre s ∧ R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    Held R L (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ∧
    Outside (s.sp.toNat + 72) 8 R.rt ∧
    Apart (s.mem.readLE (s.sp.toNat + 8) 8) (8 * s.mem.readLE (s.sp.toNat + 16) 8) ((s.regs 28).toNat + 16) 8 ∧
    Apart (s.sp.toNat + 72) 8 ((s.regs 28).toNat + 16) 8

abbrev VLQ (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (s : State) (m : Memory) : Prop :=
  MulAddVWWSum.Q s m ∧ R.inv b L (s.regs 28).toNat (view R.rt L m) ∧
    m.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8

theorem vww_live (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibMulAddWW.program.link impl) (segAddr Extracted.program vwwFn) (VLPre R b L) (VLQ R b L) := by
  have he : segAddr Extracted.program vwwFn = FvModexp.Lib.MulAddVWWA64.entry := by decide
  rw [he]
  have h0 := EqHashModel.Summary.of_codeIn (codeIn_vww impl hap) MulAddVWWSum.mulAddVWW_summary
  refine Summary0.mono (Callees.Summary0.live h0 (fun s => [(s.mem.readLE (s.sp.toNat + 8) 8,
      s.mem.readLE (s.sp.toNat + 8) 8 + 8 * s.mem.readLE (s.sp.toNat + 16) 8),
      (s.sp.toNat + 72, s.sp.toNat + 80)]) (fun s m _ hq => hq.2.2) R b L) ?_ (fun _ _ _ hq => hq)
  intro s ⟨hp, hi, hh, ho, ha1, ha2⟩
  refine ⟨hp, hi, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Nat.add_sub_cancel_left]; exact hh.symm
    · left; simpa using ho
  · simp only [Outside, and_true]; unfold Apart at ha1 ha2; omega

/-! ## The facts after `z.make(m + 1)` (`Mid`) -/

/-- The join of the reuse and allocation paths of `z.make(m + 1)` (`CMP R2, R4`). -/
abbrev hMid : Nat := segAddr Extracted.program fn + 0x7c

/-- The segment-boundary facts after the result array `(p, c)` is chosen. -/
structure Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl : BitVec 64) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory) : Prop where
  gok : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4208 < s.sp.toNat
  g48 : (s.regs 28).toNat + 24 ≤ 2 ^ 48
  al : s.sp.toNat % 16 = 0
  sp0 : 4208 ≤ s.sp.toNat
  sp1 : s.sp.toNat + 72 ≤ 2 ^ 48
  wrt : Outside (s.sp.toNat - 4208) (4208 + 72) R.rt
  gw : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4208) (4208 + 72)
  grt : Outside ((s.regs 28).toNat + 16) 8 R.rt
  lr4 : (s.regs 30).toNat % 4 = 0
  lr48 : (s.regs 30).toNat < 2 ^ 48
  xl40 : xl.toNat < 2 ^ 40
  -- frame words and spills
  lr : M.readLE (s.sp.toNat - 112) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat
  sm : M.readLE (s.sp.toNat + 40) 8 = xl.toNat
  sm1 : M.readLE (s.sp.toNat - 24) 8 = xl.toNat + 1
  sacc : M.accessible (s.sp.toNat - 4208) (4208 + 72) true = true
  gacc : M.accessible ((s.regs 28).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8
  -- the result array
  cap : xl.toNat + 1 ≤ c
  c41 : c < 2 ^ 41
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) (s.sp.toNat - 4208) (4208 + 72)
  pg : Apart p (8 * c) ((s.regs 28).toNat + 16) 8
  pheld : Held R L' p (8 * c)
  px : p = xp.toNat ∨ Apart p (8 * c) xp.toNat (8 * xl.toNat)
  -- the operand
  xacc : M.accessible xp.toNat (8 * xl.toNat) false = true
  x48 : xp.toNat + 8 * xl.toNat ≤ 2 ^ 48
  -- runtime
  ext : LiveExt R L L'
  bud : b - makeCost (xl.toNat + 1) ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M)
  ror : (p = zp.toNat ∧ c = zc.toNat) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  lsep : ∀ r ∈ L, Outside r.1 (r.2 - r.1) (win s 4208 72)
  mf : MemFrame s.mem M (R.rt ++ winA s 4208 72 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)])
  lf : LiveFrame s.mem M L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

/-- The stack ranges and array parts the code after `Mid` writes. -/
def WsOK (s : State) (p c : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ r ∈ ws, r.1 ≤ r.2 ∧ ((s.sp.toNat - 104 ≤ r.1 ∧ r.2 ≤ s.sp.toNat - 24) ∨ (s.sp.toNat - 16 ≤ r.1 ∧ r.2 ≤ s.sp.toNat - 8) ∨
    (p ≤ r.1 ∧ r.2 ≤ p + 8 * c))

/-- **A write without allocation keeps `Mid`** (stack stores, `mulAddVWW.abi0`, `z[m] = c`). -/
theorem Mid.frame0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) {M2 : Memory} {ws : List (Nat × Nat)}
    (hws : WsOK s p c ws) (hf : MemFrame M M2 ws) :
    Mid R b L zp zc xp xl s p c L' b' M2 := by
  have hpw := h.pw; have hgw := h.gw; have hpg := h.pg; have hsp0 := h.sp0
  unfold Apart at hpw hgw hpg
  have rd : ∀ a, (s.sp.toNat - 120 ≤ a ∧ a + 8 ≤ s.sp.toNat - 104 ∨ s.sp.toNat - 24 ≤ a ∧ a + 8 ≤ s.sp.toNat - 16 ∨
      s.sp.toNat + 8 ≤ a ∧ a + 8 ≤ s.sp.toNat + 72) → M2.readLE a 8 = M.readLE a 8 := by
    intro a ha
    refine hf.readLE a 8 (outside_of_forall fun r hr => ?_)
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  have hinv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M2) := by
    refine RtInv.inv_frame' hf (fun r hr => ?_) h.inv
    have h0 := (hws r hr).1
    rcases (hws r hr).2 with h' | h' | h'
    · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
    · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
    · exact (h.pheld.sub h'.1 (by omega)).symm
  refine { h with
      lr := by rw [rd _ (by omega)]; exact h.lr
      fp := by rw [rd _ (by omega)]; exact h.fp
      sm := by rw [rd _ (by omega)]; exact h.sm
      sm1 := by rw [rd _ (by omega)]; exact h.sm1
      sacc := by rw [hf.accessible]; exact h.sacc
      gacc := by rw [hf.accessible]; exact h.gacc
      grd := ?_
      pacc := by rw [hf.accessible]; exact h.pacc
      xacc := by rw [hf.accessible]; exact h.xacc
      inv := hinv
      mf := ?_
      lf := ?_ }
  · rw [← h.grd]
    refine hf.readLE _ _ (outside_of_forall fun r hr => ?_)
    rcases (hws r hr).2 with h' | h' | h' <;> omega
  · refine h.mf.trans (hf.widen R.rt) fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1, hw2⟩, hz⟩ := ho
    refine ⟨hrt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h'
    · omega
    · omega
    · rcases h.ror with ⟨rfl, rfl⟩ | ⟨hin, -⟩
      · omega
      · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hf.readLE a n (outside_of_forall fun r hr => ?_)]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      have hsep := h.lsep q hq
      simp only [win, outside_cons, outside_nil, and_true] at hsep hz
      rcases (hws r hr).2 with h' | h' | h'
      · omega
      · omega
      · rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hap⟩
        · omega
        · have := hap q hq; unfold Apart at this; omega

/-- **The postcondition** from `Mid` at the return (`s'.mem = M`, result `(p, n', c)`). -/
theorem Mid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {y r : BitVec 64}
    {s : State} {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) (hx0 : xl.toNat ≠ 0) (hy0 : y.toNat ≠ 0) (s' : State) (n' : Nat)
    (hm : s'.mem = M) (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 1).toNat = n') (h2 : (s'.regs 2).toNat = c)
    (hn : n' ≤ xl.toNat + 1)
    (hv : natVal M p n' = natVal s.mem xp.toNat xl.toNat * y.toNat + r.toNat) (hnorm : NatNorm M p n') :
    Post R b L zp zc xp xl y r s s' := by
  subst hm
  have hneed : need xl y r = xl.toNat + 1 := by unfold need; rw [if_neg (by omega)]
  refine ⟨p, n', c, h0, h1, h2, hv, hnorm, by have := h.cap; omega, hn, L', b', h.ext, ?_, h.inv,
    fun _ => ⟨h.p8, h.pheld, h.pacc, h.p48⟩, h.ror, h.mf, h.lf⟩
  rw [hneed]; exact h.bud

end FvModexp.Arm64.MulAddWW
