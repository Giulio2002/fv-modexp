import FvModexp.Proofs.Arm64.Nat.LibDivW
import FvModexp.Proofs.Arm64.Nat.NatAddMid
import FvModexp.Proofs.Arm64.Nat.DivWVW

/-!
# `nat.divW` (go-bigmodexpfix natdiv.go:550), arm64: statement, callee, segment-boundary facts

```go
func (z nat) divW(x nat, y Word) (q nat, r Word) {
	m := len(x)
	switch {
	case y == 0: panic("division by zero")
	case y == 1: q = z.set(x); return
	case m == 0: q = z[:0]; return
	}
	z = z.make(m)
	r = divWVW(z, 0, x, y)
	q = z.norm()
	return
}
```
(`set`, `make`, `norm` nat.go:49-95 inlined.) Arguments `R0..R2 = z`, `R3..R5 = x`, `R6 = y`; results `R0..R2 = q`,
`R3 = r`. Frame 144 (`MOVD.W R30, -144(RSP)`; `SP' = SP - 144`): saved `X30` at `SP - 144`, `X29` at `SP - 152`;
spills `152, 176, 184, 192, 200(RSP')` = `SP + 8, 32, 40, 48, 56` (`above = 64`); locals of the divWVW path
`80, 88, 120(RSP')` = `SP - 64` (m), `SP - 56` (cap), `SP - 24` (p); of the `set` path `104, 112, 128(RSP')` =
`SP - 40, -32, -16`. Calls: `runtime.makeslice` (`make(nat, m, m + 4)` / `make(nat, 1)`; contract stack 4096 below
`SP'`: `stk = 144 + 4096 = 4240`), `runtime.memmove` (the `copy` of `set`), `divWVW` (asm's summary, stk 152, above 72).
The precondition excludes `y = 0` (panic). `x` normalised (the `y = 1` path returns `z.set(x)` unnormalised).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel
open FvModexp.Arm64.NatAdd (held_keep liveFrame_of_memFrame outside_of_inRanges held_apart_fresh)

namespace FvModexp.Arm64.DivW

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.divW"
def names : List String := LibDivW.names
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

/-- The precondition: `y ≠ 0`, `x` normalised, the `makeslice` request of `z.make(m)` when `z` is too small and the
`memmove` requests of `z.set(x)`. -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4240 64 ∧ Outside wordT 16 R.rt ∧ y.toNat ≠ 0 ∧ xl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    Outside zp.toNat (8 * zc.toNat) (win s 4240 64) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ NatNorm s.mem xp.toNat xl.toNat ∧
    Outside xp.toNat (8 * xl.toNat) (win s 4240 64) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

/-- The postcondition: a normalised nat `(p', n', c')` holding `X / y` (in `z`'s array or a fresh one) and `R3 = X % y`. -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl y : BitVec 64) (s s' : State) :
    Prop :=
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 1).toNat = n' ∧ (s'.regs 2).toNat = c' ∧
    (s'.regs 3).toNat = natVal s.mem xp.toNat xl.toNat % y.toNat ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat / y.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ xl.toNat ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost xl.toNat ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4240 64 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

/-! ## The callee `divWVW`, moved into the restricted program -/

theorem Ensures.toSummaryRegs8 {p0 P : Program} {entry : Nat}
    {pre : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → State → Prop}
    {post : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → State → State → Prop}
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7, Ensures p0 entry [a0, a1, a2, a3, a4, a5, a6, a7]
      (pre a0 a1 a2 a3 a4 a5 a6 a7) (post a0 a1 a2 a3 a4 a5 a6 a7))
    (hx : p0.fetch p0.exitAddr = none) (hc : CodeIn p0 P) :
    Summary P entry
      (fun s => RetAddr p0 (s.regs 30).toNat ∧
        pre (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6) (s.regs 7) s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 18 = s.regs 18) ∧
        post (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6) (s.regs 7) s s') := by
  intro s hpc ⟨hret, hpre⟩
  exact Ensures.toSummaryIn (h (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (s.regs 4) (s.regs 5) (s.regs 6)
    (s.regs 7)) hx hc s hpc ⟨hret, by simp [ArgsFrom], hpre⟩

set_option linter.defProp false in
/-- `divWVW`'s `ens` as a summary inside `LibDivW.program.link impl`. -/
def dvw (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :=
  Ensures.toSummaryRegs8 (fun zp zl zc xn xp xl xc y => DivWVW.ens impl hap R b L zp zl zc xn xp xl xc y)
    (noExit_restrict hap DivWVW.names)
    (show CodeIn ((Extracted.program.onlySegments DivWVW.names).link impl) (LibDivW.program.link impl) by
      rw [LibDivW.eq_only]; exact codeIn_restrict_mono hap (Callees.sub_of_all (by decide)))

/-! ## The facts after `z.make(m)` (`Mid`), shared by the `divWVW` path and the `set` path -/

/-- The segment-boundary facts after the result array `(p, c)` of `z.make(m)` is chosen (`m = len x > 0`). -/
structure Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl : BitVec 64) (s : State)
    (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory) : Prop where
  gok : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4240 < s.sp.toNat
  g48 : (s.regs 28).toNat + 24 ≤ 2 ^ 48
  al : s.sp.toNat % 16 = 0
  sp0 : 4240 ≤ s.sp.toNat
  sp1 : s.sp.toNat + 64 ≤ 2 ^ 48
  wrt : Outside (s.sp.toNat - 4240) (4240 + 64) R.rt
  gw : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4240) (4240 + 64)
  grt : Outside ((s.regs 28).toNat + 16) 8 R.rt
  lr4 : (s.regs 30).toNat % 4 = 0
  lr48 : (s.regs 30).toNat < 2 ^ 48
  xl40 : xl.toNat < 2 ^ 40
  x0 : 0 < xl.toNat
  lr : M.readLE (s.sp.toNat - 144) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 152) 8 = (s.regs 29).toNat
  sacc : M.accessible (s.sp.toNat - 4240) (4240 + 64) true = true
  gacc : M.accessible ((s.regs 28).toNat + 16) 8 false = true
  grd : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8
  cap : xl.toNat ≤ c
  c41 : c < 2 ^ 41
  p8 : p % 8 = 0
  p48 : p + 8 * c ≤ 2 ^ 48
  pacc : M.accessible p (8 * c) true = true
  pw : Apart p (8 * c) (s.sp.toNat - 4240) (4240 + 64)
  pg : Apart p (8 * c) ((s.regs 28).toNat + 16) 8
  pheld : Held R L' p (8 * c)
  px : p = xp.toNat ∨ Apart p (8 * c) xp.toNat (8 * xl.toNat)
  xacc : M.accessible xp.toNat (8 * xl.toNat) false = true
  x48 : xp.toNat + 8 * xl.toNat ≤ 2 ^ 48
  xheld : Held R L' xp.toNat (8 * xl.toNat)
  xw : Apart xp.toNat (8 * xl.toNat) (s.sp.toNat - 4240) (4240 + 64)
  ext : LiveExt R L L'
  bud : b - makeCost xl.toNat ≤ b'
  inv : R.inv b' L' (s.regs 28).toNat (view R.rt L' M)
  lsep : LiveSep L' (win s 4240 64)
  ror : (p = zp.toNat ∧ c = zc.toNat) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)
  mf : MemFrame s.mem M (R.rt ++ winA s 4240 64 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)])
  lf : LiveFrame s.mem M L [(zp.toNat, zp.toNat + 8 * zc.toNat)]
  mv : ∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k]

/-- The stack ranges and array parts the code after `Mid` (and its callees) may write: the window except the saved
`X29`/`X30` words, and the result array. -/
def WsOK (s : State) (p c : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ r ∈ ws, r.1 ≤ r.2 ∧ ((s.sp.toNat - 4240 ≤ r.1 ∧ r.2 ≤ s.sp.toNat - 152) ∨
    (s.sp.toNat - 136 ≤ r.1 ∧ r.2 ≤ s.sp.toNat - 8) ∨ (s.sp.toNat + 8 ≤ r.1 ∧ r.2 ≤ s.sp.toNat + 64) ∨
    (p ≤ r.1 ∧ r.2 ≤ p + 8 * c))

/-- **A call keeps `Mid`**: the callee wrote only inside `R.rt`, the window parts of `WsOK` and the result array,
extending the live set. -/
theorem Mid.frame {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) {M2 : Memory} {ws : List (Nat × Nat)} {L'' : List (Nat × Nat)}
    {b'' : Nat} (hws : WsOK s p c ws) (hf : MemFrame M M2 (R.rt ++ ws)) (hl : LiveFrame M M2 L' ws)
    (hext : LiveExt R L' L'') (hb : b' ≤ b'') (hinv : R.inv b'' L'' (s.regs 28).toNat (view R.rt L'' M2)) :
    Mid R b L zp zc xp xl s p c L'' b'' M2 := by
  have hpw := h.pw; have hgw := h.gw; have hsp0 := h.sp0; have hpg := h.pg
  unfold Apart at hpw hgw hpg
  have key : ∀ a n, s.sp.toNat - 4240 ≤ a → a + n ≤ s.sp.toNat + 64 →
      (∀ r ∈ ws, a + n ≤ r.1 ∨ r.2 ≤ a) → Outside a n (R.rt ++ ws) := by
    intro a n h1 h2 h3
    simp only [outside_append]
    exact ⟨h.wrt.of_sub h1 (by omega), outside_of_forall h3⟩
  have rd : ∀ a, s.sp.toNat - 152 ≤ a → a + 8 ≤ s.sp.toNat - 136 → M2.readLE a 8 = M.readLE a 8 := by
    intro a h1 h2
    refine hf.readLE a 8 (key a 8 (by omega) (by omega) fun r hr => ?_)
    rcases (hws r hr).2 with h' | h' | h' | h' <;> omega
  refine { h with
      lr := by rw [rd _ (by omega) (by omega)]; exact h.lr
      fp := by rw [rd _ (by omega) (by omega)]; exact h.fp
      sacc := by rw [hf.accessible]; exact h.sacc
      gacc := by rw [hf.accessible]; exact h.gacc
      grd := ?_
      pacc := by rw [hf.accessible]; exact h.pacc
      pheld := hext.held h.pheld
      xacc := by rw [hf.accessible]; exact h.xacc
      xheld := hext.held h.xheld
      ext := h.ext.trans hext
      bud := Nat.le_trans h.bud hb
      inv := hinv
      lsep := ?_
      mf := ?_
      lf := ?_ }
  · rw [← h.grd]
    refine hf.readLE _ _ ?_
    simp only [outside_append]
    refine ⟨h.grt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h' | h' <;> omega
  · intro r hr
    obtain ⟨ns, rfl, hn, -⟩ := hext
    rcases List.mem_append.1 hr with hr | hr
    · exact h.lsep r hr
    · have hin := (hn r hr).1
      have hw := h.wrt
      simp only [win, outside_cons, outside_nil, and_true]
      have := outside_of_inRanges hw hin
      omega
  · refine h.mf.trans hf fun a n ho => ⟨ho, ?_⟩
    simp only [outside_append, winA, outside_cons, outside_nil, and_true] at ho ⊢
    obtain ⟨⟨hrt, hw1, hw2⟩, hz⟩ := ho
    refine ⟨hrt, outside_of_forall fun r hr => ?_⟩
    rcases (hws r hr).2 with h' | h' | h' | h'
    · omega
    · omega
    · omega
    · rcases h.ror with ⟨rfl, rfl⟩ | ⟨hin, -⟩
      · omega
      · have := outside_of_inRanges hrt hin; omega
  · refine ⟨fun a n hin hz => ?_⟩
    rw [hl.readLE a n (h.ext.inRanges_old hin) (outside_of_forall fun r hr => ?_)]
    · exact h.lf.readLE a n hin hz
    · obtain ⟨q, hq, hq1, hq2⟩ := hin
      have hsep := h.lsep q (h.ext.mem_old hq)
      simp only [win, outside_cons, outside_nil, and_true] at hsep hz
      rcases (hws r hr).2 with h' | h' | h' | h'
      · omega
      · omega
      · omega
      · rcases h.ror with ⟨rfl, rfl⟩ | ⟨-, hap⟩
        · omega
        · have := hap q hq; unfold Apart at this; omega

/-- **A frame without allocation keeps `Mid`** (stack stores). -/
theorem Mid.frame0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) {M2 : Memory} {ws : List (Nat × Nat)}
    (hws : WsOK s p c ws) (hf : MemFrame M M2 ws) : Mid R b L zp zc xp xl s p c L' b' M2 := by
  have hsp0 := h.sp0
  refine h.frame hws (hf.widen R.rt) (liveFrame_of_memFrame hf) (LiveExt.refl R L') (Nat.le_refl _) ?_
  refine RtInv.inv_frame' hf (fun r hr => ?_) h.inv
  have h0 := (hws r hr).1
  rcases (hws r hr).2 with h' | h' | h' | h'
  · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
  · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
  · exact Or.inl (h.wrt.of_sub (by omega) (by omega))
  · exact (h.pheld.sub h'.1 (by omega)).symm

/-- **The postcondition** from `Mid` at the return (`s'.mem = M`, result `(p, n', c)`, remainder `R3`). -/
theorem Mid.post {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl y : BitVec 64} {s : State}
    {p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {M : Memory}
    (h : Mid R b L zp zc xp xl s p c L' b' M) (s' : State) (n' : Nat)
    (hm : s'.mem = M) (h0 : (s'.regs 0).toNat = p) (h1 : (s'.regs 1).toNat = n') (h2 : (s'.regs 2).toNat = c)
    (h3 : (s'.regs 3).toNat = natVal s.mem xp.toNat xl.toNat % y.toNat) (hn : n' ≤ xl.toNat)
    (hv : natVal M p n' = natVal s.mem xp.toNat xl.toNat / y.toNat) (hnorm : NatNorm M p n') :
    Post R b L zp zc xp xl y s s' := by
  subst hm
  exact ⟨p, n', c, h0, h1, h2, h3, hv, hnorm, by have := h.cap; omega, hn, L', b', h.ext, h.bud, h.inv,
    fun _ => ⟨h.p8, h.pheld, h.pacc, h.p48⟩, h.ror, h.mf, h.lf⟩

end FvModexp.Arm64.DivW
