import FvModexp.Proofs.Arm64.Nat.MulCall
import FvModexp.Proofs.Arm64.Nat.MulOps
import FvModexp.Proofs.Arm64.Nat.KSqrRel

/-!
# `nat.mul` (arm64), the chunk loop `40 ≤ n < m` (natmul.go:50-62): the base relation `LB`

```go
karatsuba(stk, z[:2n], x[:n], y)            // x0 * y
clear(z[2n:])
defer stk.restore(stk.save())
t := stk.nat(2 * n)
for i := n; i < m; i += n {
	t = t.mul(stk, x[i:min(i+n, m)], y)
	addTo(z[i:], t)
}
return z.norm()
```
`LB … M Lk bk spent Mi` = the facts at every call boundary of the loop after `t := stk.nat(2n)` (memory `Mi`), relative
to `Core … p c L1 b1 M` (after `z.make`): the frame record (`SP' = SP - 256`; offsets from `SP`: saved `X30` `-256`,
`X29` `-264`, defer bits `-162`/`-161` (`= 2`), `c` `-160`, `m + n` `-136`, `p` `-112`, `stk` `-72`, the defer
record `{deferwrap2, stk, len}` at `-64, -56, -48`, its address at `-16`, the argument spills `x`, `y` at `+40 … +80`),
the runtime invariant, the stack (`len` raised by `rnd 2n`), the frames relative to `M`. The scratch `t`, the value of
`z` and the loop counter are stated by each segment.

`LB.step`: a callee at `SP - 256` (window inside ours, `above ≤ 88`) whose writes are classified by `LCls` (inside
`p[0:m+n]`, the stack header, `M`'s free part, or fresh) and which brings the stack back keeps `LB`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep guard)

/-- `nat.mul.deferwrap2` (the deferred `stk.restore(len)`), address stored in the defer record -/
def fnD2 : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul.deferwrap2"
abbrev mDfn : Nat := 0x1bb380

theorem fnD2_entry : segAddr Extracted.program fnD2 = mDfn := by decide

/-- the writes of the loop relative to `M`: `p[0:m+n]` and `M`'s stack header / free part -/
@[reducible] def lws (M : Memory) (st p N : Nat) : List (Nat × Nat) := (p, p + 8 * N) :: stkWs M st

/-- see the module doc -/
structure LB (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk spent : Nat)
    (Mi : Memory) : Prop where
  core : Core R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M
  h40 : 40 ≤ yl
  hlt : yl < xl
  ext : LiveExt R L1 Lk
  bud : b1 - spent ≤ bk
  inv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk Mi)
  reg : Mi.regions = s.mem.regions
  fr : MemFrame M Mi (R.rt ++ winA s W 88 ++ lws M st p (xl + yl))
  lf : LiveFrame M Mi L1 (lws M st p (xl + yl))
  sok : StkOK Mi R Lk st
  slen : stLen Mi st = stLen M st + rnd (2 * yl)
  sarr : (stW Mi st = stW M st ∧ stCap Mi st = stCap M st) ∨
    (InRanges (stW Mi st) (8 * stCap Mi st) R.rt ∧ ApartAll (stW Mi st) (8 * stCap Mi st) L1)
  smem : ArrIn Lk st M Mi
  lr : Mi.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat
  fp : Mi.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat
  b94 : Mi.readLE (s.sp.toNat - 162) 1 = 2
  b95 : Mi.readLE (s.sp.toNat - 161) 1 = 2
  c96 : Mi.readLE (s.sp.toNat - 160) 8 = c
  n120 : Mi.readLE (s.sp.toNat - 136) 8 = xl + yl
  p144 : Mi.readLE (s.sp.toNat - 112) 8 = p
  s184 : Mi.readLE (s.sp.toNat - 72) 8 = st
  dfn : Mi.readLE (s.sp.toNat - 64) 8 = mDfn
  dst : Mi.readLE (s.sp.toNat - 56) 8 = st
  dln : Mi.readLE (s.sp.toNat - 48) 8 = stLen M st
  dpt : Mi.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 64
  a296 : Mi.readLE (s.sp.toNat + 40) 8 = xp
  a304 : Mi.readLE (s.sp.toNat + 48) 8 = xl
  a312 : Mi.readLE (s.sp.toNat + 56) 8 = xc
  a320 : Mi.readLE (s.sp.toNat + 64) 8 = yp
  a328 : Mi.readLE (s.sp.toNat + 72) 8 = yl
  a336 : Mi.readLE (s.sp.toNat + 80) 8 = yc

/-- the ranges a callee at `SP - 256` may write besides `R.rt` and its window -/
def LCls (R : RtInv) (L1 : List (Nat × Nat)) (M : Memory) (st p N : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ r ∈ ws, r.1 ≤ r.2 ∧ ((p ≤ r.1 ∧ r.2 ≤ p + 8 * N) ∨ (st ≤ r.1 ∧ r.2 ≤ st + 24) ∨
    (stW M st + 8 * stLen M st ≤ r.1 ∧ r.2 ≤ stW M st + 8 * stCap M st) ∨
    (InRanges r.1 (r.2 - r.1) R.rt ∧ ApartAll r.1 (r.2 - r.1) L1))

theorem LCls.append {R : RtInv} {L1 : List (Nat × Nat)} {M : Memory} {st p N : Nat} {ws ws' : List (Nat × Nat)}
    (h : LCls R L1 M st p N ws) (h' : LCls R L1 M st p N ws') : LCls R L1 M st p N (ws ++ ws') := by
  intro r hr; rcases List.mem_append.1 hr with hr | hr
  · exact h r hr
  · exact h' r hr

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
  {Mi : Memory}

/-- the window / layout facts -/
theorem LB.lay (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    4608 ≤ W ∧ W ≤ s.sp.toNat ∧ s.sp.toNat % 16 = 0 ∧ s.sp.toNat + 88 ≤ 2 ^ 48 ∧
      Outside (s.sp.toNat - W) (W + 88) R.rt ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
      Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - W) (W + 88) ∧ xl + yl ≤ c ∧ c < 2 ^ 40 ∧
      Outside p (8 * c) (win s W 88) ∧ xl ≤ 2 ^ 12 ∧ yl ≤ 2 ^ 12 ∧ xl ≤ xc ∧ yl ≤ yc ∧ xc < 2 ^ 40 ∧ yc < 2 ^ 40 := by
  obtain ⟨⟨-, ⟨hal, hb, ha, -⟩, -, hout, hga, hgr, -, -⟩, hmw, -, -, -,
    ⟨⟨hxlc, hxc40, hx12, -⟩, ⟨hylc, hyc40, hy12, -⟩, -⟩, -⟩ := h.core.pre
  exact ⟨Nat.le_trans (mulW_ge _ _) hmw, hb, hal, ha, hout, hgr, hga, h.core.cap, h.core.c40, h.core.pw,
    hx12, hy12, hxlc, hylc, hxc40, hyc40⟩

/-- the stack header at `M` is the entry's -/
theorem LB.hdrM (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    stW M st = stW s.mem st ∧ stLen M st = stLen s.mem st ∧ stCap M st = stCap s.mem st := by
  have e0 := h.core.hdr 0 (by omega); have e1 := h.core.hdr 8 (by omega); have e2 := h.core.hdr 16 (by omega)
  simp only [Nat.add_zero] at e0
  exact ⟨e0, e1, e2⟩

/-- the stack's current free part lies in `M`'s free part, or the array is fresh -/
theorem LB.free (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    (stW Mi st = stW M st ∧ stCap Mi st = stCap M st ∧ stLen M st ≤ stLen Mi st) ∨
      (InRanges (stW Mi st) (8 * stCap Mi st) R.rt ∧ ApartAll (stW Mi st) (8 * stCap Mi st) L1) := by
  rcases h.sarr with ⟨e1, e2⟩ | h2
  · exact Or.inl ⟨e1, e2, by rw [h.slen]; omega⟩
  · exact Or.inr h2

/-- the ranges of `lws` are outside the window -/
theorem LB.lwsOut (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    ∀ q ∈ lws M st p (xl + yl), q.2 ≤ s.sp.toNat - W ∨ s.sp.toNat + 88 ≤ q.1 := by
  obtain ⟨-, -, -, -, -, -, -, hcap, -, hpw, -⟩ := h.lay
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  obtain ⟨-, -, -, -, -, -, hstk, -, -⟩ := h.core.pre
  obtain ⟨-, -, hstw, -, -, -, hfw, -⟩ := hstk
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw hpw
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw
  intro q hq
  simp only [lws, stkWs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rw [eW, eL, eC] at hq
  rcases hq with rfl | rfl | rfl <;> simp only <;> omega

/-- every classified write range is inside a range of `lws` or fresh -/
theorem LB.cls (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {ws : List (Nat × Nat)}
    (hws : LCls R L1 M st p (xl + yl) ws) :
    ∀ r ∈ ws, r.1 ≤ r.2 ∧ ((∃ q ∈ lws M st p (xl + yl), q.1 ≤ r.1 ∧ r.2 ≤ q.2) ∨
      (InRanges r.1 (r.2 - r.1) R.rt ∧ ApartAll r.1 (r.2 - r.1) L1)) := by
  intro r hr
  obtain ⟨hle, hc⟩ := hws r hr
  refine ⟨hle, ?_⟩
  rcases hc with hc | hc | hc | hc
  · exact Or.inl ⟨_, List.mem_cons_self, hc.1, hc.2⟩
  · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hc.1, hc.2⟩
  · exact Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hc.1, hc.2⟩
  · exact Or.inr hc

theorem LB.wsep (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    LiveSep L1 (win s W 88) := h.core.lsep

set_option maxRecDepth 20000 in
/-- **A callee at `SP - 256` keeps `LB`**: it wrote `R.rt`, its window (inside ours, below the locals) and
`LCls` ranges, extended the live set, charged at most `k'`, and brought the stack back. -/
theorem LB.step (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {Mi' : Memory} {k a : Nat}
    (hk : 256 + k ≤ W) (ha : a ≤ 88) {ws : List (Nat × Nat)} (hws : LCls R L1 M st p (xl + yl) ws)
    (hF : MemFrame Mi Mi' (R.rt ++ [(s.sp.toNat - 256 - k, s.sp.toNat - 256 - 8), (s.sp.toNat - 256 + 8,
      s.sp.toNat - 256 + a)] ++ ws)) (hLF : LiveFrame Mi Mi' Lk ws) (hreg : Mi'.regions = Mi.regions)
    {Lk' : List (Nat × Nat)} {bk' k' : Nat} (hext : LiveExt R Lk Lk') (hb : bk - k' ≤ bk')
    (hinv : R.inv bk' Lk' (s.regs 28).toNat (view R.rt Lk' Mi')) (hsb : StackBackL R Lk Lk' st Mi Mi') :
    LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' (spent + k') Mi' := by
  obtain ⟨hW, hWs, -, -, hout, -, -⟩ := h.lay
  have hcl := h.cls hws
  have hko := h.lwsOut
  have hLs := h.wsep
  have hrd : ∀ x m, s.sp.toNat - 264 ≤ x → x + m ≤ s.sp.toNat + 88 → (x + m ≤ s.sp.toNat - 248 ∨ s.sp.toNat - 168 ≤ x) →
      Mi'.readLE x m = Mi.readLE x m := by
    intro x m h1 h2 h3
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, outside_of_forall fun r hr => ?_⟩
    obtain ⟨hle, hc⟩ := hcl r hr
    rcases hc with ⟨q, hq, q1, q2⟩ | ⟨hin, -⟩
    · have := hko q hq; omega
    · have := NatSub.outside_of_inRanges (hout.of_sub (a := x) (n := m) (by omega) (by omega)) hin; omega
  obtain ⟨⟨hok', hlen', harr'⟩, hmem'⟩ := hsb
  have hsarr : (stW Mi' st = stW M st ∧ stCap Mi' st = stCap M st) ∨
      (InRanges (stW Mi' st) (8 * stCap Mi' st) R.rt ∧ ApartAll (stW Mi' st) (8 * stCap Mi' st) L1) := by
    rcases harr' with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · rw [e1, e2]; exact h.sarr
    · exact Or.inr ⟨hin, fun r hr => hap r (h.ext.mem_old hr)⟩
  refine
    { core := h.core, h40 := h.h40, hlt := h.hlt, ext := h.ext.trans hext, bud := by have := h.bud; omega,
      inv := hinv, reg := hreg.trans h.reg, fr := ?_, lf := ?_, sok := hok', slen := by rw [hlen']; exact h.slen,
      sarr := hsarr, smem := h.smem.trans hmem' hext,
      lr := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.lr,
      fp := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.fp,
      b94 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.b94,
      b95 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.b95,
      c96 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.c96,
      n120 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.n120,
      p144 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.p144,
      s184 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.s184,
      dfn := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.dfn,
      dst := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.dst,
      dln := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.dln,
      dpt := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.dpt,
      a296 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a296,
      a304 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a304,
      a312 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a312,
      a320 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a320,
      a328 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a328,
      a336 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a336 }
  · refine h.fr.trans hF fun x m ho => ⟨ho, ?_⟩
    rw [outside_append, outside_append] at ho
    obtain ⟨⟨hrt, hwa⟩, hz⟩ := ho
    simp only [winA, outside_cons, outside_nil, and_true] at hwa
    obtain ⟨hw1, hw2⟩ := hwa
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hrt, by omega, by omega⟩, outside_of_forall fun r hr => ?_⟩
    obtain ⟨hle, hc⟩ := hcl r hr
    rcases hc with ⟨q, hq, q1, q2⟩ | ⟨hin, -⟩
    · have := MemFrame.outside_mem hz hq; omega
    · have := NatSub.outside_of_inRanges hrt hin; omega
  · refine ⟨fun x m hin hz => ?_⟩
    rw [hLF.readLE x m (h.ext.inRanges_old hin) (outside_of_forall fun r hr => ?_)]
    · exact h.lf.readLE x m hin hz
    · obtain ⟨hle, hc⟩ := hcl r hr
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      rcases hc with ⟨q', hq', q1, q2⟩ | ⟨-, hap⟩
      · have := MemFrame.outside_mem hz hq'; omega
      · have := hap q hq; unfold Apart at this; omega

/-- the loop's own stores (`i`, `i + n`, the spilled `t` at `104 … 136`, `176`) keep `LB` -/
theorem LB.local (h : LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {Mi' : Memory}
    (hF0 : MemFrame Mi Mi' [(s.sp.toNat - 152, s.sp.toNat - 136), (s.sp.toNat - 128, s.sp.toNat - 112),
      (s.sp.toNat - 80, s.sp.toNat - 72)]) (hreg : Mi'.regions = Mi.regions) :
    LB R b L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi' := by
  have hW0 : 4608 ≤ W ∧ W ≤ s.sp.toNat := ⟨h.lay.1, h.lay.2.1⟩
  have hF : MemFrame Mi Mi' (winA s W 88) := hF0.mono fun a n ho => by
    simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hrd : ∀ x m, (x + m ≤ s.sp.toNat - 152 ∨ s.sp.toNat - 136 ≤ x) → (x + m ≤ s.sp.toNat - 128 ∨
      s.sp.toNat - 112 ≤ x) → (x + m ≤ s.sp.toNat - 80 ∨ s.sp.toNat - 72 ≤ x) → Mi'.readLE x m = Mi.readLE x m :=
    fun x m h1 h2 h3 => hF0.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  obtain ⟨hW, hWs, -, -, hout, -, -⟩ := h.lay
  have hko := h.lwsOut
  have hLs := h.wsep
  have hst : Outside st 24 (winA s W 88) := by
    have := hko _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [winA, outside_cons, outside_nil, and_true]; simp only at this; omega
  have eW : stW Mi' st = stW Mi st := hF.readLE _ _ (hst.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen Mi' st = stLen Mi st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eC : stCap Mi' st = stCap Mi st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  refine
    { core := h.core, h40 := h.h40, hlt := h.hlt, ext := h.ext, bud := h.bud,
      inv := inv_frame_winA hF hout (by omega) (by decide) h.inv, reg := hreg.trans h.reg,
      fr := h.fr.trans hF fun x m ho => ⟨ho, by simp only [outside_append] at ho; exact ho.1.2⟩,
      lf := LiveFrame.trans h.lf ⟨fun x m hin _ => hF.readLE x m (winA_of_win' (outside_of_liveSep hin hLs))⟩
        fun _ _ h => h,
      sok := stkOK_frame h.sok hF hst, slen := by rw [eL]; exact h.slen,
      sarr := by rw [eW, eC]; exact h.sarr, smem := h.smem.congr eW eC fun _ h => h,
      lr := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.lr,
      fp := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.fp,
      b94 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.b94,
      b95 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.b95,
      c96 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.c96,
      n120 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.n120,
      p144 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.p144,
      s184 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.s184,
      dfn := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.dfn,
      dst := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.dst,
      dln := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.dln,
      dpt := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.dpt,
      a296 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a296,
      a304 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a304,
      a312 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a312,
      a320 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a320,
      a328 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a328,
      a336 := by rw [hrd _ _ (by omega) (by omega) (by omega)]; exact h.a336 }

end

end FvModexp.Arm64.NatMul
