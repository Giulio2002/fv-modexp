import FvModexp.Proofs.Amd64.NatQ.MulCall
import FvModexp.Proofs.Amd64.NatQ.MulOps
import FvModexp.Proofs.Amd64.NatQ.KSqrRel

/-!
# [amd64 port (divmc s45) of the Q-form Arm64/NatQ/MulLoopRel.lean — TIGHT COSTS] `nat.mul` (amd64), the chunk loop `40 ≤ n < m` (natmul.go:50-62): the base relation `LB`

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
to `Core … p c L1 b1 M` (after `z.make`): the frame record (`SP' = RSP - 256`; offsets from `RSP`: return address `0`,
saved `BP` `-8`, defer bits `0x56/0x57(SP')` = `-170`/`-169` (`= 2`), `c` `-168`, `m + n` `-144`, `p` `-112`, `stk`
`-72`, the defer record `{deferwrap2, stk, len}` at `0xc0(SP')` = `-64, -56, -48`, its address at `0xf0(SP')` = `-16`,
the spills `x` at `+64 … +80`, the stack argument `y` at `+8 … +24`),
the runtime invariant, the stack (`len` raised by `rnd 2n`), the frames relative to `M`. The scratch `t`, the value of
`z` and the loop counter are stated by each segment.

`LB.step`: a callee entered at `RSP - 264` (window inside ours, `above ≤ 88`) whose writes are classified by `LCls` (inside
`p[0:m+n]`, the stack header, `M`'s free part, or fresh) and which brings the stack back keeps `LB`.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep guard
  inv_frame_win)

/-- `nat.mul.deferwrap2` (the deferred `stk.restore(len)`), address stored in the defer record -/
def fnD2 : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.mul.deferwrap2"
abbrev mDfn : Nat := 0x5f0f60

theorem fnD2_entry : segAddr Extracted.program fnD2 = mDfn := by decide

/-- the writes of the loop relative to `M`: `p[0:m+n]` and `M`'s stack header / free part -/
@[reducible] def lws (M : Memory) (st p N : Nat) : List (Nat × Nat) := (p, p + 8 * N) :: stkWs M st

/-- the part of `LB` shared with the prologue relations (before `t := stk.nat(2n)`; see `MulLoopPA`) -/
structure LB0 (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk spent : Nat)
    (Mi : Memory) : Prop where
  core : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M
  h40 : 40 ≤ yl
  hlt : yl < xl
  ext : LiveExt R L1 Lk
  bud : b1 - (spent + stkR H s.mem st) + stkR H Mi st ≤ bk
  spk : makeB (xl + yl) + spent ≤ mulCQ xl yl
  inv : R.inv bk Lk (s.regs 14).toNat (view R.rt Lk Mi)
  reg : Mi.regions = s.mem.regions
  fr : MemFrame M Mi (R.rt ++ win s W 88 ++ lws M st p (xl + yl))
  lf : LiveFrame M Mi L1 (lws M st p (xl + yl))
  sok : StkOK Mi R Lk st

/-- see the module doc -/
structure LB (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk spent : Nat)
    (Mi : Memory) : Prop extends LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi where
  slen : stLen Mi st = stLen M st + rnd (2 * yl)
  sarr : (stW Mi st = stW M st ∧ stCap Mi st = stCap M st) ∨
    (InRanges (stW Mi st) (8 * stCap Mi st) R.rt ∧ ApartAll (stW Mi st) (8 * stCap Mi st) L1)
  smem : ArrIn Lk st M Mi
  ra : Mi.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : Mi.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  b56 : Mi.readLE ((s.regs 4).toNat - 170) 1 = 2
  b57 : Mi.readLE ((s.regs 4).toNat - 169) 1 = 2
  c58 : Mi.readLE ((s.regs 4).toNat - 168) 8 = c
  n70 : Mi.readLE ((s.regs 4).toNat - 144) 8 = xl + yl
  p90 : Mi.readLE ((s.regs 4).toNat - 112) 8 = p
  sb8 : Mi.readLE ((s.regs 4).toNat - 72) 8 = st
  dfn : Mi.readLE ((s.regs 4).toNat - 64) 8 = mDfn
  dst : Mi.readLE ((s.regs 4).toNat - 56) 8 = st
  dln : Mi.readLE ((s.regs 4).toNat - 48) 8 = stLen M st
  dpt : Mi.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 64
  x140 : Mi.readLE ((s.regs 4).toNat + 64) 8 = xp
  x148 : Mi.readLE ((s.regs 4).toNat + 72) 8 = xl
  x150 : Mi.readLE ((s.regs 4).toNat + 80) 8 = xc
  y108 : Mi.readLE ((s.regs 4).toNat + 8) 8 = yp
  y110 : Mi.readLE ((s.regs 4).toNat + 16) 8 = yl
  y118 : Mi.readLE ((s.regs 4).toNat + 24) 8 = yc

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
theorem LB0.lay (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    4608 ≤ W ∧ W ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat + 88 ≤ 2 ^ 48 ∧
      Outside ((s.regs 4).toNat - W) (W + 88) R.rt ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
      Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - W) (W + 88) ∧ xl + yl ≤ c ∧ c < 2 ^ 40 ∧
      Outside p (8 * c) (win s W 88) ∧ xl ≤ 2 ^ 12 ∧ yl ≤ 2 ^ 12 ∧ xl ≤ xc ∧ yl ≤ yc ∧ xc < 2 ^ 40 ∧ yc < 2 ^ 40 := by
  obtain ⟨⟨-, ⟨hb, ha, -⟩, hal, -, hout, hga, hgr, -, -⟩, hmw, -, -, -,
    ⟨⟨hxlc, hxc40, hx12, -⟩, ⟨hylc, hyc40, hy12, -⟩, -⟩, -⟩ := h.core.pre
  simp only [regSP] at hb ha
  exact ⟨Nat.le_trans (mulW64_ge _ _) hmw, hb, hal, ha, hout, hgr, hga, h.core.cap, h.core.c40, h.core.pw,
    hx12, hy12, hxlc, hylc, hxc40, hyc40⟩

/-- the stack header at `M` is the entry's -/
theorem LB0.hdrM (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    stW M st = stW s.mem st ∧ stLen M st = stLen s.mem st ∧ stCap M st = stCap s.mem st := by
  have e0 := h.core.hdr 0 (by omega); have e1 := h.core.hdr 8 (by omega); have e2 := h.core.hdr 16 (by omega)
  simp only [Nat.add_zero] at e0
  exact ⟨e0, e1, e2⟩

/-- the stack's current free part lies in `M`'s free part, or the array is fresh -/
theorem LB.free (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    (stW Mi st = stW M st ∧ stCap Mi st = stCap M st ∧ stLen M st ≤ stLen Mi st) ∨
      (InRanges (stW Mi st) (8 * stCap Mi st) R.rt ∧ ApartAll (stW Mi st) (8 * stCap Mi st) L1) := by
  rcases h.sarr with ⟨e1, e2⟩ | h2
  · exact Or.inl ⟨e1, e2, by rw [h.slen]; omega⟩
  · exact Or.inr h2

/-- the ranges of `lws` are outside the window -/
theorem LB0.lwsOut (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    ∀ q ∈ lws M st p (xl + yl), q.2 ≤ (s.regs 4).toNat - W ∨ (s.regs 4).toNat + 88 ≤ q.1 := by
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
theorem LB0.cls (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {ws : List (Nat × Nat)}
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

theorem LB0.wsep (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    LiveSep L1 (win s W 88) := h.core.lsep

set_option maxRecDepth 20000 in
/-- **A callee entered at `RSP - 264` keeps `LB`**: it wrote `R.rt`, its window (inside ours, below the locals) and
`LCls` ranges, extended the live set, charged at most `k'`, and brought the stack back. -/
theorem LB.step (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {Mi' : Memory} {k a : Nat}
    (hk : 264 + k ≤ W) (ha : a ≤ 88) {ws : List (Nat × Nat)} (hws : LCls R L1 M st p (xl + yl) ws)
    (hF : MemFrame Mi Mi' (R.rt ++ [((s.regs 4).toNat - 264 - k, (s.regs 4).toNat - 264 + a)] ++ ws)) (hLF : LiveFrame Mi Mi' Lk ws) (hreg : Mi'.regions = Mi.regions)
    {Lk' : List (Nat × Nat)} {bk' k' : Nat} (hext : LiveExt R Lk Lk')
    (hb : bk - (k' + stkR H Mi st) + stkR H Mi' st ≤ bk' ∨ (bk - k' ≤ bk' ∧ stCap Mi' st = stCap Mi st))
    (hc : makeB (xl + yl) + spent + k' ≤ mulCQ xl yl)
    (hinv : R.inv bk' Lk' (s.regs 14).toNat (view R.rt Lk' Mi')) (hsb : StackBackL R Lk Lk' st Mi Mi') :
    LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk' bk' (spent + k') Mi' := by
  obtain ⟨hW, hWs, -, -, hout, -, -⟩ := h.lay
  have hcl := h.cls hws
  have hko := h.lwsOut
  have hLs := h.wsep
  have hrd : ∀ x m, (s.regs 4).toNat - 176 ≤ x → x + m ≤ (s.regs 4).toNat + 88 →
      Mi'.readLE x m = Mi.readLE x m := by
    intro x m h1 h2
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, outside_of_forall fun r hr => ?_⟩
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
    { core := h.core, h40 := h.h40, hlt := h.hlt, ext := h.ext.trans hext, bud := ?_, spk := by omega,
      inv := hinv, reg := hreg.trans h.reg, fr := ?_, lf := ?_, sok := hok', slen := by rw [hlen']; exact h.slen,
      sarr := hsarr, smem := h.smem.trans hmem' hext,
      ra := by rw [hrd _ _ (by omega) (by omega)]; exact h.ra,
      bp := by rw [hrd _ _ (by omega) (by omega)]; exact h.bp,
      b56 := by rw [hrd _ _ (by omega) (by omega)]; exact h.b56,
      b57 := by rw [hrd _ _ (by omega) (by omega)]; exact h.b57,
      c58 := by rw [hrd _ _ (by omega) (by omega)]; exact h.c58,
      n70 := by rw [hrd _ _ (by omega) (by omega)]; exact h.n70,
      p90 := by rw [hrd _ _ (by omega) (by omega)]; exact h.p90,
      sb8 := by rw [hrd _ _ (by omega) (by omega)]; exact h.sb8,
      dfn := by rw [hrd _ _ (by omega) (by omega)]; exact h.dfn,
      dst := by rw [hrd _ _ (by omega) (by omega)]; exact h.dst,
      dln := by rw [hrd _ _ (by omega) (by omega)]; exact h.dln,
      dpt := by rw [hrd _ _ (by omega) (by omega)]; exact h.dpt,
      x140 := by rw [hrd _ _ (by omega) (by omega)]; exact h.x140,
      x148 := by rw [hrd _ _ (by omega) (by omega)]; exact h.x148,
      x150 := by rw [hrd _ _ (by omega) (by omega)]; exact h.x150,
      y108 := by rw [hrd _ _ (by omega) (by omega)]; exact h.y108,
      y110 := by rw [hrd _ _ (by omega) (by omega)]; exact h.y110,
      y118 := by rw [hrd _ _ (by omega) (by omega)]; exact h.y118 }
  · have h0 := h.bud; have h1 := h.core.bud; have h2 := (h.core.pre.2.2.2.2.2.2.2.1).2
    rcases hb with hb | ⟨hb, hcp⟩
    · omega
    · rw [stkR_congr hcp]; omega
  · refine h.fr.trans hF fun x m ho => ⟨ho, ?_⟩
    rw [outside_append, outside_append] at ho
    obtain ⟨⟨hrt, hwa⟩, hz⟩ := ho
    simp only [win, outside_cons, outside_nil, and_true] at hwa
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hrt, by omega⟩, outside_of_forall fun r hr => ?_⟩
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

/-- the loop's own stores (the outgoing `y` arguments `0 … 16(SP')`, the spilled `t` at `0x60, 0x68, 0xb0(SP')`, `i`,
`8 i`, `i + n` at `0x78, 0x80, 0x88(SP')`) keep `LB` -/
theorem LB.local (h : LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {Mi' : Memory}
    (hF0 : MemFrame Mi Mi' [((s.regs 4).toNat - 256, (s.regs 4).toNat - 232), ((s.regs 4).toNat - 160,
      (s.regs 4).toNat - 144), ((s.regs 4).toNat - 136, (s.regs 4).toNat - 112), ((s.regs 4).toNat - 80,
      (s.regs 4).toNat - 72)]) (hreg : Mi'.regions = Mi.regions) :
    LB R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi' := by
  have hW0 : 4608 ≤ W ∧ W ≤ (s.regs 4).toNat := ⟨h.lay.1, h.lay.2.1⟩
  have hF : MemFrame Mi Mi' (win s W 88) := hF0.mono fun a n ho => by
    simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have hrd : ∀ x m, (s.regs 4).toNat - 232 ≤ x → (x + m ≤ (s.regs 4).toNat - 160 ∨ (s.regs 4).toNat - 144 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 136 ∨ (s.regs 4).toNat - 112 ≤ x) →
      (x + m ≤ (s.regs 4).toNat - 80 ∨ (s.regs 4).toNat - 72 ≤ x) → Mi'.readLE x m = Mi.readLE x m :=
    fun x m h0 h1 h2 h3 => hF0.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  obtain ⟨hW, hWs, -, -, hout, -, -⟩ := h.lay
  have hko := h.lwsOut
  have hLs := h.wsep
  have hst : Outside st 24 (win s W 88) := by
    have := hko _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [win, outside_cons, outside_nil, and_true]; simp only at this; omega
  have eW : stW Mi' st = stW Mi st := hF.readLE _ _ (hst.of_sub (Nat.le_refl _) (by omega))
  have eL : stLen Mi' st = stLen Mi st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  have eC : stCap Mi' st = stCap Mi st := hF.readLE _ _ (hst.of_sub (by omega) (by omega))
  refine
    { core := h.core, h40 := h.h40, hlt := h.hlt, ext := h.ext, bud := by rw [stkR_congr eC]; exact h.bud,
      spk := h.spk, inv := inv_frame_win hF hout (by omega) (by decide) h.inv, reg := hreg.trans h.reg,
      fr := h.fr.trans hF fun x m ho => ⟨ho, by simp only [outside_append] at ho; exact ho.1.2⟩,
      lf := LiveFrame.trans h.lf ⟨fun x m hin _ => hF.readLE x m (outside_of_liveSep hin hLs)⟩
        fun _ _ h => h,
      sok := stkOK_frame h.sok hF hst, slen := by rw [eL]; exact h.slen,
      sarr := by rw [eW, eC]; exact h.sarr, smem := h.smem.congr eW eC fun _ h => h,
      ra := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.ra,
      bp := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.bp,
      b56 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.b56,
      b57 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.b57,
      c58 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.c58,
      n70 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.n70,
      p90 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.p90,
      sb8 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.sb8,
      dfn := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.dfn,
      dst := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.dst,
      dln := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.dln,
      dpt := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.dpt,
      x140 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.x140,
      x148 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.x148,
      x150 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.x150,
      y108 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.y108,
      y110 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.y110,
      y118 := by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega)]; exact h.y118 }

end

end FvModexp.Amd64.Q.NatMul
