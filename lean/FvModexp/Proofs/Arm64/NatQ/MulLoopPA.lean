import FvModexp.Proofs.Arm64.NatQ.MulLoopHead

/-!
# [Q-form copy of Arm64/Nat/MulLoopPA.lean — TIGHT COSTS, divmc s34] `nat.mul` (arm64), the chunk loop's prologue (`40 ≤ n < m`, natmul.go:50-55): relations

```go
karatsuba(stk, z[:2n], x[:n], y)   // CALL 0x1bb038, return 0x1bb03c, BLT → 0x1bb054
clear(z[2n:])                      // memclrNoHeapPointers 0x1bb084
defer stk.restore(stk.save())      // bits |= 2, record {deferwrap2, stk, len} at 192(SP'), 240(SP') = SP' + 192
t := stk.nat(2 * n)                // CALL 0x1bb0bc, return 0x1bb0c0 → JMP head 0x1bb204
```
`LQ … Lk bk spent Mi` (`extends LB0`): the stack is back at its length at `M` (`StackBackL … M Mi`), the frame words
(`SP' = SP - 256`; offsets from `SP`) saved `X30` `-256`, `X29` `-264`, `c` `-160`, `m + n` `-136`, `2n` `-120`,
`p` `-112`, `stk` `-72`, the spills `+40 … +80`; `p` apart from `x` and `y`.
`KA … S` at `0x1bb054` (after `karatsuba`; `z[0:2n] = X[0:n]·Y`, bits `= 0`); `LP … P` at `(*stack).nat`'s entry
(`z[0:m+n] = X[0:n]·Y`, bits `= 2`, the defer record). `lpNatPre`: `StackNat.Pre` at `P`.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.NatMul

variable {H : Nat}

open FvModexp.Arm64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep)

abbrev stkNatM : Nat := 0x1b3970

/-- see the module doc -/
structure LQ (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk spent : Nat)
    (Mi : Memory) : Prop extends LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi where
  sb : StackBackL R L1 Lk st M Mi
  lr : Mi.readLE (s.sp.toNat - 256) 8 = (s.regs 30).toNat
  fp : Mi.readLE (s.sp.toNat - 264) 8 = (s.regs 29).toNat
  c96 : Mi.readLE (s.sp.toNat - 160) 8 = c
  n120 : Mi.readLE (s.sp.toNat - 136) 8 = xl + yl
  n136 : Mi.readLE (s.sp.toNat - 120) 8 = 2 * yl
  p144 : Mi.readLE (s.sp.toNat - 112) 8 = p
  s184 : Mi.readLE (s.sp.toNat - 72) 8 = st
  a296 : Mi.readLE (s.sp.toNat + 40) 8 = xp
  a304 : Mi.readLE (s.sp.toNat + 48) 8 = xl
  a312 : Mi.readLE (s.sp.toNat + 56) 8 = xc
  a320 : Mi.readLE (s.sp.toNat + 64) 8 = yp
  a328 : Mi.readLE (s.sp.toNat + 72) 8 = yl
  a336 : Mi.readLE (s.sp.toNat + 80) 8 = yc
  px : Apart p (8 * c) xp (8 * xl)
  py : Apart p (8 * c) yp (8 * yl)

/-- after `karatsuba(stk, z[:2n], x[:n], y)`, at `0x1bb054` -/
structure KA (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) :
    Prop where
  lq : LQ R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (KCQ yl) S.mem
  pc : S.pc = BitVec.ofNat 64 0x1bb054
  sp : S.sp = s.sp - 256#64
  g : S.regs 28 = s.regs 28
  fp : S.regs 29 = s.sp - 264#64
  x18 : S.regs 18 = s.regs 18
  r10 : S.regs 10 = BitVec.ofNat 64 yl
  b94 : S.mem.readLE (s.sp.toNat - 162) 1 = 0
  val : natVal S.mem p (2 * yl) = natVal s.mem xp yl * natVal s.mem yp yl

/-- at `(*stack).nat`'s entry (`CALL 0x1bb0bc`) -/
structure LP (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk : Nat) (P : State) :
    Prop where
  lq : LQ R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (KCQ yl) P.mem
  pc : P.pc = BitVec.ofNat 64 stkNatM
  sp : P.sp = s.sp - 256#64
  g : P.regs 28 = s.regs 28
  fp : P.regs 29 = s.sp - 264#64
  x18 : P.regs 18 = s.regs 18
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 1 = BitVec.ofNat 64 (2 * yl)
  r30 : P.regs 30 = BitVec.ofNat 64 0x1bb0c0
  b94 : P.mem.readLE (s.sp.toNat - 162) 1 = 2
  b95 : P.mem.readLE (s.sp.toNat - 161) 1 = 2
  dfn : P.mem.readLE (s.sp.toNat - 64) 8 = mDfn
  dst : P.mem.readLE (s.sp.toNat - 56) 8 = st
  dln : P.mem.readLE (s.sp.toNat - 48) 8 = stLen M st
  dpt : P.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 64
  val : natVal P.mem p (xl + yl) = natVal s.mem xp yl * natVal s.mem yp yl

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory} {Lk : List (Nat × Nat)} {bk spent : Nat}
  {Mi : Memory}

/-- the stack's current array (`M`'s or fresh) and free part at `Mi`: outside the window, apart from the guard word,
the header apart from the free part -/
theorem LQ.stk (h : LQ R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    (0 < stCap Mi st → Outside (stW Mi st) (8 * stCap Mi st) (win s W 88) ∧
      Apart (stW Mi st) (8 * stCap Mi st) (NatSqr.guard s) 8) ∧
    Apart st 24 (stW Mi st + 8 * stLen Mi st) (8 * (stCap Mi st - stLen Mi st)) := by
  obtain ⟨hW, hWs, -, -, hout, hgr, hga, -⟩ := h.lay
  obtain ⟨eW, eL, eC⟩ := h.hdrM
  have hsp : StkPre R L s W 88 st := h.core.pre.2.2.2.2.2.2.1
  obtain ⟨-, ⟨-, hsth, -, -, -, hlc0, -⟩, -, -, hsarr, -, -, hstf, -⟩ := hsp
  obtain ⟨⟨-, hlen, harr⟩, -⟩ := h.sb
  simp only [NatSqr.guard, BasicSqr.freeP, BasicSqr.freeN] at hstf hsarr ⊢
  rcases harr with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · rw [e1, e2, eW, eC]; rw [hlen, eL]
    exact ⟨hsarr, hstf⟩
  · have hgo := NatSub.outside_of_inRanges hgr hin
    have hst := apart_of_held (h.core.ext.held hsth) hin hap
    have hlc := h.sok.2.2.2.2.2.1
    refine ⟨fun _ => ⟨?_, by unfold Apart; omega⟩, by unfold Apart at hst ⊢; omega⟩
    have := NatSub.outside_of_inRanges (hout.of_sub (a := s.sp.toNat - W) (n := W + 88) (by omega) (by omega)) hin
    simp only [win, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
/-- **`stk.nat(2n)`'s precondition** at its entry `P` -/
theorem lpNatPre {P : State} (h : LP R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk P) :
    StackNatX.PreQ R bk Lk H 4208 24 st (2 * yl) P := by
  have hq := h.lq
  obtain ⟨hW, hWs, hal, ha48, hout, hgr, hga, hcap, -, -, hx12, hy12, -⟩ := hq.lay
  have h40 := hq.h40; have hlt := hq.hlt
  obtain ⟨eW, eL, eC⟩ := hq.hdrM
  have hspP : P.sp.toNat = s.sp.toNat - 256 := by rw [h.sp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hce := hq.callee (S1 := P) (stk1 := 4208) (above1 := 24) hspP h.g rfl (by omega) (by omega)
  have hpre := hq.core.pre
  obtain ⟨-, -, hsv, -, -, ⟨-, -, -, hlen16⟩, hsp, ⟨hlvH, hcost⟩, -⟩ := hpre
  obtain ⟨-, -, hstw, -, -, -, -, -, hstwb, -⟩ := hsp
  have hgl := hq.glob (w' := []) (fun _ _ _ => trivial)
  have hwbacc : P.mem.accessible StackNat.wbA 4 false = true := hgl.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hsa, hsf⟩ := hq.stk
  obtain ⟨⟨-, hlenP, -⟩, -⟩ := hq.sb
  have hk := lsp_end h40 hlt (k := 0) (by omega)
  simp only [lsp, chunkSum, Nat.add_zero] at hk
  have hb := hq.core.bud; have hb1 := hq.bud
  have hwin : ∀ x k, Outside x k (win s W 88) → Outside x k (win P 4208 24) := by
    intro x k hx; simp only [win, outside_cons, outside_nil, and_true] at hx ⊢; rw [hspP]; omega
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hstP : stLen P.mem st = stLen s.mem st := by rw [hlenP, eL]
  refine ⟨hce, hsv, hq.sok, hwin _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega),
    fun hc => ⟨hwin _ _ (hsa hc).1, ?_⟩, by omega, by rw [hstP]; omega, ⟨by rw [hstP]; omega, by omega⟩,
    by rw [h.g]; exact hq.inv, hwbacc, hstwb, hsf⟩
  · have := (hsa hc).2; simp only [NatSqr.guard] at this; rw [h.g]; exact this

set_option maxRecDepth 20000 in
/-- the frames of `LB0` after a callee at `SP - 256` (window inside ours) whose other writes are classified by `LCls` -/
theorem LB0.frames (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {Mi' : Memory}
    {k a : Nat} (hk : 256 + k ≤ W) (ha : a ≤ 88) {ws : List (Nat × Nat)} (hws : LCls R L1 M st p (xl + yl) ws)
    (hF : MemFrame Mi Mi' (R.rt ++ [(s.sp.toNat - 256 - k, s.sp.toNat - 256 - 8), (s.sp.toNat - 256 + 8,
      s.sp.toNat - 256 + a)] ++ ws)) (hLF : LiveFrame Mi Mi' Lk ws) :
    MemFrame M Mi' (R.rt ++ winA s W 88 ++ lws M st p (xl + yl)) ∧ LiveFrame M Mi' L1 (lws M st p (xl + yl)) := by
  obtain ⟨hW, hWs, -, -, hout, -, -⟩ := h.lay
  have hcl := h.cls hws
  refine ⟨?_, ?_⟩
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

/-- the stack's header and free part at `Mi` are `LCls` write ranges -/
theorem LQ.stkCls (h : LQ R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) :
    LCls R L1 M st p (xl + yl) (stkWs Mi st) := by
  obtain ⟨⟨-, hlen, harr⟩, -⟩ := h.sb
  have hlc := h.sok.2.2.2.2.2.1
  intro r hr
  simp only [stkWs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨by simp only; omega, Or.inr (Or.inl ⟨by simp only; omega, by simp only; omega⟩)⟩
  · refine ⟨by simp only; omega, ?_⟩
    rcases harr with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by simp only; rw [e1, hlen]; exact Nat.le_refl _, by simp only; rw [e1, e2]; exact Nat.le_refl _⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
      · simp only; exact hin.sub (by omega) (by omega)
      · simp only; exact ApartAll.sub' hap (by omega) (by omega)

end

end FvModexp.Arm64.Q.NatMul
