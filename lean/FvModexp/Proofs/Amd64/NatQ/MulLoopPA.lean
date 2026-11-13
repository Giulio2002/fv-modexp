import FvModexp.Proofs.Amd64.NatQ.MulLoopHead

/-!
# [amd64 port (divmc s45) of the Q-form Arm64/NatQ/MulLoopPA.lean — TIGHT COSTS] `nat.mul` (amd64), the chunk loop's prologue (`40 ≤ n < m`, natmul.go:50-55): relations

```go
karatsuba(stk, z[:2n], x[:n], y)   // CALL 0x5f0ae0, return 0x5f0ae5, JG (m > n) → 0x5f0b05
clear(z[2n:])                      // memclrNoHeapPointers 0x5f0b4c (skipped when m + n = 2n)
defer stk.restore(stk.save())      // bits |= 2 (0x56/0x57(SP')), record {deferwrap2, stk, len} at 0xc0(SP'), ptr 0xf0(SP')
t := stk.nat(2 * n)                // CALL 0x5f0ba4, return 0x5f0ba9 → DX = n, JMP head 0x5f0d39
```
`LQ … Lk bk spent Mi` (`extends LB0`): the stack is back at its length at `M` (`StackBackL … M Mi`), the frame words
(`SP' = RSP - 256`; offsets from `RSP`) return address `0`, saved `BP` `-8`, `c` `-168`, `m + n` `-144`, `2n` `-120`,
`p` `-112`, `stk` `-72`, the spills `x` `+64 … +80`, `y` `+8 … +24`; `p` apart from `x` and `y`.
`KA … S` at `0x5f0b05` (after `karatsuba`; `z[0:2n] = X[0:n]·Y`, bits `= 0`); `LP … P` at `(*stack).nat`'s entry
`0x5e6480` (`z[0:m+n] = X[0:n]·Y`, bits `= 2`, the defer record). `lpNatPre`: `StackNatX.PreQ` at `P`.
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame StkPre StkSep)

abbrev stkNatM : Nat := 0x5e6480

/-- see the module doc -/
structure LQ (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk spent : Nat)
    (Mi : Memory) : Prop extends LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi where
  sb : StackBackL R L1 Lk st M Mi
  ra : Mi.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  bp : Mi.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  c58 : Mi.readLE ((s.regs 4).toNat - 168) 8 = c
  n70 : Mi.readLE ((s.regs 4).toNat - 144) 8 = xl + yl
  n88 : Mi.readLE ((s.regs 4).toNat - 120) 8 = 2 * yl
  p90 : Mi.readLE ((s.regs 4).toNat - 112) 8 = p
  sb8 : Mi.readLE ((s.regs 4).toNat - 72) 8 = st
  x140 : Mi.readLE ((s.regs 4).toNat + 64) 8 = xp
  x148 : Mi.readLE ((s.regs 4).toNat + 72) 8 = xl
  x150 : Mi.readLE ((s.regs 4).toNat + 80) 8 = xc
  y108 : Mi.readLE ((s.regs 4).toNat + 8) 8 = yp
  y110 : Mi.readLE ((s.regs 4).toNat + 16) 8 = yl
  y118 : Mi.readLE ((s.regs 4).toNat + 24) 8 = yc
  px : Apart p (8 * c) xp (8 * xl)
  py : Apart p (8 * c) yp (8 * yl)

/-- after `karatsuba(stk, z[:2n], x[:n], y)`, at `0x5f0b05` -/
structure KA (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) :
    Prop where
  lq : LQ R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (KCQ yl) S.mem
  pc : S.rip = BitVec.ofNat 64 0x5f0b05
  sp : S.regs 4 = s.regs 4 - 256#64
  g : S.regs 14 = s.regs 14
  bp : S.regs 5 = s.regs 4 - 8#64
  fs : S.fsBase = s.fsBase
  df : S.df = s.df
  x15 : S.xmm 15 = s.xmm 15
  r10 : S.regs 10 = BitVec.ofNat 64 yl
  b56 : S.mem.readLE ((s.regs 4).toNat - 170) 1 = 0
  val : natVal S.mem p (2 * yl) = natVal s.mem xp yl * natVal s.mem yp yl

/-- at `(*stack).nat`'s entry (`CALL 0x5f0ba4`, entry `0x5e6480`, return `0x5f0ba9` at `RSP - 264`) -/
structure LP (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) (Lk : List (Nat × Nat)) (bk : Nat) (P : State) :
    Prop where
  lq : LQ R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk (KCQ yl) P.mem
  pc : P.rip = BitVec.ofNat 64 stkNatM
  sp : P.regs 4 = s.regs 4 - 264#64
  g : P.regs 14 = s.regs 14
  bp : P.regs 5 = s.regs 4 - 8#64
  fs : P.fsBase = s.fsBase
  df : P.df = s.df
  x15 : P.xmm 15 = s.xmm 15
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r3 : P.regs 3 = BitVec.ofNat 64 (2 * yl)
  ra : P.mem.readLE ((s.regs 4).toNat - 264) 8 = 0x5f0ba9
  b56 : P.mem.readLE ((s.regs 4).toNat - 170) 1 = 2
  b57 : P.mem.readLE ((s.regs 4).toNat - 169) 1 = 2
  dfn : P.mem.readLE ((s.regs 4).toNat - 64) 8 = mDfn
  dst : P.mem.readLE ((s.regs 4).toNat - 56) 8 = st
  dln : P.mem.readLE ((s.regs 4).toNat - 48) 8 = stLen M st
  dpt : P.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 64
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
    have := NatSub.outside_of_inRanges (hout.of_sub (a := (s.regs 4).toNat - W) (n := W + 88) (by omega) (by omega)) hin
    simp only [win, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
/-- **`stk.nat(2n)`'s precondition** at its entry `P` -/
theorem lpNatPre {P : State} (h : LP R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk P) :
    StackNatX.PreQ R bk Lk H 4192 24 st (2 * yl) P := by
  have hq := h.lq
  obtain ⟨hW, hWs, hal, ha48, hout, hgr, hga, hcap, -, -, hx12, hy12, -⟩ := hq.lay
  have h40 := hq.h40; have hlt := hq.hlt
  obtain ⟨eW, eL, eC⟩ := hq.hdrM
  have hspP : (P.regs 4).toNat = (s.regs 4).toNat - 264 := by
    rw [h.sp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hce := hq.callee (S1 := P) (stk1 := 4192) (above1 := 24) hspP h.g rfl h.fs (by omega) (by omega)
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
  have hwin : ∀ x k, Outside x k (win s W 88) → Outside x k (win P 4192 24) := by
    intro x k hx; simp only [win, outside_cons, outside_nil, and_true] at hx ⊢; rw [hspP]; omega
  simp only [win, outside_cons, outside_nil, and_true] at hstw
  have hstP : stLen P.mem st = stLen s.mem st := by rw [hlenP, eL]
  refine ⟨hce, hsv, hq.sok, hwin _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega),
    fun hc => ⟨hwin _ _ (hsa hc).1, ?_⟩, by omega, by rw [hstP]; omega, ⟨by rw [hstP]; omega, by omega⟩,
    by rw [h.g]; exact hq.inv, hwbacc, hstwb, hsf⟩
  · have := (hsa hc).2; simp only [NatSqr.guard] at this; rw [h.g]; exact this

set_option maxRecDepth 20000 in
/-- the frames of `LB0` after a callee entered at `RSP - 264` (window inside ours) whose other writes are classified by `LCls` -/
theorem LB0.frames (h : LB0 R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M Lk bk spent Mi) {Mi' : Memory}
    {k a : Nat} (hk : 264 + k ≤ W) (ha : a ≤ 88) {ws : List (Nat × Nat)} (hws : LCls R L1 M st p (xl + yl) ws)
    (hF : MemFrame Mi Mi' (R.rt ++ [((s.regs 4).toNat - 264 - k, (s.regs 4).toNat - 264 + a)] ++ ws))
    (hLF : LiveFrame Mi Mi' Lk ws) :
    MemFrame M Mi' (R.rt ++ win s W 88 ++ lws M st p (xl + yl)) ∧ LiveFrame M Mi' L1 (lws M st p (xl + yl)) := by
  obtain ⟨hW, hWs, -, -, hout, -, -⟩ := h.lay
  have hcl := h.cls hws
  refine ⟨?_, ?_⟩
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

end FvModexp.Amd64.Q.NatMul
