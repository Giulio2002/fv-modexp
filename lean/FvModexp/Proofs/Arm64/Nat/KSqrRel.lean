import FvModexp.Proofs.Arm64.Nat.SqrKPre
import FvModexp.Proofs.Arm64.Nat.AddTo
import FvModexp.Proofs.Arm64.Nat.Restore
import FvModexp.Proofs.Common.KSqrMath

/-!
# `karatsubaSqr` (arm64, go-bigmodexpfix natmul.go:257): the relation between the call segments

Frame 320 (`SP' = SP - 320`, entry `SP`): saved `X30` at `SP - 320`, `X29` at `SP - 328`; locals (offsets from `SP`):
defer bit `-249` (1 byte), `n2` at `-248`, `n + 1` at `-240`; the six stack `*Int`s `tx` `-232`, `z1` `-200`,
`z2` `-144`, `z0` `-112`, `x1` `-80`, `x0` `-48` (`neg` byte, `abs` = ptr/len/cap at `+8/+16/+24`); the open-coded
defer record `{deferwrap1, stk, len(stk.w)}` at `-168, -160, -152`, its address at `-16`; spills `stk, zp, zl, zc, xp`
at `SP + 8 … SP + 40` (`above = 48`).

`KM … M Lk bk spent` = the facts at every call boundary after `z1 := stk.nat(2·n2 + 1)` (scratch `t`): the frame
record, `x0`/`x1` (constant), the runtime invariant at `(Lk, bk)` with `spent` charged, the stack (`len` raised by
`rnd (2·n2+1)`, array kept or fresh), `t` apart from the stack's header and free part, and the frames relative to the
entry (writes only `z[0:2n]`, the entry stack's header/free part, `R.rt` and the window). The `*Int`s `tx`, `z1`, `z0`,
`z2` and the contents of `z`/`t` change between segments and are stated by each segment.

`KM.step`: a callee at `SP - 320` whose writes are in `z[0:2n]`, `t`, the `tx`/`z1` headers or the stack's header/free
part, which brings the stack back, keeps `KM`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- `n2 = ⌈n/2⌉` -/
abbrev kn2 (n : Nat) : Nat := (n + 1) / 2
/-- the length of the scratch `z1` (`stk.nat(2·n2 + 1)`) -/
abbrev kT (n : Nat) : Nat := 2 * kn2 n + 1
/-- `karatsubaSqr.deferwrap1` (the defer record's code pointer) -/
abbrev kDfn : Nat := 0x1bc5e0

/-- an `*Int` header at `a` -/
@[reducible] def IntAt (m : Memory) (a ng p l c : Nat) : Prop :=
  m.readLE a 1 = ng ∧ m.readLE (a + 8) 8 = p ∧ m.readLE (a + 16) 8 = l ∧ m.readLE (a + 24) 8 = c

/-- the writes `karatsubaSqr` may make (relative to the entry): `z[0:2n]` and the entry stack's header / free part -/
@[reducible] def kws (s : State) (st zp n : Nat) : List (Nat × Nat) := (zp, zp + 8 * (2 * n)) :: stkWs s.mem st

/-- see the module doc -/
structure KM (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State)
    (lx0 lx1 t : Nat) (Lk : List (Nat × Nat)) (bk spent : Nat) (M : Memory) : Prop where
  pre : KPre R b L W st zp (2 * n) zc xp n xc s
  -- the halves of `x` (normalised lengths)
  l0 : lx0 ≤ kn2 n
  v0 : natVal s.mem xp lx0 = natVal s.mem xp (kn2 n)
  nn0 : NatNorm s.mem xp lx0
  l1 : lx1 ≤ n - kn2 n
  v1 : natVal s.mem (xp + 8 * kn2 n) lx1 = natVal s.mem (xp + 8 * kn2 n) (n - kn2 n)
  nn1 : NatNorm s.mem (xp + 8 * kn2 n) lx1
  -- the scratch `t` (`z1`'s array)
  scr : Scr R L Lk s.mem s.mem st t (kT n)
  tsep : StkSep M st t (8 * kT n)
  -- runtime
  ext : LiveExt R L Lk
  bud : b - spent ≤ bk
  inv : R.inv bk Lk (s.regs 28).toNat (view R.rt Lk M)
  reg : M.regions = s.mem.regions
  fr : MemFrame s.mem M (R.rt ++ winA s W 48 ++ kws s st zp n)
  lf : LiveFrame s.mem M L (kws s st zp n)
  -- the stack
  sok : StkOK M R Lk st
  slen : stLen M st = stLen s.mem st + StackNat.rnd (kT n)
  sarr : (stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st) ∨
    (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)
  -- the frame record
  lr : M.readLE (s.sp.toNat - 320) 8 = (s.regs 30).toNat
  fp : M.readLE (s.sp.toNat - 328) 8 = (s.regs 29).toNat
  bit : M.readLE (s.sp.toNat - 249) 1 = 1
  n2s : M.readLE (s.sp.toNat - 248) 8 = kn2 n
  n1s : M.readLE (s.sp.toNat - 240) 8 = n + 1
  dfn : M.readLE (s.sp.toNat - 168) 8 = kDfn
  dst : M.readLE (s.sp.toNat - 160) 8 = st
  dln : M.readLE (s.sp.toNat - 152) 8 = stLen s.mem st
  dpt : M.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 168
  s1 : M.readLE (s.sp.toNat + 8) 8 = st
  s2 : M.readLE (s.sp.toNat + 16) 8 = zp
  s3 : M.readLE (s.sp.toNat + 24) 8 = 2 * n
  s4 : M.readLE (s.sp.toNat + 32) 8 = zc
  s5 : M.readLE (s.sp.toNat + 40) 8 = xp
  x0h : IntAt M (s.sp.toNat - 48) 0 xp lx0 xc
  x1h : IntAt M (s.sp.toNat - 80) 0 (xp + 8 * kn2 n) lx1 (xc - kn2 n)

/-- the window facts of the entry -/
theorem KM.lay {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    4880 + 16 * n ≤ W ∧ W ≤ s.sp.toNat ∧ s.sp.toNat % 16 = 0 ∧ s.sp.toNat + 48 ≤ 2 ^ 48 ∧ 80 ≤ n ∧ n ≤ 2 ^ 12 ∧
      n ≤ xc ∧ xc < 2 ^ 40 ∧ 2 * n ≤ zc ∧ zc < 2 ^ 40 ∧
      Outside (s.sp.toNat - W) (W + 48) R.rt ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
      Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - W) (W + 48) := by
  obtain ⟨⟨-, ⟨hal, hb, ha, -⟩, -, hout, hga, hgr, -, -⟩, hW, -, -, -, h80, hxc, hxc40, hx12, -, -, -, -, -, hzl, hzc40, -⟩ := h.pre
  unfold ksqrW at hW
  exact ⟨by omega, hb, hal, ha, h80, hx12, hxc, hxc40, by omega, hzc40, hout, hgr, hga⟩

/-- the ranges a callee at `SP - 320` may write besides `R.rt` and its window: `z[0:2n]`, `t`, the `tx`/`z1` headers,
the stack's current header and free part -/
def KWs (s : State) (M : Memory) (st zp n t : Nat) (ws : List (Nat × Nat)) : Prop :=
  ∀ r ∈ ws, r.1 ≤ r.2 ∧ ((zp ≤ r.1 ∧ r.2 ≤ zp + 8 * (2 * n)) ∨ (t ≤ r.1 ∧ r.2 ≤ t + 8 * kT n) ∨
    (s.sp.toNat - 232 ≤ r.1 ∧ r.2 ≤ s.sp.toNat - 168) ∨ (s.sp.toNat - 144 ≤ r.1 ∧ r.2 ≤ s.sp.toNat - 80) ∨
    (st ≤ r.1 ∧ r.2 ≤ st + 24) ∨
    (stW M st + 8 * stLen M st ≤ r.1 ∧ r.2 ≤ stW M st + 8 * stCap M st))

theorem KWs.append {s : State} {M : Memory} {st zp n t : Nat} {ws ws' : List (Nat × Nat)}
    (h : KWs s M st zp n t ws) (h' : KWs s M st zp n t ws') : KWs s M st zp n t (ws ++ ws') := by
  intro r hr; rcases List.mem_append.1 hr with hr | hr
  · exact h r hr
  · exact h' r hr

/-- the stack's current free part lies in the entry's free part, or is fresh -/
theorem KM.free {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    (stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st ∧ stLen s.mem st ≤ stLen M st) ∨
      (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L) := by
  rcases h.sarr with ⟨e1, e2⟩ | h2
  · exact Or.inl ⟨e1, e2, by rw [h.slen]; omega⟩
  · exact Or.inr h2

/-- every write range is in the header area of the frame, inside a range of `kws`, or fresh (inside `R.rt`, apart from
`L`) -/
theorem KM.wcls {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) {ws : List (Nat × Nat)}
    (hws : KWs s M st zp n t ws) :
    ∀ r ∈ ws, r.1 ≤ r.2 ∧ ((s.sp.toNat - 232 ≤ r.1 ∧ r.2 ≤ s.sp.toNat - 168) ∨
      (s.sp.toNat - 144 ≤ r.1 ∧ r.2 ≤ s.sp.toNat - 80) ∨ (∃ q ∈ kws s st zp n, q.1 ≤ r.1 ∧ r.2 ≤ q.2) ∨
      (InRanges r.1 (r.2 - r.1) R.rt ∧ ApartAll r.1 (r.2 - r.1) L)) := by
  intro r hr
  obtain ⟨hle, hc⟩ := hws r hr
  refine ⟨hle, ?_⟩
  rcases hc with hc | hc | hc | hc | hc | hc
  · exact Or.inr (Or.inr (Or.inl ⟨_, List.mem_cons_self, hc.1, hc.2⟩))
  · rcases h.scr.loc with ⟨-, h1, h2⟩ | ⟨hin, hap⟩
    · exact Or.inr (Or.inr (Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        by simp only; omega, by simp only; omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩))
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hc.1, hc.2⟩))
  · rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, hap⟩
    · rw [e1, e2] at hc
      have := h.sok.2.2.2.2.2.1
      exact Or.inr (Or.inr (Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        by simp only; omega, by simp only; omega⟩))
    · have := h.sok.2.2.2.2.2.1
      exact Or.inr (Or.inr (Or.inr ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩))

/-- the ranges of `kws` are outside the window -/
theorem KM.kwsOut {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    ∀ q ∈ kws s st zp n, q.2 ≤ s.sp.toNat - W ∨ s.sp.toNat + 48 ≤ q.1 := by
  have hzw : Outside zp (8 * zc) (win s W 48) := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsp : StkPre R L s W 48 st := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzl : 2 * n ≤ zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, hstw, -, -, -, hfw, -⟩ := hsp
  simp only [win, outside_cons, outside_nil, and_true] at hzw hstw hfw
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw
  intro q hq
  simp only [kws, stkWs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> simp only <;> omega

theorem KM.wsep {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) : LiveSep L (win s W 48) :=
  h.pre.1.2.2.2.2.2.2.1

/-- **A callee at `SP - 320` keeps `KM`**: it wrote `R.rt`, its window (inside ours, below the locals) and `KWs`
ranges, extended the live set, charged at most `c`, and brought the stack back. -/
theorem KM.step {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) {M' : Memory} {k a : Nat}
    (hk : 320 + k ≤ W) (ha : a ≤ 64) {ws : List (Nat × Nat)} (hws : KWs s M st zp n t ws)
    (hF : MemFrame M M' (R.rt ++ [(s.sp.toNat - 320 - k, s.sp.toNat - 320 - 8), (s.sp.toNat - 320 + 8,
      s.sp.toNat - 320 + a)] ++ ws)) (hLF : LiveFrame M M' Lk ws) (hreg : M'.regions = M.regions)
    {Lk' : List (Nat × Nat)} {bk' c : Nat} (hext : LiveExt R Lk Lk') (hb : bk - c ≤ bk')
    (hinv : R.inv bk' Lk' (s.regs 28).toNat (view R.rt Lk' M')) (hsb : StackBack R Lk Lk' st M M') :
    KM R b L W st zp zc xp n xc s lx0 lx1 t Lk' bk' (spent + c) M' := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, hout, -, -⟩ := h.lay
  have hcl := h.wcls hws
  have hko := h.kwsOut
  have hLs := h.wsep
  -- a read in our window above the callee's, or outside both windows and all write ranges, is unchanged
  have hrd : ∀ x m, s.sp.toNat - 328 ≤ x → x + m ≤ s.sp.toNat + 48 → (x + m ≤ s.sp.toNat - 312 ∨ s.sp.toNat - 256 ≤ x) →
      (x + m ≤ s.sp.toNat - 232 ∨ s.sp.toNat - 168 ≤ x) → (x + m ≤ s.sp.toNat - 144 ∨ s.sp.toNat - 80 ≤ x) →
      M'.readLE x m = M.readLE x m := by
    intro x m h1 h2 h3 h4 h5
    refine hF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, outside_of_forall fun r hr => ?_⟩
    obtain ⟨hle, hc⟩ := hcl r hr
    rcases hc with hc | hc | ⟨q, hq, q1, q2⟩ | ⟨hin, -⟩
    · omega
    · omega
    · have := hko q hq; omega
    · have := NatSub.outside_of_inRanges (hout.of_sub (a := x) (n := m) (by omega) (by omega)) hin; omega
  -- the stack after the call
  obtain ⟨hok', hlen', harr'⟩ := hsb
  have hsarr : (stW M' st = stW s.mem st ∧ stCap M' st = stCap s.mem st) ∨
      (InRanges (stW M' st) (8 * stCap M' st) R.rt ∧ ApartAll (stW M' st) (8 * stCap M' st) L) := by
    rcases harr' with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · rw [e1, e2]; exact h.sarr
    · exact Or.inr ⟨hin, fun r hr => hap r (h.ext.mem_old hr)⟩
  have htsep : StkSep M' st t (8 * kT n) := by
    refine ⟨h.tsep.1, ?_⟩
    rcases harr' with ⟨e1, e2⟩ | ⟨hin, hap⟩
    · simp only [BasicSqr.freeP, BasicSqr.freeN] at h ⊢
      have := h.tsep.2; simp only [BasicSqr.freeP, BasicSqr.freeN] at this
      rw [e1, e2, hlen']; exact this
    · have hap' := apart_of_held h.scr.held hin hap
      have := h.sok.2.2.2.2.2.1
      have hl := hok'.2.2.2.2.2.1
      simp only [BasicSqr.freeP, BasicSqr.freeN]
      unfold Apart at hap' ⊢; omega
  refine
    { pre := h.pre, l0 := h.l0, v0 := h.v0, nn0 := h.nn0, l1 := h.l1, v1 := h.v1, nn1 := h.nn1,
      scr := { h.scr with held := hext.held h.scr.held }, tsep := htsep, ext := h.ext.trans hext,
      bud := by have := h.bud; omega, inv := hinv, reg := hreg.trans h.reg, fr := ?_, lf := ?_, sok := hok', slen := by rw [hlen']; exact h.slen,
      sarr := hsarr, lr := ?_, fp := ?_, bit := ?_, n2s := ?_, n1s := ?_, dfn := ?_, dst := ?_, dln := ?_, dpt := ?_,
      s1 := ?_, s2 := ?_, s3 := ?_, s4 := ?_, s5 := ?_, x0h := ?_, x1h := ?_ }
  · refine h.fr.trans hF fun x m ho => ⟨ho, ?_⟩
    rw [outside_append, outside_append] at ho
    obtain ⟨⟨hrt, hwa⟩, hz⟩ := ho
    simp only [winA, outside_cons, outside_nil, and_true] at hwa
    obtain ⟨hw1, hw2⟩ := hwa
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨hrt, by omega, by omega⟩, outside_of_forall fun r hr => ?_⟩
    obtain ⟨hle, hc⟩ := hcl r hr
    rcases hc with hc | hc | ⟨q, hq, q1, q2⟩ | ⟨hin, -⟩
    · omega
    · omega
    · have := MemFrame.outside_mem hz hq; omega
    · have := NatSub.outside_of_inRanges hrt hin; omega
  · refine ⟨fun x m hin hz => ?_⟩
    rw [hLF.readLE x m (h.ext.inRanges_old hin) (outside_of_forall fun r hr => ?_)]
    · exact h.lf.readLE x m hin hz
    · obtain ⟨hle, hc⟩ := hcl r hr
      obtain ⟨q, hq, hq1, hq2⟩ := hin
      rcases hc with hc | hc | ⟨q', hq', q1, q2⟩ | ⟨-, hap⟩
      · have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this; omega
      · have := hLs q hq; simp only [win, outside_cons, outside_nil, and_true] at this; omega
      · have := MemFrame.outside_mem hz hq'; omega
      · have := hap q hq; unfold Apart at this; omega
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.lr
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.fp
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.bit
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.n2s
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.n1s
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.dfn
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.dst
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.dln
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.dpt
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.s1
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.s2
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.s3
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.s4
  · rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h.s5
  · obtain ⟨q1, q2, q3, q4⟩ := h.x0h
    exact ⟨by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact q1,
      by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact q2,
      by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact q3,
      by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact q4⟩
  · obtain ⟨q1, q2, q3, q4⟩ := h.x1h
    exact ⟨by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact q1,
      by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact q2,
      by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact q3,
      by rw [hrd _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact q4⟩

/-- the read-only data stays loaded -/
theorem KM.dl {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) : Extracted.program.DataLoaded M := by
  obtain ⟨⟨-, ⟨hal, hb, ha', hw⟩, hdl, -, -, -, -, hro⟩, -⟩ := h.pre
  have hzl : 2 * n ≤ zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzlive : NatLive s.mem R L zp zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsp : StkPre R L s W 48 st := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, ⟨-, -, hsacc, -, hnl, hlc, -⟩, -⟩ := hsp
  have hfr : MemFrame s.mem M (R.rt ++ (winA s W 48 ++ kws s st zp n)) := by
    rw [← List.append_assoc]; exact h.fr
  refine dataLoaded_frame hdl h.reg hro hfr fun r hr hlt => ?_
  simp only [winA, kws, stkWs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl | rfl | rfl
  · exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
  · exact Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
  · obtain ⟨-, -, hacc, -⟩ := hzlive (by simp only at hlt; omega)
    exact Memory.accessible_mono _ hacc (by simp only; omega) (by simp only; omega)
  · exact Memory.accessible_mono _ hsacc (by simp only; omega) (by simp only; omega)
  · simp only at hlt
    obtain ⟨-, -, hacc, -⟩ := hnl (by omega)
    exact Memory.accessible_mono _ hacc (by simp only; omega) (by simp only; omega)

/-- the stack-guard word keeps its value -/
theorem KM.grd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, hout, hgr, hga⟩ := h.lay
  have hzg : Apart zp (8 * zc) (guard s) 8 := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hzl : 2 * n ≤ zc := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsp : StkPre R L s W 48 st := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, hstg, -, hfg, -⟩ := hsp
  simp only [guard, BasicSqr.freeP, BasicSqr.freeN] at hzg hstg hfg
  unfold Apart at hzg hstg hfg hga
  refine h.fr.readLE _ _ ?_
  simp only [winA, kws, stkWs, outside_append, outside_cons, outside_nil, and_true]
  refine ⟨⟨hgr, by omega, by omega⟩, by omega, by omega, by omega⟩

/-- the call environment of a callee at `SP - 320` (window inside ours, below the locals) -/
theorem KM.callee {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) {S1 : State} {stk1 above1 : Nat}
    (hsp : S1.sp.toNat = s.sp.toNat - 320) (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = M)
    (hk : 320 + stk1 ≤ W) (ha : above1 ≤ 64) : CallEnv R Lk S1 stk1 above1 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha', hw⟩, hdl, hout, hga, hgr, hLs, hro⟩, -⟩ := h.pre
  unfold Apart at hga
  have hgrd := h.grd
  obtain ⟨ns, hLk, hn, -⟩ := h.ext
  refine ⟨⟨by rw [hg]; exact hg1, by rw [hg, hm, h.fr.accessible]; exact hg2, by rw [hg, hm, hgrd, hsp]; omega⟩,
    ⟨by omega, by omega, by omega, ?_⟩, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro⟩
  · rw [hm, h.fr.accessible, hsp]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · rw [hm]; exact h.dl
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr
    simp only [win, outside_cons, outside_nil, and_true]; rw [hsp]
    rw [hLk] at hr
    rcases List.mem_append.1 hr with hr | hr
    · have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this; omega
    · have := NatSub.outside_of_inRanges hout (hn r hr).1; omega

/-- the stack's current array and free part: outside the window, apart from the guard word and the header, held -/
theorem KM.stk {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) :
    (0 < stCap M st → Outside (stW M st) (8 * stCap M st) (win s W 48) ∧
      Apart (stW M st) (8 * stCap M st) (guard s) 8) ∧
    Apart (BasicSqr.freeP M st) (BasicSqr.freeN M st) (guard s) 8 ∧
    Outside (BasicSqr.freeP M st) (BasicSqr.freeN M st) (win s W 48) ∧
    Apart st 24 (BasicSqr.freeP M st) (BasicSqr.freeN M st) ∧ Held R Lk (BasicSqr.freeP M st) (BasicSqr.freeN M st) := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, hout, hgr, hga⟩ := h.lay
  have hsp : StkPre R L s W 48 st := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, ⟨-, hsth, -, -, -, hlc0, -⟩, -, -, hsarr, hfg, hfw, hstf, -, hfh⟩ := hsp
  have hlc := h.sok.2.2.2.2.2.1
  have hnl := h.sok.2.2.2.2.1
  simp only [guard, BasicSqr.freeP, BasicSqr.freeN] at hfg hfw hstf hfh hsarr ⊢
  rcases h.free with ⟨e1, e2, e3⟩ | ⟨hin, hap⟩
  · rw [e1, e2] at hnl ⊢; rw [e2] at hlc
    refine ⟨hsarr, ?_, ?_, ?_, h.ext.held (hfh.sub (by omega) (by omega))⟩
    · unfold Apart at hfg ⊢; omega
    · exact hfw.of_sub (by omega) (by omega)
    · unfold Apart at hstf ⊢; omega
  · have hgo := NatSub.outside_of_inRanges hgr hin
    have hst := apart_of_held hsth hin hap
    have hcap : 0 < stCap M st := by
      have := h.slen; simp only [StackNat.rnd, kT, kn2] at this; omega
    obtain ⟨-, hh, -, -⟩ := hnl hcap
    have hw : ∀ a k, stW M st ≤ a → a + k ≤ stW M st + 8 * stCap M st → Outside a k (win s W 48) := by
      intro a k h1 h2
      have := NatSub.outside_of_inRanges (hout.of_sub (a := s.sp.toNat - W) (n := W + 48) (by omega) (by omega)) hin
      simp only [win, outside_cons, outside_nil, and_true]; omega
    refine ⟨fun _ => ⟨hw _ _ (by omega) (by omega), by unfold Apart; omega⟩, by unfold Apart; omega,
      hw _ _ (by omega) (by omega), by unfold Apart at hst ⊢; omega, hh.sub (by omega) (by omega)⟩

/-- **`StkPre` at an inner call** (`SP - 320`, window `W' + 320 ≤ W`, above `≤ 64`) -/
theorem KM.stkPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 t : Nat} {Lk : List (Nat × Nat)} {bk spent : Nat} {M : Memory}
    (h : KM R b L W st zp zc xp n xc s lx0 lx1 t Lk bk spent M) {S1 : State} {W' a : Nat}
    (hsp : S1.sp.toNat = s.sp.toNat - 320) (hg : S1.regs 28 = s.regs 28) (hm : S1.mem = M)
    (hk : 320 + W' ≤ W) (ha : a ≤ 64) : StkPre R Lk S1 W' a st := by
  obtain ⟨hW, hWs, -, -, -, -, -, -, -, -, hout, hgr, hga⟩ := h.lay
  have hsp' : StkPre R L s W 48 st := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hst0, -, hstw, hstg, -, -, -, -, hstwb, -⟩ := hsp'
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.stk
  have hwin : ∀ x k, Outside x k (win s W 48) → Outside x k (win S1 W' a) := by
    intro x k hx; simp only [win, outside_cons, outside_nil, and_true] at hx ⊢; rw [hsp]; omega
  subst hm
  simp only [StkPre, guard, hg] at h1 h2 hstg ⊢
  exact ⟨hst0, h.sok, hwin _ _ hstw, hstg, fun hc => ⟨hwin _ _ (h1 hc).1, (h1 hc).2⟩, h2, hwin _ _ h3, h4, hstwb, h5⟩

end FvModexp.Arm64.NatSqr
