import FvModexp.Proofs.Arm64.Nat.SqrDefs

/-!
# `nat.sqr` (arm64): the relation after `z = z.make(…)` and the pure post builder

`Core … p c L1 b1 M`: the result array `(p, c)` (`z`'s own when reused, else fresh from `makeslice`), the live set `L1`,
the budget `b1` and the memory `M` after `z.make`; every path of `nat.sqr` (`n = 0`, `n = 1`, `basicMul`, `basicSqr`,
`karatsubaSqr`) reaches such a state, writes `p[0:2n]` (and the stack scratch), normalises and returns: `post_of`
builds `SPost` from the callee's facts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatSqr

/-- the state after `z = z.make(2n)` -/
structure Core (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) : Prop where
  pre : SPre R b L W zp zc st xp xl xc s
  F : MemFrame s.mem M (R.rt ++ winA s W 64)
  LF : LiveFrame s.mem M L []
  ext : LiveExt R L L1
  bud : b - makeB (2 * xl) ≤ b1
  inv : R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M)
  cap : 2 * xl ≤ c
  c40 : c < 2 ^ 40
  live : NatLive M R L1 p c
  pw : Outside p (8 * c) (win s W 64)
  kind : (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L ∧ InRanges p (8 * c) L1)
  ru : 2 * xl ≤ zc → zp + 8 * zc ≠ xp + 8 * xc → p = zp ∧ c = zc

theorem winA_of_win {s : State} {W a n : Nat} (h : Outside a n (win s W 64)) : Outside a n (winA s W 64) := by
  simp only [win, winA, outside_cons, outside_nil, and_true] at h ⊢; omega

theorem outside_of_liveSep {L ws : List (Nat × Nat)} {a n : Nat} (h : InRanges a n L) (hs : LiveSep L ws) :
    Outside a n ws := by
  obtain ⟨r, hr, h1, h2⟩ := h
  exact (hs r hr).of_sub h1 (by omega)

theorem apart_of_apartAll {L : List (Nat × Nat)} {a n p k : Nat} (h : ApartAll a n L) (hin : InRanges p k L) :
    Apart a n p k := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := h r hr; unfold Apart at this ⊢; omega

theorem apart_of_held {R : RtInv} {L : List (Nat × Nat)} {w n p k : Nat} (hh : Held R L w n)
    (hin : InRanges p k R.rt) (hap : ApartAll p k L) : Apart p k w n := by
  rcases hh with h | h
  · exact apart_of_apartAll hap h
  · have := NatAdd.outside_of_inRanges h hin; unfold Apart; omega

/-- a held range outside the window keeps its bytes from the entry to `M` -/
theorem Core.rd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) {a n : Nat} (hh : Held R L a n)
    (ho : Outside a n (win s W 64)) : M.readLE a n = s.mem.readLE a n :=
  Held.readLE hh hJ.F ⟨fun a n hin _ => hJ.LF.readLE a n hin trivial⟩ (winA_of_win ho)

/-- the window-only frame keeps the live objects -/
theorem lf_win {L : List (Nat × Nat)} {s : State} {W : Nat} {m m' : Memory} (ws : List (Nat × Nat))
    (h : MemFrame m m' (winA s W 64)) (hs : LiveSep L (win s W 64)) : LiveFrame m m' L ws :=
  ⟨fun a n hin _ => h.readLE a n (winA_of_win (outside_of_liveSep hin hs))⟩

theorem stkOK_frame {R : RtInv} {L : List (Nat × Nat)} {m m' : Memory} {st : Nat} {rs : List (Nat × Nat)}
    (h : StkOK m R L st) (hF : MemFrame m m' rs) (ho : Outside st 24 rs) : StkOK m' R L st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e0 : m'.readLE st 8 = m.readLE st 8 := hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega))
  have e1 : m'.readLE (st + 8) 8 = m.readLE (st + 8) 8 := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have e2 : m'.readLE (st + 16) 8 = m.readLE (st + 16) 8 := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  refine ⟨h1, h2, by rw [hF.accessible]; exact h3, h4, ?_, ?_, ?_⟩
  · simp only [stW, stCap] at h5 ⊢; rw [e0, e2]; intro hc
    obtain ⟨q1, q2, q3, q4⟩ := h5 hc; exact ⟨q1, q2, by rw [hF.accessible]; exact q3, q4⟩
  · simp only [stLen, stCap] at h6 ⊢; rw [e1, e2]; exact h6
  · simp only [stCap] at h7 ⊢; rw [e2]; exact h7

/-- the frame chain entry → `make` → call state → callee → return, when the callee's write of `[p, e)` is covered -/
theorem chain {R : RtInv} {wa ss ts : List (Nat × Nat)} {m0 m1 m2 m3 : Memory} {p e : Nat}
    (h1 : MemFrame m0 m1 (R.rt ++ wa)) (h2 : MemFrame m1 m2 (R.rt ++ wa ++ (p, e) :: ss)) (h3 : MemFrame m2 m3 wa)
    (hp : ∀ a n, Outside a n (R.rt ++ wa ++ ts ++ ss) → a + n ≤ p ∨ e ≤ a) :
    MemFrame m0 m3 (R.rt ++ wa ++ ts ++ ss) := by
  refine MemFrame.trans (MemFrame.trans h1 h2 (rs'' := R.rt ++ wa ++ ts ++ ss) fun a n h => ?_) h3 fun a n h => ?_
  · have := hp a n h
    simp only [outside_append, outside_cons] at h ⊢
    exact ⟨⟨h.1.1.1, h.1.1.2⟩, ⟨h.1.1.1, h.1.1.2⟩, this, h.2⟩
  · refine ⟨h, ?_⟩; simp only [outside_append] at h; exact h.1.1.2

theorem Core.hdr {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) (k : Nat) (hk : k + 8 ≤ 24) :
    M.readLE (st + k) 8 = s.mem.readLE (st + k) 8 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, ⟨-, hsth, -⟩, hstw, -⟩, -, -, -, -⟩ := hJ.pre
  exact hJ.rd (hsth.sub (by omega) (by omega)) (hstw.of_sub (by omega) (by omega))

/-- the stack object at `M` -/
theorem Core.stk {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) : StkOK M R L1 st := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, hstok, -⟩, -, -, -, -⟩ := hJ.pre
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hstok
  have e0 := hJ.hdr 0 (by omega); have e1 := hJ.hdr 8 (by omega); have e2 := hJ.hdr 16 (by omega)
  simp only [Nat.add_zero] at e0
  refine ⟨h1, hJ.ext.held h2, by rw [hJ.F.accessible]; exact h3, h4, ?_, ?_, ?_⟩
  · simp only [stW, stCap] at h5 ⊢; rw [e0, e2]; intro hc
    obtain ⟨q1, q2, q3, q4⟩ := h5 hc; exact ⟨q1, hJ.ext.held q2, by rw [hJ.F.accessible]; exact q3, q4⟩
  · simp only [stLen, stCap] at h6 ⊢; rw [e1, e2]; exact h6
  · simp only [stCap] at h7 ⊢; rw [e2]; exact h7

/-- the result array is apart from the stack header -/
theorem Core.pst {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) (hc : 0 < c) : Apart p (8 * c) st 24 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hzs, -, ⟨-, ⟨-, hsth, -⟩, -⟩, -, -, -, -⟩ := hJ.pre
  rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, hap, -⟩
  · have := (hzs hc).2.1; unfold Apart at this ⊢; omega
  · exact apart_of_held hsth hin hap

/-- the live set after `make` is outside the window -/
theorem Core.lsep {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) : LiveSep L1 (win s W 64) := by
  obtain ⟨⟨-, ⟨-, hb', -⟩, -, hout, -, -, hLs, -⟩, -⟩ := hJ.pre
  exact IntAS.liveSep_ext hJ.ext hLs fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; simp only
    rw [show s.sp.toNat + 64 - (s.sp.toNat - W) = W + 64 by omega]; exact hout

/-- the registers and spills at the join after `z = z.make(2n)` (`+0x104`): `R0..R2 = (p, 2n, c)`, `R3 = stk`,
`R4..R6 = x`; `p`, `2n`, `c` spilled at `112`, `96`, `88(SP')` -/
structure JoinAt (s S : State) (p c : Nat) (st xp xl xc : BitVec 64) : Prop where
  pc : S.pc = BitVec.ofNat 64 0x1bb524
  r0 : S.regs 0 = BitVec.ofNat 64 p
  r1 : S.regs 1 = BitVec.ofNat 64 (2 * xl.toNat)
  r2 : S.regs 2 = BitVec.ofNat 64 c
  r3 : S.regs 3 = st
  r4 : S.regs 4 = xp
  r5 : S.regs 5 = xl
  r6 : S.regs 6 = xc
  sp : S.sp = s.sp - 176#64
  g : S.regs 28 = s.regs 28
  fp : S.regs 29 = s.sp - 184#64
  x18 : S.regs 18 = s.regs 18
  mlr : S.mem.readLE (s.sp.toNat - 176) 8 = (s.regs 30).toNat
  mfp : S.mem.readLE (s.sp.toNat - 184) 8 = (s.regs 29).toNat
  m64 : S.mem.readLE (s.sp.toNat - 64) 8 = p
  m80 : S.mem.readLE (s.sp.toNat - 80) 8 = 2 * xl.toNat
  m88 : S.mem.readLE (s.sp.toNat - 88) 8 = c
  reg : S.mem.regions = s.mem.regions
  px : Apart p (8 * c) xp.toNat (8 * xl.toNat)
  na : p + 8 * c ≠ xp.toNat + 8 * xc.toNat

/-- window stores after `make` keep `Core` -/
theorem Core.win {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M M' : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) (hF : MemFrame M M' (winA s W 64)) :
    Core R b L W zp zc st xp xl xc s p c L1 b1 M' := by
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩, -⟩ := hJ.pre
  refine ⟨hJ.pre, hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩,
    LiveFrame.trans hJ.LF (lf_win [] hF hLs) fun _ _ h => h, hJ.ext, hJ.bud,
    inv_frame_winA hF hout (by omega) (by decide) hJ.inv, hJ.cap, hJ.c40, ?_, hJ.pw, hJ.kind, hJ.ru⟩
  intro h; obtain ⟨q1, q2, q3, q4⟩ := hJ.live h; exact ⟨q1, q2, by rw [hF.accessible]; exact q3, q4⟩

/-- the stack is untouched by a callee that writes held memory only in `ws` (e.g. `basicMul`) -/
theorem stackBack_keep' {R : RtInv} {L L2 : List (Nat × Nat)} {st : Nat} {m m' : Memory} {ws : List (Nat × Nat)}
    (h : StkOK m R L st) (hF : MemFrame m m' (R.rt ++ ws)) (hLF : LiveFrame m m' L ws) (ho : Outside st 24 ws)
    (he : LiveExt R L L2) : StackBackL R L L2 st m m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e : ∀ k, k + 8 ≤ 24 → m'.readLE (st + k) 8 = m.readLE (st + k) 8 := fun k hk =>
    Held.readLE (h2.sub (by omega) (by omega)) hF hLF (ho.of_sub (by omega) (by omega))
  have e0 := e 0 (by omega); have e1 := e 8 (by omega); have e2 := e 16 (by omega)
  simp only [Nat.add_zero] at e0
  have hW : stW m' st = stW m st := by simp only [stW]; rw [e0]
  have hC : stCap m' st = stCap m st := by simp only [stCap]; rw [e2]
  refine StackBack.toL ⟨⟨h1, he.held h2, by rw [hF.accessible]; exact h3, h4, ?_, ?_, ?_⟩, by simp only [stLen]; rw [e1],
    Or.inl ⟨hW, hC⟩⟩ ⟨hW, hC⟩
  · simp only [stW, stCap] at h5 ⊢; rw [e0, e2]; intro hc
    obtain ⟨q1, q2, q3, q4⟩ := h5 hc; exact ⟨q1, he.held q2, by rw [hF.accessible]; exact q3, q4⟩
  · simp only [stLen, stCap] at h6 ⊢; rw [e1, e2]; exact h6
  · simp only [stCap] at h7 ⊢; rw [e2]; exact h7

/-- the call environment of a callee called at `SP - 176` (any window inside ours) -/
theorem Core.callee {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M) {S1 : State} {stk1 above1 : Nat}
    (hsp : S1.sp.toNat = s.sp.toNat - 176) (hg : S1.regs 28 = s.regs 28) (hF : MemFrame M S1.mem (winA s W 64))
    (hreg : S1.mem.regions = s.mem.regions) (hk : 176 + stk1 ≤ W) (ha : above1 ≤ 168) :
    CallEnv R L1 S1 stk1 above1 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha', hw⟩, hdl, hout, hga, hgr, hLs, hro⟩, -⟩ := hJ.pre
  have hF1 : MemFrame s.mem S1.mem (R.rt ++ winA s W 64) :=
    hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  unfold Apart at hga
  have hgr' : S1.mem.readLE ((S1.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [hg]; exact hF1.readLE _ _ (by
      simp only [winA, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega, by omega⟩)
  have hLs1 := hJ.lsep
  refine ⟨⟨by rw [hg]; exact hg1, by rw [hg, hF1.accessible]; exact hg2, by rw [hgr', hsp]; omega⟩,
    ⟨by omega, by omega, by omega, ?_⟩, ?_, ?_, ?_, by rw [hg]; exact hgr, ?_, hro⟩
  · rw [hF1.accessible, hsp]; exact Memory.accessible_mono _ hw (by omega) (by omega)
  · exact dataLoaded_win hdl hreg hro hF1 hw (by
      intro r hr; simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · intro r hr; have := hLs1 r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega

/-- `z` reused (`2n ≤ cap z`), memory changed in the window only -/
theorem core_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State} {M : Memory}
    (hpre : SPre R b L W zp zc st xp xl xc s) (hc : 2 * xl ≤ zc) (hF : MemFrame s.mem M (winA s W 64)) :
    Core R b L W zp zc st xp xl xc s zp zc L b M := by
  have hpre' := hpre
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, hzc40, hzl, hzw, -, -, -, -, -, -, hinv⟩ := hpre'
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce
  refine ⟨hpre, hF.mono fun a n h => by simp only [outside_append] at h; exact h.2, lf_win [] hF hLs,
    LiveExt.refl R L, Nat.sub_le b _, inv_frame_winA hF hout (by omega) (by decide) hinv, hc, hzc40, ?_, hzw,
    Or.inl ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩
  intro h; obtain ⟨q1, q2, q3, q4⟩ := hzl h; exact ⟨q1, q2, by rw [hF.accessible]; exact q3, q4⟩

/-- the stack is untouched (`n < 12`: no scratch) -/
theorem stackBack_keep {R : RtInv} {L L2 : List (Nat × Nat)} {st : Nat} {m m' : Memory} {rs : List (Nat × Nat)}
    (h : StkOK m R L st) (hF : MemFrame m m' rs) (ho : Outside st 24 rs) (he : LiveExt R L L2) :
    StackBackL R L L2 st m m' := by
  have e1 : m'.readLE (st + 8) 8 = m.readLE (st + 8) 8 := hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  have h' := stkOK_frame h hF ho
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h'
  have hW : stW m' st = stW m st := by simp only [stW]; exact hF.readLE _ _ (ho.of_sub (Nat.le_refl _) (by omega))
  have hC : stCap m' st = stCap m st := by simp only [stCap]; exact hF.readLE _ _ (ho.of_sub (by omega) (by omega))
  refine StackBack.toL ⟨⟨h1, he.held h2, h3, h4, ?_, h6, h7⟩, by simp only [stLen]; rw [e1], Or.inl ⟨hW, hC⟩⟩ ⟨hW, hC⟩
  intro hc; obtain ⟨q1, q2, q3, q4⟩ := h5 hc; exact ⟨q1, he.held q2, q3, q4⟩

/-- `z` fresh from `makeslice(Word, 2n, c)` (called one frame down with the contract's window `cs` inside ours) -/
theorem core_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {M0 m : Memory} {cs : List (Nat × Nat)} {ptr round c : Nat}
    (hpre : SPre R b L W zp zc st xp xl xc s) (hF : MemFrame s.mem M0 (winA s W 64))
    (hcs : ∀ a n, Outside a n (winA s W 64) → Outside a n cs)
    (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ cs))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 28).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hsz : 8 * c ≤ round) (hcost : round ≤ makeB (2 * xl)) (hcap : 2 * xl ≤ c) (hc40 : c < 2 ^ 40) (hc0 : 0 < c)
    (hz : zc < 2 * xl ∨ zp + 8 * zc = xp + 8 * xc) :
    Core R b L W zp zc st xp xl xc s ptr c (L ++ [(ptr, ptr + round)]) (b - round) m := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩, -⟩ := hpre'
  have hin1 : InRanges ptr (8 * c) (L ++ [(ptr, ptr + round)]) :=
    ⟨(ptr, ptr + round), by simp, by simp, by simp only; omega⟩
  have hpo := NatAdd.outside_of_inRanges hout hIn
  refine ⟨hpre, MemFrame.trans hF hMF fun a n h => ?_, LiveFrame.trans (lf_win [] hF hLs) hLF fun _ _ h => h,
    LiveExt.single (by simpa using hIn) (by simpa using hAp), by omega, hinv, hcap, hc40, fun _ =>
    ⟨h8, Or.inl hin1, Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), by omega⟩, ?_,
    Or.inr ⟨hIn.sub (Nat.le_refl _) (by omega), ApartAll.sub' hAp (Nat.le_refl _) (by omega), hin1⟩,
    fun h1 h2 => by omega⟩
  · simp only [outside_append] at h ⊢; exact ⟨h.2, h.1, hcs a n h.2⟩
  · simp only [win, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The post builder**: from `Core` at `M`, the call state's memory `MS` (window stores only), the callee's results
(`p[0:2n] = X²`, live set `L2`, budget, stack back, writes `p[0:2n]` + scratch) and the normalised return `s'`. -/
theorem post_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b L W zp zc st xp xl xc s p c L1 b1 M)
    {MS M2 : Memory} {L2 : List (Nat × Nat)} {b2 k : Nat} (hS : MemFrame M MS (winA s W 64))
    (v2 : natVal M2 p (2 * xl) = natVal s.mem xp xl * natVal s.mem xp xl)
    (e2 : LiveExt R L1 L2) (bud2 : b1 - k ≤ b2) (hk : makeB (2 * xl) + k ≤ sqrC (stLen s.mem st) xl)
    (inv2 : R.inv b2 L2 (s.regs 28).toNat (view R.rt L2 M2))
    (sb2 : StackBackL R L1 L2 st MS M2)
    (F2 : MemFrame MS M2 (R.rt ++ winA s W 64 ++ (p, p + 8 * (2 * xl)) :: stkWs MS st))
    (LF2 : LiveFrame MS M2 L1 ((p, p + 8 * (2 * xl)) :: stkWs MS st))
    {s' : State} {l' : Nat} (F3 : MemFrame M2 s'.mem (winA s W 64))
    (r0 : s'.regs 0 = BitVec.ofNat 64 p) (r1 : s'.regs 1 = BitVec.ofNat 64 l')
    (r2 : s'.regs 2 = BitVec.ofNat 64 c) (hl : l' ≤ 2 * xl)
    (hv : natVal M2 p l' = natVal M2 p (2 * xl)) (hn : NatNorm M2 p l') :
    SPost R b L W zp zc st xp xl xc s s' := by
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, hzl, hzw, -, -, hstk, -, -, -, -⟩ := hJ.pre
  obtain ⟨-, ⟨hal, hb', ha, hw⟩, -, hout, -, -, hLs, -⟩ := hce
  obtain ⟨-, hstok, hstw, -, -, -, -, -, -⟩ := hstk
  have hstok0 := hstok
  obtain ⟨-, hsth, -, -, hsnl, -, -⟩ := hstok0
  have hcap := hJ.cap
  have hpw := hJ.pw
  simp only [win, outside_cons, outside_nil, and_true] at hstw hpw hzw
  -- the stack header: entry = M = MS; M2 = s'
  have hd0 : ∀ k, k + 8 ≤ 24 → M.readLE (st + k) 8 = s.mem.readLE (st + k) 8 := fun k hk =>
    hJ.rd (hsth.sub (by omega) (by omega)) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hd1 : ∀ k, k + 8 ≤ 24 → MS.readLE (st + k) 8 = M.readLE (st + k) 8 := fun k hk =>
    hS.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have hd3 : ∀ k, k + 8 ≤ 24 → s'.mem.readLE (st + k) 8 = M2.readLE (st + k) 8 := fun k hk =>
    F3.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
  have eW : stW MS st = stW s.mem st := by
    have a1 := hd1 0 (by omega); have a0 := hd0 0 (by omega); simp only [Nat.add_zero] at a1 a0
    simp only [stW]; rw [a1, a0]
  have eL : stLen MS st = stLen s.mem st := by
    simp only [stLen]; rw [hd1 8 (by omega), hd0 8 (by omega)]
  have eC : stCap MS st = stCap s.mem st := by
    simp only [stCap]; rw [hd1 16 (by omega), hd0 16 (by omega)]
  have eW' : stW s'.mem st = stW M2 st := by simp only [stW]; have := hd3 0 (by omega); simpa using this
  have eL' : stLen s'.mem st = stLen M2 st := by simp only [stLen]; rw [hd3 8 (by omega)]
  have eC' : stCap s'.mem st = stCap M2 st := by simp only [stCap]; rw [hd3 16 (by omega)]
  have eWs : stkWs MS st = stkWs s.mem st := by simp only [stkWs]; rw [eW, eL, eC]
  rw [eWs] at F2 LF2
  obtain ⟨⟨sbok, sblen, sbor⟩, sbm⟩ := sb2
  have hacc : ∀ a n w, s'.mem.accessible a n w = M.accessible a n w := fun a n w => by
    rw [F3.accessible, F2.accessible, hS.accessible]
  have hext : LiveExt R L L2 := hJ.ext.trans e2
  have hpo : Outside p (8 * l') (winA s W 64) := by
    simp only [winA, outside_cons, outside_nil, and_true]; omega
  have hval : natVal s'.mem p l' = natVal s.mem xp xl * natVal s.mem xp xl := by
    rw [natVal_frame F3 hpo, hv, v2]
  -- the frames
  have hPw : ∀ a n, Outside a n (R.rt ++ winA s W 64 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) →
      a + n ≤ p ∨ p + 8 * (2 * xl) ≤ a := by
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h
    rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
    · omega
    · have := NatAdd.outside_of_inRanges h.1.1.1 hin; omega
  have f1 : MemFrame s.mem MS (R.rt ++ winA s W 64) :=
    hJ.F.trans hS (fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩)
  have hMF : MemFrame s.mem s'.mem (R.rt ++ winA s W 64 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) :=
    chain f1 F2 F3 hPw
  have hLs' : LiveSep L (win s W 64) := hLs
  have hLF : LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st) := by
    refine LiveFrame.trans (LiveFrame.trans (LiveFrame.trans ⟨fun a n hin _ => hJ.LF.readLE a n hin trivial⟩
      (lf_win _ hS hLs') fun _ _ h => h) ?_ fun _ _ h => h) (lf_win _ F3 hLs') fun _ _ h => h
    refine ⟨fun a n hin ho => LF2.readLE a n (hJ.ext.inRanges_old hin) ?_⟩
    simp only [List.cons_append, List.nil_append, outside_cons] at ho ⊢
    refine ⟨?_, ho.2⟩
    rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨-, hap, -⟩
    · have := ho.1; omega
    · have := apart_of_apartAll hap hin; unfold Apart at this; omega
  refine ⟨p, l', c, r0, r1, r2, hval, ?_, by omega, hl, hJ.c40, L2, b2, hext, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hMF, hLF⟩
  · -- normalised
    rcases hn with h | h
    · exact Or.inl h
    · by_cases h0 : l' = 0
      · exact Or.inl h0
      right; rw [F3.readLE _ _ (by simp only [winA, outside_cons, outside_nil, and_true]; omega)]; exact h
  · have := hJ.bud; omega
  · exact inv_frame_winA F3 hout (by omega) (by decide) inv2
  · intro hc; obtain ⟨q1, q2, q3, q4⟩ := hJ.live hc
    exact ⟨q1, e2.held q2, by rw [hacc]; exact q3, q4⟩
  · rcases hJ.kind with h | ⟨hin, hap, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨hcap, hin, hap⟩
  · -- a fresh result is apart from the stack's final array
    intro hne hc0 hcap0
    rcases hJ.kind with h | ⟨hin, hap, hin1⟩
    · exact absurd h hne
    rw [eC'] at hcap0; rw [eW', eC']
    rcases sbor with ⟨h1, h2⟩ | ⟨-, h2⟩
    · rw [h2, eC] at hcap0; rw [h1, h2, eW, eC]
      exact apart_of_held (hsnl hcap0).2.1 hin hap
    · have := apart_of_apartAll h2 hin1; unfold Apart at this ⊢; omega
  · -- reuse: exactly `z[0:2n]` written
    intro h1 h2
    obtain ⟨hp, hc⟩ := hJ.ru h1 h2
    subst hp hc
    refine ⟨rfl, rfl, by rw [natVal_frame F3 (by simp only [winA, outside_cons, outside_nil, and_true]; omega), v2],
      chain f1 F2 F3 fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h; exact h.1.2, ?_⟩
    refine LiveFrame.trans (LiveFrame.trans (LiveFrame.trans ⟨fun a n hin _ => hJ.LF.readLE a n hin trivial⟩
      (lf_win _ hS hLs') fun _ _ h => h) ?_ fun _ _ h => h) (lf_win _ F3 hLs') fun _ _ h => h
    exact ⟨fun a n hin ho => LF2.readLE a n (hJ.ext.inRanges_old hin) ho⟩
  · refine ⟨⟨?_, by rw [eL', sblen, eL], ?_⟩, ?_⟩
    · exact stkOK_frame sbok F3 (by simp only [winA, outside_cons, outside_nil, and_true]; omega)
    · rw [eW', eC']
      rcases sbor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [h1, eW], by rw [h2, eC]⟩
      · exact Or.inr ⟨h1, fun r hr => h2 r (hJ.ext.mem_old hr)⟩
    · rw [eW', eC']; intro hn; apply sbm; rw [eW, eC]; exact hn

end FvModexp.Arm64.NatSqr
