import FvModexp.Proofs.Amd64.NatQ.MulDefs
import FvModexp.Proofs.Amd64.NatQ.SqrRel

set_option autoImplicit false

/-!
# [amd64 port (divmc s43) of the Q-form Arm64/NatQ/MulRel.lean — TIGHT COSTS] `nat.mul` (amd64): the relation after `z = z.make(m + n)` and the pure post builder

`Core … p c L1 b1 M`: the result array `(p, c)` (`z`'s own when reused, else fresh from `makeslice`), live set `L1`,
budget `b1`, memory `M` after `z.make` (`m = len x ≥ n = len y ≥ 2`); the paths `basicMul` / `karatsuba` (+ chunk loop)
write `p[0:m+n]` (and the stack scratch), normalise and return: `post_of` builds `MPost` from the callee's facts.
`JoinAt`: registers and spills at the join `0x5f09d5` after `make` (amd64 frame: `PUSHQ BP; SUBQ $0xf8` →
`SP' = RSP - 256`, callees entered at `RSP - 264`; `y` is a stack argument at `RSP + 8 / + 16 / + 24`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (outside_of_liveSep apart_of_apartAll apart_of_held stkOK_frame chain inv_frame_win)

/-- the window-only frame keeps the live objects (any `above`) -/
theorem lf_win' {L : List (Nat × Nat)} {s : State} {W ab : Nat} {m m' : Memory} (ws : List (Nat × Nat))
    (h : MemFrame m m' (win s W ab)) (hs : LiveSep L (win s W ab)) : LiveFrame m m' L ws :=
  ⟨fun a n hin _ => h.readLE a n (outside_of_liveSep hin hs)⟩

/-- the state after `z = z.make(m + n)` -/
structure Core (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W zp zc st xp xl xc yp yl yc : Nat) (s : State)
    (p c : Nat) (L1 : List (Nat × Nat)) (b1 : Nat) (M : Memory) : Prop where
  pre : MPre R b H L W zp zc st xp xl xc yp yl yc s
  F : MemFrame s.mem M (R.rt ++ win s W 88)
  LF : LiveFrame s.mem M L []
  ext : LiveExt R L L1
  bud : b - makeB (xl + yl) ≤ b1
  inv : R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M)
  cap : xl + yl ≤ c
  c40 : c < 2 ^ 40
  live : NatLive M R L1 p c
  pw : Outside p (8 * c) (win s W 88)
  kind : (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L ∧ InRanges p (8 * c) L1)
  ru : xl + yl ≤ zc → zp + 8 * zc ≠ xp + 8 * xc → zp + 8 * zc ≠ yp + 8 * yc → p = zp ∧ c = zc

/-- the registers and spills at the join after `z = z.make(m + n)` (`0x5f09d5`, after `MOVQ CX, 0x58(SP);
MOVQ AX, 0x90(SP)`): `AX, BX, CX = (p, m+n, c)`, `DI = stk`, `SI, R8, R9 = x`, `DX, R10, R11 = y`;
`SP' = RSP - 256`, `BP = RSP - 8`; `p`, `m + n`, `c` spilled at `0x90`, `0x70`, `0x58(SP')` = `RSP - 112`, `- 144`,
`- 168`; `x` spilled at `RSP + 64 / 72 / 80`, `y` (stack argument) at `RSP + 8 / 16 / 24`; the return address at `RSP`
and the caller's `BP` at `RSP - 8` -/
structure JoinAt (s S : State) (p c : Nat) (st xp xl xc yp yl yc : BitVec 64) : Prop where
  pc : S.rip = BitVec.ofNat 64 0x5f09d5
  r0 : S.regs 0 = BitVec.ofNat 64 p
  r3 : S.regs 3 = BitVec.ofNat 64 (xl.toNat + yl.toNat)
  r1 : S.regs 1 = BitVec.ofNat 64 c
  r7 : S.regs 7 = st
  r6 : S.regs 6 = xp
  r8 : S.regs 8 = xl
  r9 : S.regs 9 = xc
  r2 : S.regs 2 = yp
  r10 : S.regs 10 = yl
  r11 : S.regs 11 = yc
  sp : S.regs 4 = s.regs 4 - 256#64
  g : S.regs 14 = s.regs 14
  bp : S.regs 5 = s.regs 4 - 8#64
  fs : S.fsBase = s.fsBase
  df : S.df = s.df
  x15 : S.xmm 15 = s.xmm 15
  mra : S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
  mbp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  m112 : S.mem.readLE ((s.regs 4).toNat - 112) 8 = p
  m144 : S.mem.readLE ((s.regs 4).toNat - 144) 8 = xl.toNat + yl.toNat
  m168 : S.mem.readLE ((s.regs 4).toNat - 168) 8 = c
  m64 : S.mem.readLE ((s.regs 4).toNat + 64) 8 = xp.toNat
  m72 : S.mem.readLE ((s.regs 4).toNat + 72) 8 = xl.toNat
  m80 : S.mem.readLE ((s.regs 4).toNat + 80) 8 = xc.toNat
  m8 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = yp.toNat
  m16 : S.mem.readLE ((s.regs 4).toNat + 16) 8 = yl.toNat
  m24 : S.mem.readLE ((s.regs 4).toNat + 24) 8 = yc.toNat
  reg : S.mem.regions = s.mem.regions
  px : Apart p (8 * c) xp.toNat (8 * xl.toNat)
  py : Apart p (8 * c) yp.toNat (8 * yl.toNat)
  nax : p + 8 * c ≠ xp.toNat + 8 * xc.toNat
  nay : p + 8 * c ≠ yp.toNat + 8 * yc.toNat

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
  {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}

/-- a held range outside the window keeps its bytes from the entry to `M` -/
theorem Core.rd (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) {a n : Nat} (hh : Held R L a n)
    (ho : Outside a n (win s W 88)) : M.readLE a n = s.mem.readLE a n :=
  Held.readLE hh hJ.F ⟨fun a n hin _ => hJ.LF.readLE a n hin trivial⟩ ho

theorem Core.hdr (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) (k : Nat) (hk : k + 8 ≤ 24) :
    M.readLE (st + k) 8 = s.mem.readLE (st + k) 8 := by
  obtain ⟨-, -, -, -, -, -, ⟨-, ⟨-, hsth, -⟩, hstw, -⟩, -, -, -⟩ := hJ.pre
  exact hJ.rd (hsth.sub (by omega) (by omega)) (hstw.of_sub (by omega) (by omega))

/-- the stack object at `M` -/
theorem Core.stk (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) : StkOK M R L1 st := by
  obtain ⟨-, -, -, -, -, -, ⟨-, hstok, -⟩, -, -, -⟩ := hJ.pre
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hstok
  have e0 := hJ.hdr 0 (by omega); have e1 := hJ.hdr 8 (by omega); have e2 := hJ.hdr 16 (by omega)
  simp only [Nat.add_zero] at e0
  refine ⟨h1, hJ.ext.held h2, by rw [hJ.F.accessible]; exact h3, h4, ?_, ?_, ?_⟩
  · simp only [stW, stCap] at h5 ⊢; rw [e0, e2]; intro hc
    obtain ⟨q1, q2, q3, q4⟩ := h5 hc; exact ⟨q1, hJ.ext.held q2, by rw [hJ.F.accessible]; exact q3, q4⟩
  · simp only [stLen, stCap] at h6 ⊢; rw [e1, e2]; exact h6
  · simp only [stCap] at h7 ⊢; rw [e2]; exact h7

/-- the live set after `make` is outside the window -/
theorem Core.lsep (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) : LiveSep L1 (win s W 88) := by
  obtain ⟨⟨-, ⟨hb', -, -⟩, -, -, hout, -, -, hLs, -⟩, -⟩ := hJ.pre
  simp only [regSP] at hb'
  exact IntAS.liveSep_ext hJ.ext hLs fun r hr => by
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; simp only
    rw [show (s.regs 4).toNat + 88 - ((s.regs 4).toNat - W) = W + 88 by omega]; exact hout

/-- window stores after `make` keep `Core` -/
theorem Core.wfr (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) {M' : Memory}
    (hF : MemFrame M M' (win s W 88)) : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M' := by
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -⟩, -⟩ := hJ.pre
  refine ⟨hJ.pre, hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩,
    LiveFrame.trans hJ.LF (lf_win' [] hF hLs) fun _ _ h => h, hJ.ext, hJ.bud,
    inv_frame_win hF hout (by omega) (by decide) hJ.inv, hJ.cap, hJ.c40, ?_, hJ.pw, hJ.kind, hJ.ru⟩
  intro h; obtain ⟨q1, q2, q3, q4⟩ := hJ.live h; exact ⟨q1, q2, by rw [hF.accessible]; exact q3, q4⟩

/-- the call environment of a callee entered at `RSP - 264` (`CALL` from `SP' = RSP - 256`; any window inside ours) -/
theorem Core.callee (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M) {S1 : State} {stk1 above1 : Nat}
    (hsp : (S1.regs 4).toNat = (s.regs 4).toNat - 264) (hg : S1.regs 14 = s.regs 14) (hfs : S1.fsBase = s.fsBase)
    (hF : MemFrame M S1.mem (win s W 88))
    (hreg : S1.mem.regions = s.mem.regions) (hk : 264 + stk1 ≤ W) (ha : above1 ≤ 352) :
    CallEnv R L1 S1 stk1 above1 := by
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb, ha', hw⟩, hal, hdl, hout, hga, hgr, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩, -⟩ := hJ.pre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb ha' hw
  have hF1 : MemFrame s.mem S1.mem (R.rt ++ win s W 88) :=
    hJ.F.trans hF fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩
  unfold Apart at hga htw
  have hgr' : S1.mem.readLE ((S1.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hg]; exact hF1.readLE _ _ (by
      simp only [win, outside_append, outside_cons, outside_nil, and_true]; exact ⟨hgr, by omega⟩)
  have htls : S1.mem.readLE (S1.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
    rw [hfs]; exact hF1.readLE _ _ (by
      simp only [win, outside_append, outside_cons, outside_nil, and_true]; exact ⟨htrt, by omega⟩)
  have hLs1 := hJ.lsep
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [stackguard0Offset, regG]; rw [hg]; exact hg1
  · simp only [stackguard0Offset, regG]; rw [hg, hF1.accessible]; exact hg2
  · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [hg] at hgr' ⊢; rw [hgr', hsp]; omega
  · first | omega | (simp only [stackguard0Offset, regG, regSP]; omega) | (simp_all only [stackguard0Offset, regG, regSP, Apart]; omega)
  · simp only [regSP]; omega
  · simp only [regSP]; omega
  · simp only [regSP]; rw [hF1.accessible, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  · omega
  · exact dataLoaded_frame64 hdl hreg hro hF1 (by
      intro r hr _; simp only [win, List.mem_singleton] at hr; subst hr
      simp only; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega))
  · rw [hsp]; exact hout.of_sub (by omega) (by omega)
  · rw [hsp, hg]; unfold Apart; omega
  · rw [hg]; exact hgr
  · intro r hr; have := hLs1 r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hsp]; omega
  · rw [hfs]; exact htb
  · rw [hfs, hF1.accessible]; exact htr
  · rw [htls, htg, hg]
  · rw [hfs]; exact htrt
  · rw [hfs, hsp]; unfold Apart; omega

end

/-- `z` reused (`m + n ≤ cap z`), memory changed in the window only -/
theorem core_reuse {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {M : Memory} (hpre : MPre R b H L W zp zc st xp xl xc yp yl yc s) (hc : xl + yl ≤ zc)
    (hF : MemFrame s.mem M (win s W 88)) :
    Core R b H L W zp zc st xp xl xc yp yl yc s zp zc L b M := by
  have hpre' := hpre
  obtain ⟨hce, -, -, -, -, ⟨-, -, ⟨hzc40, hzl, hzw, -⟩, -⟩, -, -, -, hinv⟩ := hpre'
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -⟩ := hce
  refine ⟨hpre, hF.mono fun a n h => by simp only [outside_append] at h; exact h.2, lf_win' [] hF hLs,
    LiveExt.refl R L, Nat.sub_le b _, inv_frame_win hF hout (by omega) (by decide) hinv, hc, hzc40, ?_, hzw,
    Or.inl ⟨rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩
  intro h; obtain ⟨q1, q2, q3, q4⟩ := hzl h; exact ⟨q1, q2, by rw [hF.accessible]; exact q3, q4⟩

/-- `z` fresh from `makeslice(Word, m + n, c)` (called one frame down with the contract's window `cs` inside ours) -/
theorem core_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {M0 m : Memory} {cs : List (Nat × Nat)} {ptr round c : Nat}
    (hpre : MPre R b H L W zp zc st xp xl xc yp yl yc s) (hF : MemFrame s.mem M0 (win s W 88))
    (hcs : ∀ a n, Outside a n (win s W 88) → Outside a n cs)
    (hLF : LiveFrame M0 m L []) (hMF : MemFrame M0 m (R.rt ++ cs))
    (hAp : ApartAll ptr round L) (hIn : InRanges ptr round R.rt) (hle : ptr + round ≤ 2 ^ 48)
    (hacc : m.accessible ptr round true = true) (h8 : ptr % 8 = 0)
    (hinv : R.inv (b - round) (L ++ [(ptr, ptr + round)]) (s.regs 14).toNat (view R.rt (L ++ [(ptr, ptr + round)]) m))
    (hsz : 8 * c ≤ round) (hcost : round ≤ makeB (xl + yl)) (hcap : xl + yl ≤ c) (hc40 : c < 2 ^ 40) (hc0 : 0 < c)
    (hz : zc < xl + yl ∨ zp + 8 * zc = xp + 8 * xc ∨ zp + 8 * zc = yp + 8 * yc) :
    Core R b H L W zp zc st xp xl xc yp yl yc s ptr c (L ++ [(ptr, ptr + round)]) (b - round) m := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -⟩, -⟩ := hpre'
  have hin1 : InRanges ptr (8 * c) (L ++ [(ptr, ptr + round)]) :=
    ⟨(ptr, ptr + round), by simp, by simp, by simp only; omega⟩
  have hpo := NatAdd.outside_of_inRanges hout hIn
  refine ⟨hpre, MemFrame.trans hF hMF fun a n h => ?_, LiveFrame.trans (lf_win' [] hF hLs) hLF fun _ _ h => h,
    LiveExt.single (by simpa using hIn) (by simpa using hAp), by omega, hinv, hcap, hc40, fun _ =>
    ⟨h8, Or.inl hin1, Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), by omega⟩, ?_,
    Or.inr ⟨hIn.sub (Nat.le_refl _) (by omega), ApartAll.sub' hAp (Nat.le_refl _) (by omega), hin1⟩,
    fun h1 h2 h3 => by omega⟩
  · simp only [outside_append] at h ⊢; exact ⟨h.2, h.1, hcs a n h.2⟩
  · simp only [win, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The post builder**: from `Core` at `M`, the call state's memory `MS` (window stores only), the callees' results
(`p[0:m+n] = X·Y`, live set `L2`, budget, stack back, writes `p[0:m+n]` + scratch) and the normalised return `s'`. -/
theorem post_of {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W zp zc st xp xl xc yp yl yc : Nat} {s : State}
    {p c : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {M : Memory}
    (hJ : Core R b H L W zp zc st xp xl xc yp yl yc s p c L1 b1 M)
    {MS M2 : Memory} {L2 : List (Nat × Nat)} {b2 k : Nat} (hS : MemFrame M MS (win s W 88))
    (v2 : natVal M2 p (xl + yl) = natVal s.mem xp xl * natVal s.mem yp yl)
    (e2 : LiveExt R L1 L2) (bud2 : b1 - (k + stkR H MS st) + stkR H M2 st ≤ b2 ∨ (b1 - k ≤ b2 ∧ stCap M2 st = stCap MS st))
    (hk : makeB (xl + yl) + k ≤ mulCQ xl yl)
    (inv2 : R.inv b2 L2 (s.regs 14).toNat (view R.rt L2 M2))
    (sb2 : StackBackL R L1 L2 st MS M2)
    (F2 : MemFrame MS M2 (R.rt ++ win s W 88 ++ (p, p + 8 * (xl + yl)) :: stkWs MS st))
    (LF2 : LiveFrame MS M2 L1 ((p, p + 8 * (xl + yl)) :: stkWs MS st))
    {s' : State} {l' : Nat} (F3 : MemFrame M2 s'.mem (win s W 88))
    (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (r0 : s'.regs 0 = BitVec.ofNat 64 p) (r1 : s'.regs 3 = BitVec.ofNat 64 l')
    (r2 : s'.regs 1 = BitVec.ofNat 64 c) (hl : l' ≤ xl + yl)
    (hv : natVal M2 p l' = natVal M2 p (xl + yl)) (hn : NatNorm M2 p l') :
    MPost R b H L W zp zc st xp xl xc yp yl yc s s' := by
  obtain ⟨hce, -, -, -, -, ⟨-, -, ⟨-, hzl, hzw, -⟩, -⟩, hstk, -, -, -⟩ := hJ.pre
  obtain ⟨-, ⟨hb', ha, hw⟩, hal, -, hout, -, -, hLs, -⟩ := hce
  obtain ⟨-, hstok, hstw, -, -, -, -, -, -⟩ := hstk
  have hstok0 := hstok
  obtain ⟨-, hsth, -, -, hsnl, -, -⟩ := hstok0
  have hcap := hJ.cap
  have hpw := hJ.pw
  simp only [win, outside_cons, outside_nil, and_true] at hstw hpw hzw
  have hd0 : ∀ k, k + 8 ≤ 24 → M.readLE (st + k) 8 = s.mem.readLE (st + k) 8 := fun k hk =>
    hJ.rd (hsth.sub (by omega) (by omega)) (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hd1 : ∀ k, k + 8 ≤ 24 → MS.readLE (st + k) 8 = M.readLE (st + k) 8 := fun k hk =>
    hS.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
  have hd3 : ∀ k, k + 8 ≤ 24 → s'.mem.readLE (st + k) 8 = M2.readLE (st + k) 8 := fun k hk =>
    F3.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)
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
  have hpo : Outside p (8 * l') (win s W 88) := by
    simp only [win, outside_cons, outside_nil, and_true]; omega
  have hval : natVal s'.mem p l' = natVal s.mem xp xl * natVal s.mem yp yl := by
    rw [natVal_frame F3 hpo, hv, v2]
  have hPw : ∀ a n, Outside a n (R.rt ++ win s W 88 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) →
      a + n ≤ p ∨ p + 8 * (xl + yl) ≤ a := by
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h
    rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨hin, -, -⟩
    · omega
    · have := NatAdd.outside_of_inRanges h.1.1.1 hin; omega
  have f1 : MemFrame s.mem MS (R.rt ++ win s W 88) :=
    hJ.F.trans hS (fun a n h => ⟨h, by simp only [outside_append] at h; exact h.2⟩)
  have hMF : MemFrame s.mem s'.mem (R.rt ++ win s W 88 ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) :=
    chain f1 F2 F3 hPw
  have hLs' : LiveSep L (win s W 88) := hLs
  have hLF : LiveFrame s.mem s'.mem L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st) := by
    refine LiveFrame.trans (LiveFrame.trans (LiveFrame.trans ⟨fun a n hin _ => hJ.LF.readLE a n hin trivial⟩
      (lf_win' _ hS hLs') fun _ _ h => h) ?_ fun _ _ h => h) (lf_win' _ F3 hLs') fun _ _ h => h
    refine ⟨fun a n hin ho => LF2.readLE a n (hJ.ext.inRanges_old hin) ?_⟩
    simp only [List.cons_append, List.nil_append, outside_cons] at ho ⊢
    refine ⟨?_, ho.2⟩
    rcases hJ.kind with ⟨rfl, rfl⟩ | ⟨-, hap, -⟩
    · have := ho.1; omega
    · have := apart_of_apartAll hap hin; unfold Apart at this; omega
  refine ⟨hfs, hdf, p, l', c, r0, r1, r2, hval, ?_, by omega, hl, hJ.c40, L2, b2, hext, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hMF, hLF⟩
  · rcases hn with h | h
    · exact Or.inl h
    · by_cases h0 : l' = 0
      · exact Or.inl h0
      right; rw [F3.readLE _ _ (by simp only [win, outside_cons, outside_nil, and_true]; omega)]; exact h
  · have := hJ.bud; have hcq := (hJ.pre.2.2.2.2.2.2.2.1).2
    rw [stkR_congr eC']
    rcases bud2 with h | ⟨h, hc⟩
    · rw [stkR_congr eC] at h; omega
    · rw [stkR_congr (hc.trans eC)]; omega
  · exact inv_frame_win F3 hout (by omega) (by decide) inv2
  · intro hc; obtain ⟨q1, q2, q3, q4⟩ := hJ.live hc
    exact ⟨q1, e2.held q2, by rw [hacc]; exact q3, q4⟩
  · rcases hJ.kind with h | ⟨hin, hap, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨hcap, hin, hap⟩
  · intro hne hc0 hcap0
    rcases hJ.kind with h | ⟨hin, hap, hin1⟩
    · exact absurd h hne
    rw [eC'] at hcap0; rw [eW', eC']
    rcases sbor with ⟨h1, h2⟩ | ⟨-, h2⟩
    · rw [h2, eC] at hcap0; rw [h1, h2, eW, eC]
      exact apart_of_held (hsnl hcap0).2.1 hin hap
    · have := apart_of_apartAll h2 hin1; unfold Apart at this ⊢; omega
  · intro h1 h2 h3
    obtain ⟨hp, hc⟩ := hJ.ru h1 h2 h3
    subst hp hc
    refine ⟨rfl, rfl, Or.inl (by rw [natVal_frame F3 (by simp only [win, outside_cons, outside_nil, and_true]; omega),
      v2]), chain f1 F2 F3 fun a n h => by
        simp only [outside_append, outside_cons, outside_nil, and_true] at h; exact h.1.2, ?_⟩
    refine LiveFrame.trans (LiveFrame.trans (LiveFrame.trans ⟨fun a n hin _ => hJ.LF.readLE a n hin trivial⟩
      (lf_win' _ hS hLs') fun _ _ h => h) ?_ fun _ _ h => h) (lf_win' _ F3 hLs') fun _ _ h => h
    exact ⟨fun a n hin ho => LF2.readLE a n (hJ.ext.inRanges_old hin) ho⟩
  · refine ⟨⟨?_, by rw [eL', sblen, eL], ?_⟩, ?_⟩
    · exact stkOK_frame sbok F3 (by simp only [win, outside_cons, outside_nil, and_true]; omega)
    · rw [eW', eC']
      rcases sbor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [h1, eW], by rw [h2, eC]⟩
      · exact Or.inr ⟨h1, fun r hr => h2 r (hJ.ext.mem_old hr)⟩
    · simp only [ArrIn]; rw [eW', eC']; intro hn; apply sbm; rw [eW, eC]; exact hn

end FvModexp.Amd64.Q.NatMul
