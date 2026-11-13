import FvModexp.Proofs.Amd64.NatQ.KSqrB
import FvModexp.Proofs.Amd64.Nat.StackNatX

/-!
# [amd64 port (divmc s39) of the Q-form Arm64/NatQ/KSqrProD.lean — TIGHT COSTS] `karatsubaSqr` (amd64): the `z1 := stk.nat(2·n2 + 1)` call (natmul.go:291-292) → `KB1` (pure)

`KP … P`: the state at `(*stack).nat`'s entry (`CALL` at `0x5f2573`, return `0x5f2578` pushed at `SP - 320`): `KPre`
at the entry `s`, the normalised halves of `x` (as `KM`), the prologue's frame stores (saved `RBP`, spills, defer
record, the `x0`/`x1`/`z0`/`z2` headers, the push); the prologue wrote only `[SP - 320, SP)` and the spill area.
`ks_natcall`: the call (`StackNatX.sumQ` in `LibSqr`, pre `kNatPre`) and `KB1` from its postcondition (`kmOf`).
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatSqr

variable {H : Nat}

abbrev stkNatA : Nat := 0x5e6480

theorem stkNat_entry : segAddr Extracted.program StackNat.fn = stkNatA := by decide

structure KP (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc : Nat) (s : State)
    (lx0 lx1 : Nat) (P : State) : Prop where
  pre : KPre R b H L W st zp (2 * n) zc xp n xc s
  pc : P.rip = BitVec.ofNat 64 stkNatA
  sp : (P.regs 4).toNat = (s.regs 4).toNat - 320
  g : P.regs 14 = s.regs 14
  fpr : P.regs 5 = s.regs 4 - 8#64
  fs : P.fsBase = s.fsBase
  df : P.df = s.df
  x15 : P.xmm 15 = s.xmm 15
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 3 = BitVec.ofNat 64 (kT n)
  ra : P.mem.readLE ((s.regs 4).toNat - 320) 8 = 0x5f2578
  l0 : lx0 ≤ kn2 n
  v0 : natVal s.mem xp lx0 = natVal s.mem xp (kn2 n)
  nn0 : NatNorm s.mem xp lx0
  l1 : lx1 ≤ n - kn2 n
  v1 : natVal s.mem (xp + 8 * kn2 n) lx1 = natVal s.mem (xp + 8 * kn2 n) (n - kn2 n)
  nn1 : NatNorm s.mem (xp + 8 * kn2 n) lx1
  fr : MemFrame s.mem P.mem [((s.regs 4).toNat - 320, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 48)]
  reg : P.mem.regions = s.mem.regions
  fp : P.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  bit : P.mem.readLE ((s.regs 4).toNat - 249) 1 = 1
  n2s : P.mem.readLE ((s.regs 4).toNat - 248) 8 = kn2 n
  n1s : P.mem.readLE ((s.regs 4).toNat - 240) 8 = 8 * kn2 n
  dfn : P.mem.readLE ((s.regs 4).toNat - 168) 8 = kDfn
  dst : P.mem.readLE ((s.regs 4).toNat - 160) 8 = st
  dln : P.mem.readLE ((s.regs 4).toNat - 152) 8 = stLen s.mem st
  dpt : P.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 168
  s1 : P.mem.readLE ((s.regs 4).toNat + 8) 8 = st
  s2 : P.mem.readLE ((s.regs 4).toNat + 16) 8 = zp
  s3 : P.mem.readLE ((s.regs 4).toNat + 24) 8 = 2 * n
  s4 : P.mem.readLE ((s.regs 4).toNat + 32) 8 = zc
  s5 : P.mem.readLE ((s.regs 4).toNat + 40) 8 = xp
  x0h : IntAt P.mem ((s.regs 4).toNat - 48) 0 xp lx0 xc
  x1h : IntAt P.mem ((s.regs 4).toNat - 80) 0 (xp + 8 * kn2 n) lx1 (xc - kn2 n)
  z0h : Z0H s P.mem zp zc n
  z2h : Z2H s P.mem zp zc n

/-- the window facts of the entry (from `KPre`) -/
theorem KP.lay {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 : Nat} {P : State} (h : KP R b H L W st zp zc xp n xc s lx0 lx1 P) :
    4880 + 16 * n ≤ W ∧ W ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat + 48 ≤ 2 ^ 48 ∧ 80 ≤ n ∧
      n ≤ 2 ^ 12 ∧ n ≤ xc ∧ xc < 2 ^ 40 ∧ 2 * n ≤ zc ∧ zc < 2 ^ 40 ∧
      Outside ((s.regs 4).toNat - W) (W + 48) R.rt ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
      Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - W) (W + 48) := by
  obtain ⟨⟨-, ⟨hb, ha, -⟩, hal, -, hout, hga, hgr, -, -, -⟩, hW, -, -, -, h80, hxc, hxc40, hx12, -, -, -, -, -, hzl, hzc40, -⟩ := h.pre
  unfold ksqrW at hW
  exact ⟨by omega, hb, hal, ha, h80, hx12, hxc, hxc40, by omega, hzc40, hout, hgr, hga⟩

/-- reads outside the prologue's writes are unchanged since the entry -/
theorem KP.rd {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 : Nat} {P : State} (h : KP R b H L W st zp zc xp n xc s lx0 lx1 P) {a k : Nat}
    (ha : a + k ≤ (s.regs 4).toNat - 320 ∨ (s.regs 4).toNat + 48 ≤ a ∨
      ((s.regs 4).toNat ≤ a ∧ a + k ≤ (s.regs 4).toNat + 8)) :
    P.mem.readLE a k = s.mem.readLE a k :=
  h.fr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`stk.nat(2·n2 + 1)`'s precondition** at its entry `P` -/
theorem kNatPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 : Nat} {P : State} (h : KP R b H L W st zp zc xp n xc s lx0 lx1 P) :
    StackNatX.PreQ R b L H 4192 24 st (kT n) P := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨-, -, hw⟩, -, hdl, -, -, -, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩, -, hsv, hglb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hsp, -, hslen, ⟨hlenH, hcost⟩, -, hinv⟩ := h.pre
  obtain ⟨hst0, hsok, hstw, hstg, hsta, hfg, hfw, hsf, hswb, -, -, -, -, -, -⟩ := hsp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwbacc, -, -⟩ := hglb
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hw
  have hspP := h.sp
  have hacc : ∀ a k w, P.mem.accessible a k w = s.mem.accessible a k w := fun a k w => h.fr.accessible a k w
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw
  simp only [guard, BasicSqr.freeP, BasicSqr.freeN] at hstg hfg hfw hsf hsta
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hc40⟩ := hsok
  have eW : P.mem.readLE st 8 = s.mem.readLE st 8 := h.rd (by omega)
  have eL : P.mem.readLE (st + 8) 8 = s.mem.readLE (st + 8) 8 := h.rd (by omega)
  have eC : P.mem.readLE (st + 16) 8 = s.mem.readLE (st + 16) 8 := h.rd (by omega)
  have eG : P.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    unfold Apart at hga; exact h.rd (by omega)
  have eT : P.mem.readLE (s.fsBase.toNat - 8) 8 = s.mem.readLE (s.fsBase.toNat - 8) 8 := by
    unfold Apart at htw; exact h.rd (by omega)
  have hdlP : Extracted.program.DataLoaded P.mem := by
    refine dataLoaded_frame64 hdl h.reg hro (h.fr.widen R.rt) fun r hr hlt => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Janus.Arm64.Memory.accessible_mono _ hw (by simp only; omega) (by simp only; omega)
  simp only [stW, stLen, stCap] at hnl hlc hc40 hstw hfw hsf hsta hslen hlenH
  have hce : CallEnv R L P 4192 24 := by
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, hdlP, ?_, ?_, by rw [h.g]; exact hgr, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [stackguard0Offset, regG]; rw [h.g]; exact hg1
    · simp only [stackguard0Offset, regG]; rw [h.g, hacc]; exact hg2
    · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [h.g, eG, hspP]; omega
    · simp only [regSP]; omega
    · simp only [regSP]; omega
    · simp only [regSP]; rw [hacc, hspP]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    · omega
    · rw [hspP]; exact hout.of_sub (by omega) (by omega)
    · rw [hspP, h.g]; unfold Apart at hga ⊢; omega
    · intro r hr
      have := hLs r hr
      simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hspP]; omega
    · rw [h.fs]; exact htb
    · rw [h.fs, hacc]; exact htr
    · rw [h.fs, eT, htg, h.g]
    · rw [h.fs]; exact htrt
    · rw [h.fs, hspP]; unfold Apart at htw ⊢; omega
  unfold StackNatX.PreQ StkOK
  simp only [stW, stLen, stCap]
  rw [h.g, eW, eL, eC]
  refine ⟨hce,
    hsv, ⟨hst8, hsth, by rw [hacc]; exact hstacc, hst48, fun h0 => ?_, hlc, hc40⟩,
    by simp only [win, outside_cons, outside_nil, and_true, hspP]; omega,
    fun h0 => ⟨by simp only [win, outside_cons, outside_nil, and_true, hspP]; have := (hsta h0).1; simp only [win, outside_cons, outside_nil, and_true] at this; omega,
      by unfold Apart at hsta ⊢; have := (hsta h0).2; omega⟩,
    by simp only [kT, kn2]; omega, by simp only [kT, kn2]; omega,
    ⟨by simp only [kT, kn2]; omega, by rw [stkR_congr (m := s.mem) (m' := P.mem) (by simp only [stCap]; exact eC)]; omega⟩, ?_, by rw [hacc]; exact hwbacc, hswb, hsf⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hnl h0; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  · refine RtInv.inv_frame' h.fr (fun r hr => ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> left <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KB1` from `stk.nat`'s postcondition** (the L form: a grown array is an element of the new live set) -/
theorem kmOf {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State}
    {lx0 lx1 : Nat} {P : State} (h : KP R b H L W st zp zc xp n xc s lx0 lx1 P) {S : State}
    (hpc : S.rip = BitVec.ofNat 64 0x5f2578) (hreg : S.mem.regions = P.mem.regions)
    (hk : S.regs 4 = P.regs 4 + 8 ∧ S.regs 5 = P.regs 5 ∧ S.regs 14 = P.regs 14 ∧ S.xmm 15 = P.xmm 15)
    (hq : StackNatX.PostQ R b L H 4192 24 st (kT n) P S) :
    ∃ (Lk : List (Nat × Nat)) (bk : Nat),
      KB1 R b H L W st zp zc xp n xc s lx0 lx1 (stW S.mem st + 8 * stLen s.mem st) S Lk bk := by
  obtain ⟨hW, hWs, hal, ha48, h80, hn12, hxc, hxc40, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  obtain ⟨efs, edf, hr0, hr1, hr2, Lk, bk, ⟨hext, hbud, hinv⟩, hok, hlen, hsame, hgrow, hF, hLF, hmem⟩ := hq
  have hspP := h.sp
  obtain ⟨⟨-, -, -, -, -, -, -, hLs, -⟩, -, -, hglb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsp, -⟩ := h.pre
  obtain ⟨-, hsok, hstw, -, -, -, hfw, hsf, -, -, -, hfgA, -, -, -⟩ := hsp
  obtain ⟨-, -, -, -, -, -, -, -, hgArt, -, -, -, -⟩ := hglb
  have hsth : Held R L st 24 := hsok.2.1
  have hlc0 : stLen s.mem st ≤ stCap s.mem st := hsok.2.2.2.2.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw hsf hfgA
  have eW : stW P.mem st = stW s.mem st := h.rd (by omega)
  have eL : stLen P.mem st = stLen s.mem st := h.rd (by omega)
  have eC : stCap P.mem st = stCap s.mem st := h.rd (by omega)
  rw [eL, eC] at hsame hgrow hmem
  rw [eL] at hlen
  rw [eW] at hsame
  rw [stkR_congr eC] at hbud; rw [eL] at hr0
  have hkT : 0 < kT n := by simp only [kT]; omega
  have hscr := Scr.of_post (m0 := s.mem) (k := kT n) hok hlen hkT hsame hgrow rfl
  have hacc : ∀ a k w, S.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hF.accessible, h.fr.accessible]
  have hscr' : Scr R L Lk s.mem s.mem st (stW S.mem st + 8 * stLen s.mem st) (kT n) :=
    ⟨hscr.b48, by rw [← hacc]; exact hscr.acc, hscr.al, hscr.held, hscr.loc⟩
  have hlS : stLen S.mem st = stLen s.mem st + StackNat.rnd (kT n) := hlen
  -- reads of the frame after the call (the callee's window ends at `SP - 296`)
  have hrd2 : ∀ a k, (s.regs 4).toNat - 296 ≤ a → a + k ≤ (s.regs 4).toNat + 48 → S.mem.readLE a k = P.mem.readLE a k := by
    intro a k h1 h2
    refine hF.readLE _ _ ?_
    simp only [win, stkWs, outside_append, outside_cons, outside_nil, and_true]
    rw [hspP, eW, eL, eC]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega, by omega⟩
  have hws : stkWs P.mem st = stkWs s.mem st := by simp only [stkWs]; rw [eW, eL, eC]
  refine ⟨Lk, bk, ⟨⟨hpc, by rw [hk.1]; exact sp_add8 hspP (by omega), by rw [hk.2.2.1, h.g], by rw [hk.2.1, h.fpr],
    efs.trans h.fs, edf.trans h.df, by rw [hk.2.2.2, h.x15]⟩,
    ?km, hr0 hkT, hr1, hr2, IntAt.keep h.z0h fun x m h1 h2 => hrd2 x m (by omega) (by omega), ?z2⟩⟩
  case z2 => exact IntAt.keep h.z2h fun x m h1 h2 => hrd2 x m (by omega) (by omega)
  case km =>
  exact
    { pre := h.pre, l0 := h.l0, v0 := h.v0, nn0 := h.nn0, l1 := h.l1, v1 := h.v1, nn1 := h.nn1,
      scr := hscr',
      tsep := ⟨(hscr'.apart hsth fun _ => hsf).symm, by
          simp only [BasicSqr.freeP, BasicSqr.freeN]; rw [hlS]; unfold Apart
          simp only [StackNat.rnd, kT]; omega,
        hscr'.apart (Or.inr hgArt) fun _ => hfgA.symm⟩,
      ext := hext, bud := by unfold kc1; rw [Nat.zero_add]; exact hbud,
      spk := by unfold kc1; exact Nat.zero_le _, inv := by rw [h.g] at hinv; exact hinv,
      reg := hreg.trans h.reg,
      fr := h.fr.trans hF fun a k ho => by
        simp only [win, kws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        rw [hspP, eW, eL, eC]
        obtain ⟨⟨hrt, hw1⟩, hz, hs1, hs2⟩ := ho
        exact ⟨⟨by omega, by omega⟩, ⟨hrt, by omega⟩, hs1, hs2⟩,
      lf := LiveFrame.trans
        ⟨fun a k hin _ => h.fr.readLE a k (by
          have := outside_of_liveSep hin hLs
          simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega)⟩
        (FvModexp.LiveFrame.mono_ws (hws ▸ hLF) fun a k ho => by
          simp only [kws, outside_cons] at ho; exact ho.2) fun _ _ h => h,
      sok := hok, slen := hlS,
      sarr := by
        by_cases hc : stLen s.mem st + StackNat.rnd (kT n) ≤ stCap s.mem st
        · exact Or.inl (hsame hc)
        · exact Or.inr (hgrow (by omega)),
      smem := ArrIn.of_nat hok.2.2.2.2.2.1 hlS hsame hmem,
      lr := (hrd2 _ _ (by omega) (by omega)).trans (h.rd (by omega)),
      fp := (hrd2 _ _ (by omega) (by omega)).trans h.fp,
      bit := (hrd2 _ _ (by omega) (by omega)).trans h.bit,
      n2s := (hrd2 _ _ (by omega) (by omega)).trans h.n2s,
      n1s := (hrd2 _ _ (by omega) (by omega)).trans h.n1s,
      dfn := (hrd2 _ _ (by omega) (by omega)).trans h.dfn,
      dst := (hrd2 _ _ (by omega) (by omega)).trans h.dst,
      dln := (hrd2 _ _ (by omega) (by omega)).trans h.dln,
      dpt := (hrd2 _ _ (by omega) (by omega)).trans h.dpt,
      s1 := (hrd2 _ _ (by omega) (by omega)).trans h.s1,
      s2 := (hrd2 _ _ (by omega) (by omega)).trans h.s2,
      s3 := (hrd2 _ _ (by omega) (by omega)).trans h.s3,
      s4 := (hrd2 _ _ (by omega) (by omega)).trans h.s4,
      s5 := (hrd2 _ _ (by omega) (by omega)).trans h.s5,
      x0h := IntAt.keep h.x0h fun x m h1 h2 => hrd2 x m (by omega) (by omega),
      x1h := IntAt.keep h.x1h fun x m h1 h2 => hrd2 x m (by omega) (by omega) }

/-- `(*stack).nat` (`StackNatX.ensQ`) as a summary in `LibSqr.program` -/
theorem ksNatSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (st k : BitVec 64) :
    Summary (LibSqr.program.link impl) stkNatA
      (fun s => RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) (s.mem.readLE (s.regs regSP).toNat 8) ∧
        s.xmm xmmZero = 0 ∧ ArgsFrom64 s 0 [st, k] ∧ s.df = false ∧ StackNatX.PreQ R b L H 4192 24 st.toNat k.toNat s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        StackNatX.PostQ R b L H 4192 24 st.toNat k.toNat s s') := by
  have hS := StackNatX.sumQ impl hap R hgr hmc hwb H b L st k LibSqr.names (IntAS.sub_of_all (by decide))
  rw [← LibSqr.eq_only, stkNat_entry] at hS
  exact hS

set_option maxRecDepth 20000 in
/-- **The `z1 := stk.nat(2·n2 + 1)` call** from the prologue state `P` (callee entry, return `0x5f2578`) -/
theorem ks_natcall (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc : Nat} {s : State} {lx0 lx1 : Nat} {P : State}
    (h : KP R b H L W st zp zc xp n xc s lx0 lx1 P) (hx150 : s.xmm 15 = 0#128) (hdf0 : s.df = false)
    {ret : W64} {Q : State → Prop}
    (hK : ∀ (S : State) (Lk : List (Nat × Nat)) (bk : Nat),
      KB1 R b H L W st zp zc xp n xc s lx0 lx1 (stW S.mem st + 8 * stLen s.mem st) S Lk bk →
      ReachesRet (LibSqr.program.link impl) ret S Q) :
    ReachesRet (LibSqr.program.link impl) ret P Q := by
  have hb := h.lay
  have hst : st < 2 ^ 64 := by
    have := (h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 : StkPre R L s W 48 st).2.1.2.2.2.1; omega
  have hkt : kT n < 2 ^ 64 := by simp only [kT, kn2]; omega
  have hrd : P.mem.readLE (P.regs 4).toNat 8 = 0x5f2380 + 504 := by rw [h.sp, h.ra]
  refine ReachesRet.call_regions (ksNatSum impl hap R hgr hmc hwb H b L (BitVec.ofNat 64 st) (BitVec.ofNat 64 (kT n)))
    h.pc ⟨?_, h.x15.trans hx150, by simp [ArgsFrom64, argReg, intArgRegs, h.r0, h.r1], h.df.trans hdf0, ?_⟩
    fun s2 hr hq hreg => ?_
  · simp only [regSP]; rw [hrd]; exact ks_ra hap (by decide) 504 (by decide)
  · rw [tN' hst, tN' hkt]; exact kNatPre h
  · obtain ⟨hk, hq⟩ := hq
    rw [tN' hst, tN' hkt] at hq
    obtain ⟨Lk, bk, hB⟩ := kmOf h (by rw [hr, retAddrOf, hrd]) hreg hk hq
    exact hK s2 Lk bk hB

end FvModexp.Amd64.Q.NatSqr
