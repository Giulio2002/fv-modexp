import FvModexp.Proofs.Arm64.Nat.KMulPD
import FvModexp.Proofs.Arm64.Nat.KSqrProD
import FvModexp.Proofs.Common.StkFrame

set_option autoImplicit false

/-!
# `karatsuba` (arm64): the `z1 := stk.nat(2·n2 + 1)` call (natmul.go:203-204) and the headers after it (pure)

`KPm … P`: the state at `(*stack).nat`'s entry (`CALL` at `0x1bc098`, return `0x1bc09c`): `KPre` at the entry `s`, the
normalised halves of `x` and `y`, the prologue's frame stores (frame record, spills, `2·n2`/`n2`/`n + 1` slots, defer
record, the `x0 x1 y0 y1 z0 z2` headers), only our frame written. `kmNatPre`: the call's precondition; `kmNatSum`: the
callee summary in `LibMul`; `kmFin`: `KM1` at `0x1bc10c` from the callee's postcondition and the post-call stores
(`z1`/`tx`/`ty` headers, `SP-352 := zc - n2`, `SP-336 := zp + 8·n2`). (Adapted from this repo's `KSqrProD`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.NatMul

open FvModexp.Arm64.RunIface (Serves Globals)
open FvModexp.Arm64.NatSqr (StkPre StkSep IntAt stkNatA stkNat_entry)

structure KPm (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 : Nat) (P : State) : Prop where
  pre : KPre R b L W st zp (2 * n) zc xp n xc yp n yc s
  pc : P.pc = BitVec.ofNat 64 stkNatA
  sp : P.sp = s.sp - 448#64
  g : P.regs 28 = s.regs 28
  fpr : P.regs 29 = s.sp - 456#64
  r18 : P.regs 18 = s.regs 18
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 1 = BitVec.ofNat 64 (kT n)
  r30 : P.regs 30 = BitVec.ofNat 64 0x1bc09c
  l0 : lx0 ≤ kh n
  v0 : natVal s.mem xp lx0 = natVal s.mem xp (kh n)
  nn0 : NatNorm s.mem xp lx0
  l1 : lx1 ≤ n - kh n
  v1 : natVal s.mem (xp + 8 * kh n) lx1 = natVal s.mem (xp + 8 * kh n) (n - kh n)
  nn1 : NatNorm s.mem (xp + 8 * kh n) lx1
  m0 : ly0 ≤ kh n
  w0 : natVal s.mem yp ly0 = natVal s.mem yp (kh n)
  mn0 : NatNorm s.mem yp ly0
  m1 : ly1 ≤ n - kh n
  w1 : natVal s.mem (yp + 8 * kh n) ly1 = natVal s.mem (yp + 8 * kh n) (n - kh n)
  mn1 : NatNorm s.mem (yp + 8 * kh n) ly1
  fr : MemFrame s.mem P.mem [(s.sp.toNat - 456, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)]
  reg : P.mem.regions = s.mem.regions
  lr : P.mem.readLE (s.sp.toNat - 448) 8 = (s.regs 30).toNat
  fp : P.mem.readLE (s.sp.toNat - 456) 8 = (s.regs 29).toNat
  bit : P.mem.readLE (s.sp.toNat - 361) 1 = 1
  q88 : P.mem.readLE (s.sp.toNat - 360) 8 = 2 * kh n
  q96 : P.mem.readLE (s.sp.toNat - 352) 8 = kh n
  q104 : P.mem.readLE (s.sp.toNat - 344) 8 = n + 1
  dfn : P.mem.readLE (s.sp.toNat - 232) 8 = kDfn
  dst : P.mem.readLE (s.sp.toNat - 224) 8 = st
  dln : P.mem.readLE (s.sp.toNat - 216) 8 = stLen s.mem st
  dpt : P.mem.readLE (s.sp.toNat - 16) 8 = s.sp.toNat - 232
  s1 : P.mem.readLE (s.sp.toNat + 8) 8 = st
  s2 : P.mem.readLE (s.sp.toNat + 16) 8 = zp
  s3 : P.mem.readLE (s.sp.toNat + 24) 8 = 2 * n
  s4 : P.mem.readLE (s.sp.toNat + 32) 8 = zc
  s5 : P.mem.readLE (s.sp.toNat + 40) 8 = xp
  s6 : P.mem.readLE (s.sp.toNat + 64) 8 = yp
  x0h : IntAt P.mem (s.sp.toNat - 48) 0 xp lx0 xc
  x1h : IntAt P.mem (s.sp.toNat - 80) 0 (xp + 8 * kh n) lx1 (xc - kh n)
  y0h : IntAt P.mem (s.sp.toNat - 112) 0 yp ly0 yc
  y1h : IntAt P.mem (s.sp.toNat - 144) 0 (yp + 8 * kh n) ly1 (yc - kh n)
  z0h : Z0H s P.mem zp zc n
  z2h : Z2H s P.mem zp zc n

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 : Nat} {P : State}

theorem KPm.spN (h : KPm R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P) :
    P.sp.toNat = s.sp.toNat - 448 := by
  have F := h.pre.F
  obtain ⟨-, ⟨-, hb, -, -⟩, -⟩ := F.env
  have := F.hW; have := kW_ge n
  rw [h.sp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- reads outside our frame's writes are unchanged since the entry -/
theorem KPm.rd (h : KPm R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P) {a k : Nat}
    (ha : a + k ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 72 ≤ a ∨ (s.sp.toNat - 8 ≤ a ∧ a + k ≤ s.sp.toNat + 8)) :
    P.mem.readLE a k = s.mem.readLE a k :=
  h.fr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)

end

set_option maxRecDepth 20000 in
/-- **`stk.nat(2·n2 + 1)`'s precondition** at its entry `P` -/
theorem kmNatPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 : Nat} {P : State} (h : KPm R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P) :
    StackNat.Pre R b L 4208 24 st (kT n) P := by
  have F := h.pre.F
  have hW := F.hW; have hW' := kW_ge n
  have h40 := F.n40; have hn12 := F.n12
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hWs, ha48, hw⟩, hdl, hout, hga, hgr, hLs, hro⟩ := F.env
  have hsv := F.sv
  have hsp := F.stk
  have hslb := F.slb
  have hcost := F.cost
  have hinv := F.inv
  obtain ⟨hst0, hsok, hstw, hstg, hsta, hfg, hfw, hsf, hswb, -, -, -⟩ := hsp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwbacc, -, -⟩ := F.gl
  clear F
  have hspP : P.sp.toNat = s.sp.toNat - 448 := h.spN
  have hacc : ∀ a k w, P.mem.accessible a k w = s.mem.accessible a k w := fun a k w => h.fr.accessible a k w
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw hLs
  simp only [NatSqr.guard, BasicSqr.freeP, BasicSqr.freeN] at hstg hfg hfw hsf hsta
  obtain ⟨hst8, hsth, hstacc, hst48, hnl, hlc, hc40⟩ := hsok
  have eW : P.mem.readLE st 8 = s.mem.readLE st 8 := h.rd (by omega)
  have eL : P.mem.readLE (st + 8) 8 = s.mem.readLE (st + 8) 8 := h.rd (by omega)
  have eC : P.mem.readLE (st + 16) 8 = s.mem.readLE (st + 16) 8 := h.rd (by omega)
  have eG : P.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    unfold Apart at hga; exact h.rd (by omega)
  have hc1 : stackNatCost (stLen s.mem st) (kT n) ≤ b := by
    have h7 := kc7_le (stLen s.mem st) n
    unfold kc7 kc6 kc5 kc4 kc3 kc2b kc2 kc1 at h7; omega
  have hdlP : Extracted.program.DataLoaded P.mem :=
    dataLoaded_win hdl h.reg hro (h.fr.widen R.rt) hw (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega)
  simp only [stW, stLen, stCap] at hnl hlc hc40 hstw hfw hsf hsta hc1 hslb
  unfold StackNat.Pre CallEnv GuardOK StackOK StkOK
  simp only [stW, stLen, stCap]
  rw [h.g, eW, eL, eC]
  refine ⟨⟨⟨hg1, by rw [hacc]; exact hg2, by rw [eG, hspP]; omega⟩, ⟨by rw [hspP]; omega, by rw [hspP]; omega,
      by rw [hspP]; omega, by rw [hacc, hspP]; exact Memory.accessible_mono _ hw (by omega) (by omega)⟩, hdlP,
      by rw [hspP]; exact hout.of_sub (by omega) (by omega), by rw [hspP]; unfold Apart at hga ⊢; omega, hgr,
      fun r hr => by
        have := hLs r hr; simp only [win, outside_cons, outside_nil, and_true] at this ⊢; rw [hspP]; omega, hro⟩,
    hsv, ⟨hst8, hsth, by rw [hacc]; exact hstacc, hst48, fun h0 => ?_, hlc, hc40⟩,
    by simp only [win, outside_cons, outside_nil, and_true]; rw [hspP]; omega,
    fun h0 => ⟨by
        simp only [win, outside_cons, outside_nil, and_true]; rw [hspP]; have := (hsta h0).1
        simp only [win, outside_cons, outside_nil, and_true] at this; omega,
      by unfold Apart at hsta ⊢; have := (hsta h0).2; omega⟩,
    by simp only [kT, kh]; omega, by simp only [kT, kh]; omega, hc1, ?_, by rw [hacc]; exact hwbacc, hswb, hsf⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hnl h0; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  · refine RtInv.inv_frame' h.fr (fun r hr => ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> left <;> exact hout.of_sub (by omega) (by omega)

/-- `(*stack).nat` (`StackNat.ensL`) as a summary in `LibMul.program` (= `MulLoopNatC.mNatSum`, restated here so the
karatsuba modules do not import the `nat.mul` loop chain) -/
theorem kmNatSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (b : Nat) (L : List (Nat × Nat)) (st k : BitVec 64) :
    Summary (LibMul.program.link impl) stkNatA
      (fun s => RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [st, k] ∧ StackNat.Pre R b L 4208 24 st.toNat k.toNat s)
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        StackNat.PostL R b L 4208 24 st.toNat k.toNat s s') := by
  have hS := StackNat.sumL impl hap R hgr hmc hwb b L st k LibMul.names
    (FvModexp.Arm64.Callees.sub_of_all (by decide))
  rw [← LibMul.eq_only, stkNat_entry] at hS
  exact hS

/-- the post-call stores of the prologue (`0x1bc09c … 0x1bc108`) -/
@[reducible] def kpcWs (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - 352, s.sp.toNat - 344), (s.sp.toNat - 336, s.sp.toNat - 232)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KM1` from `stk.nat`'s postcondition and the post-call stores** (memory `M'`) -/
theorem kmFin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 : Nat} {P S : State} (h : KPm R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P)
    (hreg : S.mem.regions = P.mem.regions) (hq : StackNat.PostL R b L 4208 24 st (kT n) P S)
    {M' : Memory} (hF2 : MemFrame S.mem M' (kpcWs s)) (hreg2 : M'.regions = S.mem.regions)
    (q96 : M'.readLE (s.sp.toNat - 352) 8 = zc - kh n) (q112 : M'.readLE (s.sp.toNat - 336) 8 = zp + 8 * kh n)
    (hz1 : IntAt M' (s.sp.toNat - 264) 0 (stW S.mem st + 8 * stLen s.mem st) (kT n) (kT n))
    (htx : IntAt M' (s.sp.toNat - 296) 0 zp (kh n) zc)
    (hty : IntAt M' (s.sp.toNat - 328) 0 (zp + 8 * kh n) (kh n) (zc - kh n))
    (S' : State) (hpos : KNAt s S' 0x1bc10c) (hm : S'.mem = M') :
    ∃ (Lk : List (Nat × Nat)) (bk : Nat),
      KM1 R b L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 (stW S.mem st + 8 * stLen s.mem st) S' Lk bk := by
  have F := h.pre.F
  have hW := F.hW; have hW' := kW_ge n
  have h40 := F.n40
  obtain ⟨-, ⟨hal, hWs, ha48, -⟩, -, hout, -, -, hLs, -⟩ := F.env
  obtain ⟨-, hsok, hstw, -, -, -, hfw, hsf, -, -, -, hfgA⟩ := F.stk
  obtain ⟨-, -, -, -, -, -, -, -, hgArt, -, -, -, -⟩ := F.gl
  clear F
  obtain ⟨-, -, -, Lk, bk, ⟨hext, hbud, hinv⟩, hok, hlen, hsame, hgrow, hF, hLF, hmem⟩ := hq
  have hspP : P.sp.toNat = s.sp.toNat - 448 := h.spN
  have hsth : Held R L st 24 := hsok.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw hLs
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw hsf hfgA
  have eW : stW P.mem st = stW s.mem st := h.rd (by omega)
  have eL : stLen P.mem st = stLen s.mem st := h.rd (by omega)
  have eC : stCap P.mem st = stCap s.mem st := h.rd (by omega)
  rw [eL, eC] at hsame hgrow hmem
  rw [eL] at hlen hbud
  rw [eW] at hsame
  -- the post-call stores keep the stack header
  have hpo : Outside st 24 (kpcWs s) := by simp only [kpcWs, outside_cons, outside_nil, and_true]; omega
  obtain ⟨hok', e0, e1, e2⟩ := stkOK_frame hok hF2 hpo (LiveExt.refl R Lk)
  have hkT : 0 < kT n := by simp only [kT]; omega
  have hscr := Scr.of_post (m0 := s.mem) (k := kT n) hok hlen hkT hsame hgrow rfl
  have hacc : ∀ a k w, S.mem.accessible a k w = s.mem.accessible a k w := fun a k w => by
    rw [hF.accessible, h.fr.accessible]
  have hscr' : Scr R L Lk s.mem s.mem st (stW S.mem st + 8 * stLen s.mem st) (kT n) :=
    ⟨hscr.b48, by rw [← hacc]; exact hscr.acc, hscr.al, hscr.held, hscr.loc⟩
  have htsep : StkSep M' st (stW S.mem st + 8 * stLen s.mem st) (8 * kT n) := by
    have h3 : StkSep S.mem st (stW S.mem st + 8 * stLen s.mem st) (8 * kT n) :=
      ⟨(hscr'.apart hsth fun _ => hsf).symm, by
        simp only [BasicSqr.freeP, BasicSqr.freeN]; rw [hlen]; unfold Apart
        simp only [StackNat.rnd, kT]; omega,
      hscr'.apart (Or.inr hgArt) fun _ => hfgA.symm⟩
    unfold StkSep BasicSqr.freeP BasicSqr.freeN at h3 ⊢; rw [e0, e1, e2]; exact h3
  have hfr1 : MemFrame s.mem S.mem (R.rt ++ winA s W 72 ++ kws s st zp n) :=
    h.fr.trans hF fun a k ho => by
      simp only [winA, kws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      rw [hspP, eW, eL, eC]
      obtain ⟨⟨hrt, hw1, hw2⟩, hz, hs1, hs2⟩ := ho
      exact ⟨⟨by omega, by omega⟩, ⟨hrt, by omega, by omega⟩, hs1, hs2⟩
  have hlS : stLen M' st = stLen s.mem st + StackNat.rnd (kT n) := e1.trans hlen
  -- reads of the frame after the call and the stores
  have hrd2 : ∀ a k, s.sp.toNat - 456 ≤ a → a + k ≤ s.sp.toNat + 72 →
      (a + k ≤ s.sp.toNat - 440 ∨ s.sp.toNat - 424 ≤ a) → Outside a k (kpcWs s) →
      M'.readLE a k = P.mem.readLE a k := by
    intro a k h1 h2 h3 h4
    refine (hF2.readLE _ _ h4).trans (hF.readLE _ _ ?_)
    simp only [winA, stkWs, outside_append, outside_cons, outside_nil, and_true]
    rw [hspP, eW, eL, eC]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega, by omega⟩, by omega, by omega⟩
  have hws : stkWs P.mem st = stkWs s.mem st := by simp only [stkWs]; rw [eW, eL, eC]
  have ko : ∀ a k, a + k ≤ s.sp.toNat - 352 ∨ s.sp.toNat - 232 ≤ a ∨
      (s.sp.toNat - 344 ≤ a ∧ a + k ≤ s.sp.toNat - 336) → Outside a k (kpcWs s) := fun a k ha => by
    simp only [kpcWs, outside_cons, outside_nil, and_true]; omega
  subst hm
  refine ⟨Lk, bk, hpos, ?km, hz1, htx, hty,
    IntAt.keep h.z0h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (by omega) (ko _ _ (by omega)),
    IntAt.keep h.z2h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (by omega) (ko _ _ (by omega))⟩
  exact
    { pre := h.pre, l0 := h.l0, v0 := h.v0, nn0 := h.nn0, l1 := h.l1, v1 := h.v1, nn1 := h.nn1,
      m0 := h.m0, w0 := h.w0, mn0 := h.mn0, m1 := h.m1, w1 := h.w1, mn1 := h.mn1,
      scr := hscr',
      tsep := htsep,
      ext := hext, bud := by unfold kc1; exact hbud,
      inv := by
        rw [h.g] at hinv
        refine RtInv.inv_frame' hF2 (fun r hr => ?_) hinv
        simp only [kpcWs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> left <;> exact hout.of_sub (by omega) (by omega),
      reg := hreg2.trans (hreg.trans h.reg),
      fr := hfr1.trans hF2 fun a k ho => ⟨ho, by
        simp only [winA, kws, kpcWs, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        obtain ⟨⟨hrt, hw1, hw2⟩, -⟩ := ho
        exact ⟨by omega, by omega⟩⟩,
      lf := LiveFrame.trans
        (LiveFrame.trans
          ⟨fun a k hin _ => h.fr.readLE a k (by
            have := NatSqr.outside_of_liveSep hin hLs
            simp only [outside_cons, outside_nil, and_true] at this ⊢; omega)⟩
          (FvModexp.LiveFrame.mono_ws (hws ▸ hLF) fun a k ho => by
            simp only [kws, outside_cons] at ho; exact ho.2) fun _ _ h => h)
        ⟨fun a k hin _ => hF2.readLE a k (by
          have := NatSqr.outside_of_liveSep hin hLs
          simp only [kpcWs, outside_cons, outside_nil, and_true] at this ⊢; omega)⟩ fun _ _ h => h,
      sok := hok', slen := hlS,
      sarr := by
        rw [e0, e2]
        by_cases hc : stLen s.mem st + StackNat.rnd (kT n) ≤ stCap s.mem st
        · exact Or.inl (hsame hc)
        · exact Or.inr (hgrow (by omega)),
      smem := by
        have := ArrIn.of_nat hok.2.2.2.2.2.1 hlen hsame hmem
        unfold ArrIn at this ⊢; rw [e0, e2]; exact this,
      lr := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.lr,
      fp := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.fp,
      bit := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.bit,
      q88 := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.q88,
      q96 := q96,
      q104 := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.q104,
      q112 := q112,
      dfn := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.dfn,
      dst := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.dst,
      dln := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.dln,
      dpt := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.dpt,
      s1 := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.s1,
      s2 := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.s2,
      s3 := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.s3,
      s4 := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.s4,
      s5 := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.s5,
      s6 := (hrd2 _ _ (by omega) (by omega) (by omega) (ko _ _ (by omega))).trans h.s6,
      x0h := IntAt.keep h.x0h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (by omega) (ko _ _ (by omega)),
      x1h := IntAt.keep h.x1h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (by omega) (ko _ _ (by omega)),
      y0h := IntAt.keep h.y0h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (by omega) (ko _ _ (by omega)),
      y1h := IntAt.keep h.y1h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (by omega) (ko _ _ (by omega)) }

end FvModexp.Arm64.NatMul
