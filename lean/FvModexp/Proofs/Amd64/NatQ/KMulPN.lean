import FvModexp.Proofs.Amd64.NatQ.KMulB
import FvModexp.Proofs.Amd64.NatQ.KSqrProD
import FvModexp.Proofs.Common.StkFrame

/-!
# [amd64 port (divmc s52) of the Q-form Arm64/NatQ/KMulPN.lean — TIGHT COSTS] `karatsuba` (amd64): the `z1 := stk.nat(2·n2 + 1)` call (natmul.go:203-204) and the headers after it (pure)

`KPm … P`: the state at `(*stack).nat`'s entry (`CALL` at `0x5f2096`, return `0x5f209b` pushed at `RSP - 456`): `KPre` at
the entry `s`, the normalised halves of `x` and `y`, the prologue's frame stores (saved `RBP`, spills `RSP+32 … RSP+64`,
the `2·n2`/`8·n2`/`n2` slots at `RSP - 360`, `RSP - 352`, `RSP - 344`, defer record and bit, the `x0 x1 y0 y1 z0 z2` headers, the push);
only our frame `[RSP-456, RSP)` and the spill area `[RSP+32, RSP+72)` written. `kmNatPre`: the call's precondition;
`kmNatSum`: the callee summary in `LibMul`; `kmFin`: `KM1` at `0x5f2149` from the callee's postcondition and the
post-call stores (`z1`/`tx`/`ty` headers, `RSP-360 := zc - n2`, `RSP-336 := zp + 8·n2`).
(Adapted from this repo's amd64 `KSqrProD` and arm64 `KMulPN`.)
-/

set_option autoImplicit false

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.NatMul

variable {H : Nat}

open FvModexp.Amd64.Q.NatSqr (StkPre StkSep IntAt stkNatA stkNat_entry)

structure KPm (R : RtInv) (b H : Nat) (L : List (Nat × Nat)) (W st zp zc xp n xc yp yc : Nat) (s : State)
    (lx0 lx1 ly0 ly1 : Nat) (P : State) : Prop where
  pre : KPre R b H L W st zp (2 * n) zc xp n xc yp n yc s
  pc : P.rip = BitVec.ofNat 64 stkNatA
  sp : (P.regs 4).toNat = (s.regs 4).toNat - 456
  g : P.regs 14 = s.regs 14
  fpr : P.regs 5 = s.regs 4 - 8#64
  fs : P.fsBase = s.fsBase
  df : P.df = s.df
  x15 : P.xmm 15 = s.xmm 15
  r0 : P.regs 0 = BitVec.ofNat 64 st
  r1 : P.regs 3 = BitVec.ofNat 64 (kT n)
  ra : P.mem.readLE ((s.regs 4).toNat - 456) 8 = 0x5f209b
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
  fr : MemFrame s.mem P.mem [((s.regs 4).toNat - 456, (s.regs 4).toNat), ((s.regs 4).toNat + 32, (s.regs 4).toNat + 72)]
  reg : P.mem.regions = s.mem.regions
  fp : P.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  bit : P.mem.readLE ((s.regs 4).toNat - 369) 1 = 1
  q88 : P.mem.readLE ((s.regs 4).toNat - 360) 8 = 2 * kh n
  q96 : P.mem.readLE ((s.regs 4).toNat - 352) 8 = 8 * kh n
  q104 : P.mem.readLE ((s.regs 4).toNat - 344) 8 = kh n
  dfn : P.mem.readLE ((s.regs 4).toNat - 232) 8 = kDfn
  dst : P.mem.readLE ((s.regs 4).toNat - 224) 8 = st
  dln : P.mem.readLE ((s.regs 4).toNat - 216) 8 = stLen s.mem st
  dpt : P.mem.readLE ((s.regs 4).toNat - 16) 8 = (s.regs 4).toNat - 232
  s1 : P.mem.readLE ((s.regs 4).toNat + 32) 8 = st
  s2 : P.mem.readLE ((s.regs 4).toNat + 40) 8 = zp
  s3 : P.mem.readLE ((s.regs 4).toNat + 48) 8 = 2 * n
  s4 : P.mem.readLE ((s.regs 4).toNat + 56) 8 = zc
  s5 : P.mem.readLE ((s.regs 4).toNat + 64) 8 = xp
  x0h : IntAt P.mem ((s.regs 4).toNat - 48) 0 xp lx0 xc
  x1h : IntAt P.mem ((s.regs 4).toNat - 80) 0 (xp + 8 * kh n) lx1 (xc - kh n)
  y0h : IntAt P.mem ((s.regs 4).toNat - 112) 0 yp ly0 yc
  y1h : IntAt P.mem ((s.regs 4).toNat - 144) 0 (yp + 8 * kh n) ly1 (yc - kh n)
  z0h : Z0H s P.mem zp zc n
  z2h : Z2H s P.mem zp zc n

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
  {lx0 lx1 ly0 ly1 : Nat} {P : State}

/-- the window facts of the entry (from `KPre`) -/
theorem KPm.lay (h : KPm R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P) :
    5424 ≤ W ∧ W ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat + 72 ≤ 2 ^ 48 ∧ 40 ≤ n ∧
      n ≤ 2 ^ 12 ∧ 2 * n ≤ zc ∧ zc < 2 ^ 40 ∧
      Outside ((s.regs 4).toNat - W) (W + 72) R.rt ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
      Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - W) (W + 72) := by
  have F := h.pre.F
  obtain ⟨-, ⟨hb, ha, -⟩, hal, -, hout, hga, hgr, -, -, -⟩ := F.env
  have := kW64_ge n
  exact ⟨by have := F.hW; omega, hb, hal, ha, F.n40, F.n12, F.zc2, F.zc40, hout, hgr, hga⟩

/-- reads outside the prologue's writes are unchanged since the entry -/
theorem KPm.rd (h : KPm R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P) {a k : Nat}
    (ha : a + k ≤ (s.regs 4).toNat - 456 ∨ (s.regs 4).toNat + 72 ≤ a ∨
      ((s.regs 4).toNat ≤ a ∧ a + k ≤ (s.regs 4).toNat + 32)) :
    P.mem.readLE a k = s.mem.readLE a k :=
  h.fr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)

end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`stk.nat(2·n2 + 1)`'s precondition** at its entry `P` -/
theorem kmNatPre {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 : Nat} {P : State} (h : KPm R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P) :
    StackNatX.PreQ R b L H 4192 24 st (kT n) P := by
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have F := h.pre.F
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, ⟨-, -, hw⟩, -, hdl, -, -, -, hLs, hro, ⟨htb, htr, htg⟩, htrt, htw⟩ := F.env
  have hsv := F.sv
  have hglb := F.gl
  have hsp := F.stk
  have hslen := F.slb
  have hlenH := F.lvH
  have hcost := F.cost
  have hinv := F.inv
  clear F
  obtain ⟨hst0, hsok, hstw, hstg, hsta, hfg, hfw, hsf, hswb, -, -, -, -, -, -⟩ := hsp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hwbacc, -, -⟩ := hglb
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hw
  have hspP := h.sp
  have hacc : ∀ a k w, P.mem.accessible a k w = s.mem.accessible a k w := fun a k w => h.fr.accessible a k w
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw
  simp only [NatSqr.guard, BasicSqr.freeP, BasicSqr.freeN] at hstg hfg hfw hsf hsta
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
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, hdlP, ?_, ?_, by rw [h.g]; exact hgr, ?_, hro, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [stackguard0Offset, regG]; rw [h.g]; exact hg1
    · simp only [stackguard0Offset, regG]; rw [h.g, hacc]; exact hg2
    · simp only [stackguard0, stackguard0Offset, regG, regSP]; rw [h.g, eG, hspP]; omega
    · simp only [stackguard0Offset, regG, regSP] at hg4 hga ⊢; unfold Apart at hga; rw [h.g, hspP]; omega
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
    by simp only [kT, kh]; omega, by simp only [kT, kh]; omega,
    ⟨by simp only [kT, kh]; omega, by rw [stkR_congr (m := s.mem) (m' := P.mem) (by simp only [stCap]; exact eC)]; omega⟩, ?_, by rw [hacc]; exact hwbacc, hswb, hsf⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hnl h0; exact ⟨a1, a2, by rw [hacc]; exact a3, a4⟩
  · refine RtInv.inv_frame' h.fr (fun r hr => ?_) hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> left <;> exact hout.of_sub (by simp only; omega) (by simp only; omega)

/-- `(*stack).nat` (`StackNatX.sumQ`) as a summary in `LibMul.program` -/
theorem kmNatSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hgr : GrowsliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.growslice") 4096 R)
    (hmc : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (hwb : WbLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.gcWriteBarrier2") 4096 R 2)
    (H b : Nat) (L : List (Nat × Nat)) (st k : BitVec 64) :
    Summary (LibMul.program.link impl) stkNatA
      (fun s => RetAddr ((Extracted.program.onlySegments StackNat.names).link impl) (s.mem.readLE (s.regs regSP).toNat 8) ∧
        s.xmm xmmZero = 0 ∧ ArgsFrom64 s 0 [st, k] ∧ s.df = false ∧ StackNatX.PreQ R b L H 4192 24 st.toNat k.toNat s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        StackNatX.PostQ R b L H 4192 24 st.toNat k.toNat s s') := by
  have hS := StackNatX.sumQ impl hap R hgr hmc hwb H b L st k LibMul.names (IntAS.sub_of_all (by decide))
  rw [← LibMul.eq_only, stkNat_entry] at hS
  exact hS

/-- the post-call stores of the prologue (`0x5f209b … 0x5f2149`) -/
@[reducible] def kpcWs (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 360, (s.regs 4).toNat - 352), ((s.regs 4).toNat - 336, (s.regs 4).toNat - 232)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **`KM1` from `stk.nat`'s postcondition and the post-call stores** (memory `M'`) -/
theorem kmFin {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {W st zp zc xp n xc yp yc : Nat} {s : State}
    {lx0 lx1 ly0 ly1 : Nat} {P S : State} (h : KPm R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 P)
    (hreg : S.mem.regions = P.mem.regions) (hq : StackNatX.PostQ R b L H 4192 24 st (kT n) P S)
    {M' : Memory} (hF2 : MemFrame S.mem M' (kpcWs s)) (hreg2 : M'.regions = S.mem.regions)
    (q88 : M'.readLE ((s.regs 4).toNat - 360) 8 = zc - kh n)
    (q112 : M'.readLE ((s.regs 4).toNat - 336) 8 = zp + 8 * kh n)
    (hz1 : IntAt M' ((s.regs 4).toNat - 264) 0 (stW S.mem st + 8 * stLen s.mem st) (kT n) (kT n))
    (htx : IntAt M' ((s.regs 4).toNat - 296) 0 zp (kh n) zc)
    (hty : IntAt M' ((s.regs 4).toNat - 328) 0 (zp + 8 * kh n) (kh n) (zc - kh n))
    (S' : State) (hpos : KNAt s S' 0x5f2149) (hm : S'.mem = M') :
    ∃ (Lk : List (Nat × Nat)) (bk : Nat),
      KM1 R b H L W st zp zc xp n xc yp yc s lx0 lx1 ly0 ly1 (stW S.mem st + 8 * stLen s.mem st) S' Lk bk := by
  obtain ⟨hW, hWs, hal, ha48, h40, hn12, hzl, hzc40, hout, hgr, hga⟩ := h.lay
  have F := h.pre.F
  obtain ⟨-, -, -, -, -, -, -, hLs, -⟩ := F.env
  obtain ⟨-, hsok, hstw, -, -, -, hfw, hsf, -, -, -, hfgA, -, -, -⟩ := F.stk
  obtain ⟨-, -, -, -, -, -, -, -, hgArt, -, -, -, -⟩ := F.gl
  clear F
  obtain ⟨-, -, -, -, -, Lk, bk, ⟨hext, hbud, hinv⟩, hok, hlen, hsame, hgrow, hF, hLF, hmem⟩ := hq
  have hspP := h.sp
  have hsth : Held R L st 24 := hsok.2.1
  simp only [win, outside_cons, outside_nil, and_true] at hstw hfw
  simp only [BasicSqr.freeP, BasicSqr.freeN] at hfw hsf hfgA
  have eW : stW P.mem st = stW s.mem st := h.rd (by omega)
  have eL : stLen P.mem st = stLen s.mem st := h.rd (by omega)
  have eC : stCap P.mem st = stCap s.mem st := h.rd (by omega)
  rw [eL, eC] at hsame hgrow hmem
  rw [eL] at hlen; rw [stkR_congr eC] at hbud
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
  have hfr1 : MemFrame s.mem S.mem (R.rt ++ win s W 72 ++ kws s st zp n) :=
    h.fr.trans hF fun a k ho => by
      simp only [win, kws, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      rw [hspP, eW, eL, eC]
      obtain ⟨⟨hrt, hw1⟩, hz, hs1, hs2⟩ := ho
      exact ⟨⟨by omega, by omega⟩, ⟨hrt, by omega⟩, hs1, hs2⟩
  have hlS : stLen M' st = stLen s.mem st + StackNat.rnd (kT n) := e1.trans hlen
  -- reads of the frame after the call (the callee's window ends at `RSP - 432`) and the stores
  have hrd2 : ∀ a k, (s.regs 4).toNat - 432 ≤ a → a + k ≤ (s.regs 4).toNat + 72 → Outside a k (kpcWs s) →
      M'.readLE a k = P.mem.readLE a k := by
    intro a k h1 h2 h4
    refine (hF2.readLE _ _ h4).trans (hF.readLE _ _ ?_)
    simp only [win, stkWs, outside_append, outside_cons, outside_nil, and_true]
    rw [hspP, eW, eL, eC]
    exact ⟨⟨hout.of_sub (by omega) (by omega), by omega⟩, by omega, by omega⟩
  have hws : stkWs P.mem st = stkWs s.mem st := by simp only [stkWs]; rw [eW, eL, eC]
  have ko : ∀ a k, a + k ≤ (s.regs 4).toNat - 360 ∨ (s.regs 4).toNat - 232 ≤ a ∨
      ((s.regs 4).toNat - 352 ≤ a ∧ a + k ≤ (s.regs 4).toNat - 336) → Outside a k (kpcWs s) := fun a k ha => by
    simp only [kpcWs, outside_cons, outside_nil, and_true]; omega
  subst hm
  refine ⟨Lk, bk, hpos, ?km, hz1, htx, hty,
    IntAt.keep h.z0h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (ko _ _ (by omega)),
    IntAt.keep h.z2h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (ko _ _ (by omega))⟩
  exact
    { pre := h.pre, l0 := h.l0, v0 := h.v0, nn0 := h.nn0, l1 := h.l1, v1 := h.v1, nn1 := h.nn1,
      m0 := h.m0, w0 := h.w0, mn0 := h.mn0, m1 := h.m1, w1 := h.w1, mn1 := h.mn1,
      scr := hscr',
      tsep := htsep,
      ext := hext, bud := by unfold kc1; rw [Nat.zero_add, stkR_congr e2]; exact hbud,
      spk := by unfold kc1; exact Nat.zero_le _,
      inv := by
        rw [h.g] at hinv
        refine RtInv.inv_frame' hF2 (fun r hr => ?_) hinv
        simp only [kpcWs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> left <;> exact hout.of_sub (by omega) (by omega),
      reg := hreg2.trans (hreg.trans h.reg),
      fr := hfr1.trans hF2 fun a k ho => ⟨ho, by
        simp only [win, kws, kpcWs, stkWs, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
        obtain ⟨⟨hrt, hw1⟩, -⟩ := ho
        exact ⟨by omega, by omega⟩⟩,
      lf := LiveFrame.trans
        (LiveFrame.trans
          ⟨fun a k hin _ => h.fr.readLE a k (by
            have := NatSqr.outside_of_liveSep hin hLs
            simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega)⟩
          (FvModexp.LiveFrame.mono_ws (hws ▸ hLF) fun a k ho => by
            simp only [kws, outside_cons] at ho; exact ho.2) fun _ _ h => h)
        ⟨fun a k hin _ => hF2.readLE a k (by
          have := NatSqr.outside_of_liveSep hin hLs
          simp only [win, kpcWs, outside_cons, outside_nil, and_true] at this ⊢; omega)⟩ fun _ _ h => h,
      sok := hok', slen := hlS,
      sarr := by
        rw [e0, e2]
        by_cases hc : stLen s.mem st + StackNat.rnd (kT n) ≤ stCap s.mem st
        · exact Or.inl (hsame hc)
        · exact Or.inr (hgrow (by omega)),
      smem := by
        have := ArrIn.of_nat hok.2.2.2.2.2.1 hlen hsame hmem
        unfold ArrIn at this ⊢; rw [e0, e2]; exact this,
      lr := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans (h.rd (by omega)),
      fp := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.fp,
      bit := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.bit,
      q88 := q88,
      q104 := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.q104,
      q112 := q112,
      dfn := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.dfn,
      dst := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.dst,
      dln := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.dln,
      dpt := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.dpt,
      s1 := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.s1,
      s2 := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.s2,
      s3 := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.s3,
      s4 := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.s4,
      s5 := (hrd2 _ _ (by omega) (by omega) (ko _ _ (by omega))).trans h.s5,
      x0h := IntAt.keep h.x0h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (ko _ _ (by omega)),
      x1h := IntAt.keep h.x1h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (ko _ _ (by omega)),
      y0h := IntAt.keep h.y0h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (ko _ _ (by omega)),
      y1h := IntAt.keep h.y1h fun x m h1 h2 => hrd2 x m (by omega) (by omega) (ko _ _ (by omega)) }

end FvModexp.Amd64.Q.NatMul
