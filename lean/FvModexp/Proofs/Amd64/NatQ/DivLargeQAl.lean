import FvModexp.Proofs.Amd64.NatQ.DivLargeQRel
import FvModexp.Proofs.Amd64.NatQ.DivLargeMkA

set_option autoImplicit false

/-! (Q-form copy of Amd64/Nat/DivLargeQAl.lean, TIGHT COSTS, top s38)
# `divLarge` (amd64): `q = z.make(m + 1)` allocating — shared pure facts (`Mem.wordK`: the `Word` descriptor is
unchanged; `atJ_alloc`: `AtJ` after `makeslice`), used by `DivLargeQAm` (`m ≠ 0`) and `DivLargeQA1` (`m = 0`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Amd64.NatAdd (outside_of_inRanges)
open FvModexp.Amd64.DivBasic (LiveFrame.trans')

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivLarge
open FvModexp.Amd64.DivLarge
variable {H : Nat}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- the type descriptor `Word` (read-only data) is unchanged after `stk.nat` (pure) -/
theorem Mem.wordK {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t : Nat} {L1 : List (Nat × Nat)} {b1 w1 c1 : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {Lk : List (Nat × Nat)} {bk : Nat}
    {wS cS : Nat} {M : Janus.Arm64.Memory}
    (hM : Mem R L zp zc st up uc ip il vp vl s t wS cS Lk bk M) :
    Outside wordT 16 R.rt ∧ Apart wordT 16 ((s.regs 4).toNat - 41272) (41272 + 112) ∧
      ∀ a n, wordT ≤ a → a + n ≤ wordT + 16 → M.readLE a n = s.mem.readLE a n := by
  have hpre := hE.pre
  have hd : Extracted.program.DataLoaded s.mem := hpre.ce.2.2.2.1
  have hro : RoOut R := hpre.ce.2.2.2.2.2.2.2.2.1
  obtain ⟨-, ⟨hb', ha, hw⟩, -, -⟩ := hpre.ce
  simp only [regSP] at hb' ha hw
  have hty : Outside wordT 16 R.rt := hro.out' 1 (by decide) (by decide)
  have hwt : Apart wordT 16 ((s.regs 4).toNat - 41272) (41272 + 112) := apart_of_data hd 1 (by decide) (by decide) hw
  have hWw : Outside wordT 16 (stkWs s.mem st) := by
    have hstacc := hpre.sti.1.2.2.1
    refine outside_stkWs hpre (apart_of_data hd 1 (by decide) (by decide) hstacc) fun hc => ?_
    exact apart_of_data hd 1 (by decide) (by decide) (hpre.sti.1.2.2.2.2.1 hc).2.2.1
  have hWs : Outside wordT 16 (wsL zp zc up uc vl t) := by
    have h1 : Apart wordT 16 t (8 * vl) := apart_of_data hd 1 (by decide) (by decide) hE.scr.acc
    unfold Apart at h1
    refine outside_wsL (by omega) (fun h => ?_) (fun h => ?_)
    · have : Apart wordT 16 zp (8 * zc) := apart_of_data hd 1 (by decide) (by decide) ((hpre.zo.2.1 h).2.2.1)
      unfold Apart at this; omega
    · have : Apart wordT 16 up (8 * uc) := apart_of_data hd 1 (by decide) (by decide) ((hpre.uo.2.1 h).2.2.1)
      unfold Apart at this; omega
  refine ⟨hty, hwt, fun a n h1 h2 => hM.fr.readLE a n ?_⟩
  unfold Apart at hwt
  simp only [outside_append]
  refine ⟨⟨⟨hty.of_sub h1 (by omega), ?_⟩, hWs.of_sub h1 (by omega)⟩, hWw.of_sub h1 (by omega)⟩
  simp only [win, outside_cons, outside_nil, and_true]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the state at `joinQ` after `q = makeslice(…)` (pure): the spills (`M1`: `RSP - 144`, `- 192`, the pushed return
address), `makeslice`'s frame, the fresh block `[ptr, ptr + rnd)` → `AtJ` -/
theorem atJ_alloc {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {c : Nat} {zp zc st up uc ip il vp vl : Nat}
    {s : State} {t w1 c1 : Nat} {L1 : List (Nat × Nat)} {b1 : Nat} {Lk : List (Nat × Nat)} {bk P C sh : Nat}
    (hE : Env R b H L c zp zc st up uc ip il vp vl s t L1 b1 w1 c1) {S : State}
    (hS : AtAl R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 Lk bk P C sh S) (hz : zc < il - vl + 1)
    (hb : makeCost (il - vl + 1) ≤ bk) {qc rnd ptr : Nat} (hsz : 8 * qc ≤ rnd) (hq : il - vl + 1 ≤ qc)
    (hq40 : qc < 2 ^ 40) (hrb : rnd ≤ makeCost (il - vl + 1)) {M1 m : Janus.Arm64.Memory}
    (hW : MemFrame S.mem M1 [((s.regs 4).toNat - 312, (s.regs 4).toNat - 304),
      ((s.regs 4).toNat - 192, (s.regs 4).toNat - 184), ((s.regs 4).toNat - 144, (s.regs 4).toNat - 136)])
    (hMF : MemFrame M1 m (R.rt ++ [((s.regs 4).toNat - 312 - 4096, (s.regs 4).toNat - 312),
      ((s.regs 4).toNat - 312 + 8, (s.regs 4).toNat - 312 + 8 + 24)]))
    (hLF : LiveFrame M1 m Lk []) (hAp : ApartAll ptr rnd Lk) (hIn : InRanges ptr rnd R.rt)
    (hle : ptr + rnd ≤ 2 ^ 48) (hacc : S.mem.accessible ptr rnd true = true) (h8 : ptr % 8 = 0)
    (hinv' : R.inv (bk - rnd) (Lk ++ [(ptr, ptr + rnd)]) (s.regs 14).toNat (view R.rt (Lk ++ [(ptr, ptr + rnd)]) m))
    (hrg : m.regions = S.mem.regions) (T : State) (hpc : T.rip = BitVec.ofNat 64 joinQ)
    (hsp : T.regs 4 = s.regs 4 - 304#64) (h5 : T.regs 5 = s.regs 4 - 8#64) (h14 : T.regs 14 = s.regs 14)
    (hfs : T.fsBase = s.fsBase) (hx : T.xmm 15 = 0#128) (hdf : T.df = false)
    (h0 : T.regs 0 = BitVec.ofNat 64 t) (h1 : T.regs 1 = BitVec.ofNat 64 vl) (h2 : T.regs 2 = BitVec.ofNat 64 sh)
    (h6 : T.regs 6 = BitVec.ofNat 64 C) (h7 : T.regs 7 = BitVec.ofNat 64 (il + 1))
    (h8r : T.regs 8 = BitVec.ofNat 64 P) (h9 : T.regs 9 = BitVec.ofNat 64 (il - vl + 1))
    (h11 : T.regs 11 = BitVec.ofNat 64 vl) (h12 : T.regs 12 = BitVec.ofNat 64 vl)
    (h13 : T.regs 13 = BitVec.ofNat 64 qc) (h15 : T.regs 15 = BitVec.ofNat 64 ptr) (hm : T.mem = m) :
    AtJ R b L zp zc st up uc ip il vp vl s t w1 c1 L1 b1 (Lk ++ [(ptr, ptr + rnd)]) (bk - rnd) P C sh ptr qc T := by
  have hl := hE.lay
  have hsp0 := hl.sp0; have hsp1 := hl.sp1; have hv2 := hl.v2
  have hU := hS.ua
  have hMU := hS.mem
  have hout : Outside ((s.regs 4).toNat - 41272) (41272 + 112) R.rt := hE.pre.ce.2.2.2.2.1
  have hf : MemFrame S.mem m (R.rt ++ scrB s ++ wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) := by
    refine (mfTrans hW hMF).mono fun a n ho => ?_
    have ho' := ho
    simp only [outside_append, outside_cons, outside_nil, and_true] at ho'
    obtain ⟨⟨⟨hrt, hsc⟩, -⟩, -⟩ := ho'
    simp only [outside_append, outside_cons, outside_nil, and_true]
    repeat' apply And.intro
    all_goals first | exact hrt | omega
  have keep : ∀ a n, Held R Lk a n → (a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a) →
      m.readLE a n = S.mem.readLE a n := by
    intro a n hh hw0
    have e1 : M1.readLE a n = S.mem.readLE a n := hW.readLE a n (by
      simp only [outside_cons, outside_nil, and_true]; omega)
    rcases hh with hi | ho
    · rw [hLF.readLE a n hi trivial, e1]
    · rw [hMF.readLE a n (by
        simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨ho, by omega, by omega⟩), e1]
  have hlf : LiveFrame S.mem m L (wsL zp zc up uc vl t ++ [(P, P + 8 * C)]) :=
    ⟨fun a n hin _ => by
      have hw0 : a + n ≤ (s.regs 4).toNat - 41272 ∨ (s.regs 4).toNat + 112 ≤ a := by
        obtain ⟨r, hr, i1, i2⟩ := hin; have := hl.lsep r (hE.ext.mem_old hr); omega
      exact keep a n (Or.inl (hS.ext2.inRanges_old (hE.ext.inRanges_old hin))) hw0⟩
  have hacc2 : ∀ a n w, m.accessible a n w = S.mem.accessible a n w := fun a n w => by
    rw [hMF.accessible, hW.accessible]
  have hx1 : LiveExt R Lk (Lk ++ [(ptr, ptr + rnd)]) := LiveExt.single (by simpa using hIn) (by simpa using hAp)
  have hc1 := hE.c1len
  have hw1h : Held R Lk w1 (8 * c1) := hS.ext2.held (hE.w1live (by simp only [StackNat.rnd] at hc1; omega)).2.1
  have hth : Held R Lk t (8 * vl) := hS.ext2.held hl.theld
  have htv : natVal m t vl = natVal S.mem t vl := keep _ _ hth hl.tw
  have hpv : natVal m P (il + 1) = natVal S.mem P (il + 1) :=
    keep _ _ (hU.pheld.sub (by omega) (by have := hU.cap; omega)) (by have := hU.pw; have := hU.cap; omega)
  have htt : m.readLE (t + 8 * (vl - 1)) 8 = S.mem.readLE (t + 8 * (vl - 1)) 8 :=
    keep _ _ (hth.sub (by omega) (by omega)) (by have := hl.tw; omega)
  have hb2 := hS.bud2
  subst hm
  exact ⟨hpc, hsp, h5, h14, hfs, hx, hdf, h0, h1, h2, h6, h7, h8r, h9, h11, h12, h13, h15,
    MemU.frame hE hMU hU hf hlf hinv', UArr.live (UArr.frame hU hacc2) hx1,
    (qarr_alloc hE hU hS.ext2 hz hAp hIn hle hacc h8 hsz hq hq40 hw1h).frame hacc2,
    LiveExt.trans hS.ext2 hx1, by omega, hS.sh63, by rw [htv]; exact hS.vval, by rw [htt]; exact hS.vtop,
    by rw [hpv]; exact hS.uval, by rw [hrg]; exact hS.reg⟩

end FvModexp.Amd64.Q.DivLarge
