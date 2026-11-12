import FvModexp.Proofs.Arm64.Exp.P2DT
import FvModexp.Proofs.Arm64.Exp.P2DOneR
import FvModexp.Proofs.Arm64.Nat.StackNatCall

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): `makeslice(Word, 1, 1)` from the frame `SP - 112` (agent infra)

`mkCallD`: at the contract entry `T` (memory = the entry memory changed in the own frame), the live contract's
pre from the entry `NHyp.CPre` (`call_pre` with the entry window), and its post as the facts `MkR` of the fresh
one-word object (`[p, p + r)`, `r = blockSize 8`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

/-- the facts after the allocation (memory `T.mem → m`) -/
structure MkR (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (T : State) (m : Memory) (p r : Nat) : Prop where
  mf : MemFrame T.mem m (R.rt ++ calleeStack T 4096 3)
  lf : LiveFrame T.mem m L []
  rin : InRanges p r R.rt
  rap : ApartAll p r L
  b48 : p + r ≤ 2 ^ 48
  acc : m.accessible p r true = true
  al : p % 8 = 0
  sz : 8 ≤ r
  rc : r ≤ allocCost 8
  cs : ApartAll p r (calleeStack T 4096 3)
  inv : R.inv (b - r) (L ++ [(p, p + r)]) (T.regs 28).toNat (view R.rt (L ++ [(p, p + r)]) m)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **`makeslice(Word, 1, 1)`** (continuation form) -/
theorem mkCallD {impl : List Segment} (hmk : MakesliceLiveContract (LibW.program.link impl) mkE 4096 R)
    (ret0 : BitVec 64) (Q : State → Prop)
    (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) (hk : 4208 + 112 ≤ stk) (hA8 : 8 ≤ A)
    (hcb : allocCost 8 ≤ b)
    (T : State) (hpc : T.pc = BitVec.ofNat 64 mkE) (hsp : T.sp.toNat + 112 = s.sp.toNat)
    (h28 : T.regs 28 = s.regs 28) (hF : MemFrame s.mem T.mem (ownW s stk A))
    (hrg : T.mem.regions = s.mem.regions)
    (h0 : T.regs 0 = 2641088#64) (h1 : T.regs 1 = 1#64) (h2 : T.regs 2 = 1#64)
    (h30 : T.regs 30 = BitVec.ofNat 64 mkRa)
    (KC : ∀ (ptr : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory)
      (ex : Option (Nat × Nat)) (ep : Nat → Bool),
      MkR R L b T m ptr.toNat (blockSize 8 true) → m.regions = T.mem.regions →
      ReachesRet (LibW.program.link impl) ret0 (retStateX T junk [ptr] f v m ex ep) Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  obtain ⟨⟨⟨g1, g2, g3⟩, ⟨hal, hle, h48, hacc⟩, hd, hwrt, hgw, hgrt, hLs, -⟩, hsv, -, hro, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, hinv⟩ := hP
  generalize hSP : s.sp.toNat = SP at *
  have hown : ∀ r ∈ ownW s stk A, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr _
    simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hacc (by omega) (by omega)
  have hF' : MemFrame s.mem T.mem (R.rt ++ ownW s stk A) := hF.mono fun a k ho => by
    rw [outside_append] at ho; exact ho.2
  have hdT : Extracted.program.DataLoaded T.mem := dataLoaded_frame hd hrg hro hF' hown
  obtain ⟨ht1, ht2, ht3⟩ := StackNat.wT_facts hdT
  have hwTv : StackNat.wT = 2641088 := rfl
  rw [hwTv] at ht1 ht2 ht3
  have t0 : (T.regs 0).toNat = 2641088 := by rw [h0]; rfl
  have t1 : (T.regs 1).toNat = 1 := by rw [h1]; rfl
  have t2 : (T.regs 2).toNat = 1 := by rw [h2]; rfl
  have e30 : (T.regs 30).toNat = mkRa := by rw [h30]; rfl
  have hround : makesliceRound T = blockSize 8 true := by
    simp only [makesliceRound, typSize, typNoscan, typPtrBytes, t0, t2, ht1, ht2]; rfl
  have hwin : Outside (SP - stk) (stk + A) R.rt := hwrt
  have hinvT : R.inv b L (T.regs 28).toNat (view R.rt L T.mem) := by
    rw [h28]
    refine RtInv.inv_frame hF (fun r hr => ?_) hinv
    simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact hwin.of_sub (by omega) (by omega)
  have hc := call_pre R L b (makesliceRound T) mkE [(T.regs 0).toNat, (T.regs 1).toNat, (T.regs 2).toNat]
    (s := s) (S := T) (lo := SP - stk) (hi := SP + A) (stack := 4096) (nargs := 3) (fr := 112)
    g1 g2 (by rw [hSP]; omega) (by simp only [outside_cons]; exact ⟨by unfold Apart at hgw; omega, hgrt⟩)
    (hF.mono fun a k ho => by
      simp only [ownW, hSP, outside_append, outside_cons, outside_nil, and_true] at ho ⊢; omega)
    h28 (by rw [hSP]; exact hsp) (by omega) (by rw [e30]; decide) (by rw [e30]; decide) (by decide) (by omega)
    (by omega) (by omega) (by omega) (by rw [show SP + A - (SP - stk) = stk + A by omega]; exact hacc)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp only
      rw [show SP + A - (SP - stk) = stk + A by omega]; exact hwin) (by simpa only [win, hSP] using hLs)
    (by rw [← mkE_eq, t0, t1, t2]; exact hsv.1 _ _ _ (by decide)) hinvT (by rw [hround]; exact Nat.le_trans (blockSize_le_allocCost 8 true) hcb)
  refine ReachesRet.call_regions (hmk L b) hpc ⟨⟨hc.1, ⟨by omega, by rw [t0]; exact ht3⟩, by omega, by omega, ?_⟩, hc.2⟩ ?_
  · simp only [typSize, t0, t2, ht1, maxAlloc]; omega
  intro S1 _ hpost hrg1
  have hsz : typSize T.mem (T.regs 0).toNat * (T.regs 2).toNat = 8 := by simp only [typSize, t0, t2, ht1]
  obtain ⟨ptr, junk, f, v, m, ex, ep, hs1, hMF, hLF, hQ, hcsA, hinv'⟩ := hpost
  rw [hsz] at hQ
  obtain ⟨hobj, hap⟩ := hQ (by omega)
  simp only [makesliceObj, Fresh, hsz] at hobj
  have hns : typNoscan T.mem (T.regs 0).toNat = true := by
    simp only [typNoscan, typPtrBytes, t0, ht2]; rfl
  rw [hround] at hap hinv' hcsA
  rw [hns] at hobj
  obtain ⟨hin, h48', hacc', hal', -, -, hle'⟩ := hobj
  subst hs1
  exact KC ptr junk f v m ex ep ⟨hMF, hLF, hin, hap, h48', hacc', hal' (Or.inr (by decide)), hle',
    blockSize_le_allocCost _ _, hcsA, hinv'⟩ hrg1

end

end FvModexp.Arm64.P2D
