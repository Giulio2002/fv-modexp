import FvModexp.Proofs.Amd64.Exp.P2DT
import FvModexp.Proofs.Amd64.Exp.P2DRun
import FvModexp.Proofs.Amd64.Nat.StackNatCall

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): `makeslice(Word, 1, 1)` one frame down (agent asm s67; amd64 twin of infra's arm64
`P2DMk`, call pattern of divmc's amd64 `P2W2Al.mkCall`)

`mkCallD`: at the contract entry `T` (`RSP_T = RSP - 0x78`, memory = the entry memory changed in the own frame), the
live contract's pre from the entry `NHyp.CPre` (its `CallEnv` through `cenv_ent` / `CEnv.frame` / `cenv_rebase`),
and its post as the facts `MkR` of the fresh one-word object (`[p, p + r)`, `r = blockSize 8`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

/-- the facts after the allocation (memory `T.mem → m`) -/
structure MkR (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (T : State) (m : Memory) (p r : Nat) : Prop where
  mf : MemFrame T.mem m (R.rt ++ calleeStack64 T 4096 3)
  lf : LiveFrame T.mem m L []
  rin : InRanges p r R.rt
  rap : ApartAll p r L
  b48 : p + r ≤ 2 ^ 48
  acc : m.accessible p r true = true
  al : p % 8 = 0
  sz : 8 ≤ r
  rc : r ≤ allocCost 8
  inv : R.inv (b - r) (L ++ [(p, p + r)]) (T.regs 14).toNat (view R.rt (L ++ [(p, p + r)]) m)

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **`makeslice(Word, 1, 1)`** (continuation form) -/
theorem mkCallD {impl : List Amd64.Segment} (hmk : MakesliceLiveContract64 (LibW.program.link impl) mkE 4096 R)
    {ret0 : W64} {Q : State → Prop}
    (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) (hk : 4320 ≤ stk) (hA8 : 8 ≤ A)
    (hcb : blockSize 8 true ≤ b)
    (T : State) (hpc : T.rip = BitVec.ofNat 64 mkE) (hsp : (T.regs 4).toNat + 0x78 = (s.regs 4).toNat)
    (h14 : T.regs 14 = s.regs 14) (hF : MemFrame s.mem T.mem (ownW s stk A))
    (hrg : T.mem.regions = s.mem.regions) (hra : T.mem.readLE (T.regs 4).toNat 8 < 2 ^ 47)
    (h0 : T.regs 0 = BitVec.ofNat 64 wordTy) (h3 : T.regs 3 = 1#64) (h1 : T.regs 1 = 1#64)
    (KC : ∀ (ptr : W64) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
      (zh : Nat → BitVec 256) (kr : Nat → W64),
      MkR R L b T m ptr.toNat (blockSize 8 true) →
      ReachesRet (LibW.program.link impl) ret0 (retState64 T junk [ptr] f x yh m zh kr) Q) :
    ReachesRet (LibW.program.link impl) ret0 T Q := by
  obtain ⟨hce, hsv, -, hro, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinv⟩ := hP
  have ce0 := cenv_ent hce
  obtain ⟨-, -, -, hacc0, -, -, -, c8w, hga, -, -, -, -, -, -, -, -, -, f6⟩ := id ce0
  generalize hSP : (s.regs 4).toNat = SP at *
  have hws : ∀ r ∈ ownW s stk A, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr _
    simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;>
      exact Janus.Arm64.Memory.accessible_mono _ hacc0 (by omega) (by omega)
  have hF' : MemFrame s.mem T.mem (R.rt ++ ownW s stk A) := hF.mono fun a k ho => by
    rw [outside_append] at ho; exact ho.2
  have ce1 := CallW.CEnv.frame ce0 hF' hrg hws
    (by unfold Apart at hga; simp only [ownW, hSP, outside_cons, outside_nil, and_true]; omega)
    (by unfold Apart at f6; simp only [ownW, hSP, outside_cons, outside_nil, and_true]; omega)
  have hce := cenv_rebase ce1 (x' := SP - 0x78) (K' := stk - 0x78) (A' := 0x78 + A) (by omega) (by omega)
    (by omega) (by obtain ⟨hal, -⟩ := ce0; omega)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, -, -, -, -, -, -, -⟩ := hce
  obtain ⟨ht1, ht2, ht3⟩ := StackNat.wT_facts c12
  rw [show StackNat.wT = 7233184 by decide] at ht1 ht2 ht3
  have t4 : (T.regs 4).toNat = SP - 0x78 := by omega
  have t14 : (T.regs 14).toNat = (s.regs 14).toNat := by rw [h14]
  have t0 : (T.regs 0).toNat = 7233184 := by rw [h0]; rfl
  have t3 : (T.regs 3).toNat = 1 := by rw [h3]; rfl
  have t1 : (T.regs 1).toNat = 1 := by rw [h1]; rfl
  have hsz : typSize T.mem (T.regs 0).toNat * (T.regs 1).toNat = 8 := by
    simp only [typSize, t0, t1, ht1]
  have hround : makesliceRound64 T = blockSize 8 true := by
    simp only [makesliceRound64, typSize, typNoscan, typPtrBytes, t0, t1, ht1, ht2]; rfl
  have hacc : T.mem.accessible (SP - 0x78 - 4096) (4096 + 8 + 8 * 3) true = true :=
    Janus.Arm64.Memory.accessible_mono _ c4 (by omega) (by omega)
  have hwT : Apart 7233184 16 (SP - 0x78 - 4096) (4096 + 8 + 8 * 3) :=
    apart_of_data c12 1 (by decide) (by decide) hacc
  have hok : R.ok mkE [7233184, 1, 1] := by rw [← mkE_eq]; exact hsv.1 _ _ _ (by decide)
  unfold Apart at hwT c9
  refine ReachesRet.call_regions (hmk.pos L b) hpc ⟨⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ ?_
  · exact hra
  · rw [t4]; omega
  · rw [t4]; omega
  · rw [t4]; omega
  · rw [t4]; exact hacc
  · rw [t0]; exact ⟨by decide, ht3⟩
  · rw [t3, t1]; exact Nat.le_refl _
  · rw [t1]; omega
  · rw [hsz]; simp only [maxAlloc]; omega
  · simp only [calleeStack64, t0, t4, outside_cons, outside_nil, and_true]; omega
  · simp only [GuardOK64, t14, t4]; exact ⟨c5, c6, by omega⟩
  · simp only [calleeStack64, t14, t4, outside_cons, outside_nil, and_true]; omega
  · rw [t0, t3, t1]; exact hok
  · rw [t14]
    refine Expmc.inv_frame hF (fun r hr => Or.inr ?_) hinv
    simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> exact c8w.of_sub (by omega) (by omega)
  · rw [hround]; omega
  · intro q hq
    have := c11 q hq
    simp only [liveWin64, calleeStack64, t4, List.cons_append, List.nil_append, outside_cons, outside_nil,
      and_true] at this ⊢
    omega
  · intro q hq
    simp only [liveWin64, calleeStack64, t4, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact c8.of_sub (by simp only; omega) (by simp only; omega)
  · rw [hsz]; omega
  intro S1 _ hpost hrg1
  obtain ⟨ptr, junk, f, x, yh, m, zh, kr, rfl, hMF, hLF, ⟨hobj, hap⟩, -, hinv'⟩ := hpost
  simp only [makesliceObj64, Fresh, hsz] at hobj
  have hns : typNoscan T.mem (T.regs 0).toNat = true := by
    simp only [typNoscan, typPtrBytes, t0, ht2]; rfl
  rw [hround] at hap hinv'
  rw [hns] at hobj
  obtain ⟨hin, h48, hacc', hal, -, -, hle⟩ := hobj
  exact KC ptr junk f x yh m zh kr ⟨hMF, hLF, hin, hap, h48, hacc', hal (Or.inr trivial), hle,
    blockSize_le_allocCost _ _, hinv'⟩

end

end FvModexp.Amd64.P2D
