import FvModexp.Proofs.Arm64.Exp.P2DT
import FvModexp.Proofs.Arm64.Exp.P2DEnt
import FvModexp.Proofs.Arm64.Exp.P2DStmt
import FvModexp.Proofs.Arm64.Exp.P2DTz
import FvModexp.Proofs.Arm64.Nat.RshDefs
import FvModexp.Proofs.Arm64.Nat.LshDefs

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (arm64): the even-base recursive path — shared facts (agent infra)

Frame base `sp = SP - 112`; the path's own slots (`W1`): `sp + 96` (`lo = tz·y[0]`), `sp + 120 … 200`; `rsh`/`lsh` run
with window `[sp - (stk - 112), sp + 88)` (`CEnv` from the entry `CPre`: `cenv_of`), the recursive call with
`[sp - (stk - 112), sp + 96)` (`cpre_sub`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2D

open FvModexp.Arm64.ExpHyp

theorem tN {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- a normalised nat whose value is below `2^(64 n)` has at most `n` limbs (adapted from infra's `W2Pro.norm_len_le`) -/
theorem lenLe {m : Memory} {p l n : Nat} (hN : NatNorm m p l) (hv : natVal m p l < 2 ^ (64 * n)) : l ≤ n := by
  refine Nat.not_lt.1 fun hc => ?_
  rcases hN with h | h
  · omega
  · have e := m.readLE_add p (8 * (l - 1)) 8
    rw [show 8 * (l - 1) + 8 = 8 * l by omega] at e
    have h1 : 1 ≤ m.readLE (p + 8 * (l - 1)) 8 := Nat.pos_of_ne_zero h
    have h2 : (256 : Nat) ^ (8 * (l - 1)) = 2 ^ (64 * (l - 1)) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega
    have h3 : 2 ^ (64 * n) ≤ 2 ^ (64 * (l - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have h4 := Nat.mul_le_mul_left (256 ^ (8 * (l - 1))) h1
    simp only [natVal] at hv
    omega

/-- a fresh object is apart from every held range -/
theorem apF {R : RtInv} {L : List (Nat × Nat)} {p k a n : Nat} (hin : InRanges p k R.rt) (hap : ApartAll p k L)
    (hh : Held R L a n) : Apart p k a n := by
  rcases hh with h | h
  · exact hap.apart_of_inRanges h
  · exact (hin.apart h).symm

theorem apart_sub {a n b k a' n' : Nat} (h : Apart a n b k) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) : Apart a' n' b k := by
  unfold Apart at h ⊢; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
  {need cst : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the caller environment one frame down** (window `[SP - stk, SP - 24)` at `sp = SP - 112`) -/
theorem cenv_of (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {M : Memory}
    (hF : MemFrame s.mem M (R.rt ++ ownW s stk A)) (hrg : M.regions = s.mem.regions)
    {L1 : List (Nat × Nat)} (hx : LiveExt R L L1) (hk : 112 ≤ stk) :
    CallW.CEnv R L1 (s.regs 28).toNat (s.sp.toNat - 112) (stk - 112) 88 M := by
  obtain ⟨⟨⟨g1, g2, g3⟩, ⟨hal, hle, h48, hacc⟩, hd, hwrt, hgw, hgrt, hLs, hro'⟩, -, -, hro, -⟩ := hP
  generalize hSP : s.sp.toNat = SP at *
  have hout : Outside (SP - stk) (stk + A) R.rt := hwrt
  have hgow : Outside ((s.regs 28).toNat + 16) 8 (ownW s stk A) := by
    simp only [ownW, outside_cons, outside_nil, and_true, hSP]; unfold Apart at hgw; omega
  have hgM : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hF.readLE _ _ (by rw [outside_append]; exact ⟨hgrt, hgow⟩)
  refine ⟨by omega, by omega, by omega, by
      rw [hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega),
    g1, by rw [hF.accessible]; exact g2, by rw [hgM]; omega, hout.of_sub (by omega) (by omega),
    by unfold Apart at hgw ⊢; omega, hgrt, ?_,
    dataLoaded_frame hd hrg hro hF (fun r hr _ => by
      simp only [ownW, hSP, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> exact Memory.accessible_mono _ hacc (by omega) (by omega)), hro'⟩
  refine hx.liveSep (fun r hr => ?_) fun r hr => ?_
  · have := hLs r hr
    simp only [win, hSP, outside_cons, outside_nil, and_true] at this ⊢; omega
  · simp only [List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- `cenv_of` with extra written ranges `ws` (accessible at entry, apart from the guard word) -/
theorem cenv_ofW (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {M : Memory} {ws : List (Nat × Nat)}
    (hF : MemFrame s.mem M (R.rt ++ ws)) (hws : ∀ r ∈ ws, r.1 < r.2 → s.mem.accessible r.1 (r.2 - r.1) true = true)
    (hgws : ∀ r ∈ ws, r.2 ≤ r.1 ∨ (s.regs 28).toNat + 16 + 8 ≤ r.1 ∨ r.2 ≤ (s.regs 28).toNat + 16)
    (hrg : M.regions = s.mem.regions)
    {L1 : List (Nat × Nat)} (hx : LiveExt R L L1) (hk : 112 ≤ stk) :
    CallW.CEnv R L1 (s.regs 28).toNat (s.sp.toNat - 112) (stk - 112) 88 M := by
  obtain ⟨⟨⟨g1, g2, g3⟩, ⟨hal, hle, h48, hacc⟩, hd, hwrt, hgw, hgrt, hLs, hro'⟩, -, -, hro, -⟩ := hP
  generalize hSP : s.sp.toNat = SP at *
  have hout : Outside (SP - stk) (stk + A) R.rt := hwrt
  have hgM : M.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    rd_frame hF fun r hr => by
      rcases List.mem_append.1 hr with h | h
      · have := MemFrame.outside_mem hgrt h; omega
      · exact hgws r h
  refine ⟨by omega, by omega, by omega, by
      rw [hF.accessible]; exact Memory.accessible_mono _ hacc (by omega) (by omega),
    g1, by rw [hF.accessible]; exact g2, by rw [hgM]; omega, hout.of_sub (by omega) (by omega),
    by unfold Apart at hgw ⊢; omega, hgrt, ?_, dataLoaded_frame hd hrg hro hF hws, hro'⟩
  refine hx.liveSep (fun r hr => ?_) fun r hr => ?_
  · have := hLs r hr
    simp only [win, hSP, outside_cons, outside_nil, and_true] at this ⊢; omega
  · simp only [List.mem_singleton] at hr; subst hr; simp only
    exact hout.of_sub (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `natOne` one frame down after runtime calls (`R.rt` in the frame; `natOne`'s array held) -/
theorem natOne_subR (hP : NHyp.CPre R b L stk A zp zl zc st ins need cst s) {op : Nat}
    (hone : EvenHyp.NatOne R L s.mem op (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st))
    (hsa : EvenHyp.StkApart s.mem st op 8) {S : State}
    (hF : MemFrame s.mem S.mem (R.rt ++ ownW s stk A)) (hLF : LiveFrame s.mem S.mem L [])
    {L1 : List (Nat × Nat)} (hx : LiveExt R L L1)
    (hSsp : S.sp.toNat + 112 = s.sp.toNat) {stk' A' : Nat} (hk : stk' + 112 ≤ stk) (hA : A' ≤ 104)
    (ew : stW S.mem st = stW s.mem st) (el : stLen S.mem st = stLen s.mem st) (ec : stCap S.mem st = stCap s.mem st) :
    EvenHyp.NatOne R L1 S.mem op (win S stk' A' ++ [(zp, zp + 8 * zc)] ++ stWs S.mem st) ∧
      EvenHyp.StkApart S.mem st op 8 := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := hone
  have es : stWs S.mem st = stWs s.mem st := by unfold stWs stkWs; rw [ew, el, ec]
  have hwo : ∀ {a k : Nat}, Outside a k (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) →
      Outside a k (ownW s stk A) := fun h => by
    simp only [win, ownW, outside_append, outside_cons, outside_nil, and_true] at h ⊢; omega
  have hww : ∀ {a k : Nat}, Outside a k (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) →
      Outside a k (win S stk' A' ++ [(zp, zp + 8 * zc)] ++ stWs S.mem st) := fun h => by
    rw [es]; simp only [win, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨⟨by omega, h.1.2⟩, h.2⟩
  have rd : ∀ k, k + 8 ≤ 24 → S.mem.readLE (EvenHyp.natOneA + k) 8 = s.mem.readLE (EvenHyp.natOneA + k) 8 :=
    fun k hk => hF.readLE _ _ (by
      rw [outside_append]; exact ⟨n6.of_sub (by omega) (by omega), (hwo n7).of_sub (by omega) (by omega)⟩)
  refine ⟨⟨?_, ?_, ?_, by rw [n10.readLE hF (LiveFrame.of_nil' hLF _) (hwo n11)]; exact n4,
    by rw [hF.accessible]; exact n5, n6, hww n7, by rw [hF.accessible]; exact n8, n9, hx.held n10, hww n11⟩, ?_⟩
  · have := rd 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact n1
  · rw [rd 8 (by omega)]; exact n2
  · rw [rd 16 (by omega)]; exact n3
  · intro h; obtain ⟨a1, a2⟩ := hsa h
    refine ⟨a1, fun hl => ?_⟩
    rw [el, ec] at hl; rw [ew, el, ec]; exact a2 hl

end

end FvModexp.Arm64.P2D
