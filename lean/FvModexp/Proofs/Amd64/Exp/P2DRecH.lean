import FvModexp.Proofs.Amd64.Exp.P2DRsh
import FvModexp.Proofs.Amd64.Exp.P2DWin

set_option autoImplicit false

/-!
# `nat.expNNPowerOfTwo` (amd64): helper facts of the recursive call (agent asm s70)

Frame `sp = SP - 0x70` (`SP` = entry `RSP`). The recursive callee runs at `RSP = SP - 0x78` with window
`[SP - stk, SP - 0x30)` (`stk' = stk - 0x78`, `A' = 72`); our slots `sp + 0x58` (`lo`), `sp + 0x68` (saved BP),
`sp + 0x70` (return address) lie above it. `lenLe`, `apF`, `apart_sub` adapted from fv-modexp arm64
`Arm64/Exp/P2DRDefs.lean` (agent infra); `natOne_subR` / `cpre_cst` are the amd64 twins of infra's.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2D

open FvModexp.Amd64.ExpHyp

/-- a normalised nat whose value is below `2^(64 n)` has at most `n` limbs (adapted from arm64 `P2D.lenLe`) -/
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

/-- a fresh object is apart from every held range (adapted from arm64 `P2D.apF`) -/
theorem apF {R : RtInv} {L : List (Nat × Nat)} {p k a n : Nat} (hin : InRanges p k R.rt) (hap : ApartAll p k L)
    (hh : Held R L a n) : Apart p k a n := by
  rcases hh with h | h
  · exact hap.apart_of_inRanges h
  · exact (hin.apart h).symm

theorem apart_sub {a n b k a' n' : Nat} (h : Apart a n b k) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) : Apart a' n' b k := by
  unfold Apart at h ⊢; omega

/-- (copied from fv-modexp `Amd64/Exp/SubMod2NSeg.natNorm_frame`, agent infra) -/
theorem nnFrame {m m' : Memory} {rs : List (Nat × Nat)} (h : MemFrame m m' rs) {p n : Nat}
    (ho : Outside p (8 * n) rs) (hn : NatNorm m p n) : NatNorm m' p n := by
  rcases Nat.eq_zero_or_pos n with h0 | hn0
  · exact Or.inl h0
  rcases hn with hn | hn
  · exact Or.inl hn
  · refine Or.inr ?_
    rw [h.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact hn

theorem bud_sub {b b1 m c : Nat} (h : b - m ≤ b1) : b - (m + c) ≤ b1 - c := by omega

/-- `CPre` with a smaller budget claim -/
theorem cpre_cst {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zl zc st : Nat} {ins : List (Nat × Nat)}
    {need cst c : Nat} {s : State} (h : NHyp.CPre R b L stk A zp zl zc st ins need cst s) (hc : c ≤ cst) :
    NHyp.CPre R b L stk A zp zl zc st ins need c s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, hcb,
    a23, a24, hinv⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21,
    Nat.le_trans hc hcb, a23, a24, hinv⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- the slots of `W1 (W0 …)` -/
theorem m1_rd {M : Memory} {sp bp zp zl zc st lm xp lo : Nat} (hsp1 : 8 ≤ sp)
    (hz : bp < 2 ^ 64 ∧ zp < 2 ^ 64 ∧ zl < 2 ^ 64 ∧ zc < 2 ^ 64 ∧ st < 2 ^ 64 ∧ lm < 2 ^ 64 ∧ lo < 2 ^ 64) :
    let M1 := W1 (W0 M sp bp zp xp) sp st lm zc zl zp lo
    M1.readLE (sp + 0x58) 8 = lo ∧ M1.readLE (sp + 0x60) 8 = zp ∧ M1.readLE (sp + 0x98) 8 = zl ∧
      M1.readLE (sp + 0xa0) 8 = zc ∧ M1.readLE (sp + 0xa8) 8 = st ∧ M1.readLE (sp + 0xc8) 8 = lm ∧
      M1.readLE (sp + 0x68) 8 = bp ∧ M1.readLE (sp + 0x70) 8 = M.readLE (sp + 0x70) 8 ∧
      M1.readLE (sp + 0x78) 8 = M.readLE (sp + 0x78) 8 ∧ M1.readLE (sp + 0x80) 8 = M.readLE (sp + 0x80) 8 ∧
      M1.readLE (sp + 0x88) 8 = M.readLE (sp + 0x88) 8 := by
  obtain ⟨z0, z1, z2, z3, z4, z5, z6⟩ := hz
  intro M1
  simp (disch := omega) only [M1, W1, W0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
    Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt z0, Nat.mod_eq_of_lt z1, Nat.mod_eq_of_lt z2,
    Nat.mod_eq_of_lt z3, Nat.mod_eq_of_lt z4, Nat.mod_eq_of_lt z5, Nat.mod_eq_of_lt z6]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- a slot above `rsh`'s window survives the `rsh` call -/
theorem rshSlot {R : RtInv} {M M' : Memory} {SP stk A stkR aboveR a : Nat}
    (hF : MemFrame M M' (R.rt ++ [(SP - 0x78 - stkR, SP - 0x78 + aboveR)] ++ [((0 : Nat), 0 + 8 * 0)]))
    (hwin : Outside (SP - stk) (stk + A) R.rt) (hkR : stkR + 0x78 ≤ stk) (haR : aboveR ≤ 0x60)
    (hle : stk ≤ SP) (h1 : SP - 0x18 ≤ a) (h2 : a + 8 ≤ SP + A) : M'.readLE a 8 = M.readLE a 8 :=
  hF.readLE _ _ (by
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨hwin.of_sub (by omega) (by omega), by omega⟩, by omega⟩)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- our slots above the recursive callee's window (`[SP - stk, SP - 0x30)`) survive its frame -/
theorem keepS {R : RtInv} {M2 M3 : Memory} {SP stk A zp zc st w l c a : Nat}
    (hFc : MemFrame M2 M3 (R.rt ++ [(SP - 0x78 - (stk - 0x78), SP - 0x78 + 72)] ++ [(zp, zp + 8 * zc)] ++
      [(st, st + 24), (w + 8 * l, w + 8 * c)]))
    (hk : 0x78 ≤ stk) (hle : stk ≤ SP) (hwin : Outside (SP - stk) (stk + A) R.rt)
    (hstw : Outside st 24 [(SP - stk, SP + A)]) (harr : 0 < c → Outside w (8 * c) [(SP - stk, SP + A)])
    (hcap0 : c = 0 → w = 0) (hlc : l ≤ c) (hzW : 0 < zc → Outside zp (8 * zc) [(SP - stk, SP + A)])
    (h1 : SP - 0x30 ≤ a) (h2 : a + 8 ≤ SP + A) : M3.readLE a 8 = M2.readLE a 8 := by
  simp only [outside_cons, outside_nil, and_true] at hstw harr hzW
  refine rd_frame hFc fun q hq => ?_
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with ((hq | rfl) | rfl) | (rfl | rfl)
  · have ho : Outside a 8 R.rt := hwin.of_sub (by omega) (by omega)
    have := MemFrame.outside_mem ho hq; omega
  · simp only; omega
  · simp only; rcases Nat.eq_zero_or_pos zc with h0 | h0
    · left; omega
    · have := hzW h0; right; omega
  · simp only; omega
  · simp only
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · have := hcap0 h0; left; rw [this, h0]; omega
    · have := harr h0; right; omega

section
variable {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {stk A zp zc st : Nat}
  {s S : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- `natOne` one frame down after runtime calls (`R.rt` in the frame; `natOne`'s array held) -/
theorem natOne_subR {op : Nat}
    (hone : EvenHyp.NatOne R L s.mem op (win s stk A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st))
    (hsa : NHyp.StkApart s.mem st op 8)
    (hF : MemFrame s.mem S.mem (R.rt ++ ownW s stk A)) (hLF : LiveFrame s.mem S.mem L [])
    {L1 : List (Nat × Nat)} (hx : LiveExt R L L1)
    (hSsp : (S.regs 4).toNat + 0x78 = (s.regs 4).toNat) {stk' A' : Nat} (hk : stk' + 0x78 ≤ stk) (hA : A' ≤ 0x78)
    (ew : stW S.mem st = stW s.mem st) (el : stLen S.mem st = stLen s.mem st) (ec : stCap S.mem st = stCap s.mem st) :
    EvenHyp.NatOne R L1 S.mem op (win S stk' A' ++ [(zp, zp + 8 * zc)] ++ stWs S.mem st) ∧
      NHyp.StkApart S.mem st op 8 := by
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

end FvModexp.Amd64.P2D

namespace FvModexp.Amd64.P2D

/-! numeric helpers (kept out of the big contexts: `omega` there splits every `∨` hypothesis) -/

theorem nR1 {SP : Nat} (h : 0x78 ≤ SP) : SP - 0x78 + 0 + 8 = SP - 0x70 ∧ SP - 0x78 + 0 + 16 = SP - 0x70 + 8 ∧
    SP - 0x78 + 0 + 24 = SP - 0x70 + 16 ∧ SP - 0x70 + 0x88 = SP + 0 + 24 ∧ SP - 0x78 = SP - 0x70 - 8 ∧
    SP - 0x70 + 0x70 = SP ∧ SP - 0x70 - 8 = SP - 0x78 := by omega

theorem nO {SP stk A o : Nat} (hk : 0x78 ≤ stk) (hle : stk ≤ SP) (hA : 96 ≤ A) (h1 : 0x58 ≤ o) (h2 : o + 8 ≤ 0x78) :
    SP - 0x30 ≤ SP - 0x70 + o ∧ SP - 0x70 + o + 8 ≤ SP + A ∧ SP - 0x70 + 0x18 ≤ SP - 0x70 + o := by omega

theorem nSv {SP stk A o : Nat} (hk : 0x78 ≤ stk) (hle : stk ≤ SP) (hA : 96 ≤ A) (h1 : 0x58 ≤ o) (h2 : o + 8 ≤ 0xd0) :
    SP - 0x18 ≤ SP - 0x70 + o ∧ SP - 0x70 + o + 8 ≤ SP + A := by omega

theorem nI {SP stk A : Nat} (hk : 0x78 ≤ stk) (hle : stk ≤ SP) (hA : 96 ≤ A) :
    SP - stk ≤ SP - 0x70 - 8 ∧ SP - 0x70 - 8 + (SP - 0x70 + 0x18 - (SP - 0x70 - 8)) ≤ SP - stk + (stk + A) := by
  omega

theorem nLm {lo lm lm' : Nat} (h1 : lo < lm) (h2 : lm' = lm - lo) (h3 : lm ≤ 2 ^ 13) : 1 ≤ lm' ∧ lm' ≤ 2 ^ 13 := by
  omega

theorem nCf {b b1 m c cst : Nat} (h1 : b - m ≤ b1) (h2 : m + c ≤ cst) (h3 : cst ≤ b) : c ≤ b1 := by omega

theorem nL {p l c : Nat} (h : l ≤ c) : p + 8 * l ≤ p + 8 * c := by omega

theorem pos_odd {v : Nat} (h : v % 2 = 1) : 0 < v := by omega

end FvModexp.Amd64.P2D
