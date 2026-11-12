import FvModexp.Proofs.Arm64.Exp.P2PreWbC
import FvModexp.Proofs.Common.DivmcLsl
import FvModexp.Proofs.Common.BitArith

/-!
# `buildPrecomputationWindowModPower2` (arm64): the fill loop (nat.go:875-877) (agent infra)

`for i := range powers { powers[i] = buf[i*w : (i+1)*w : (i+2)*w] }` after `buf = stk.nat((len+1)·w)`.
`FillJ i`: the loop head `0x1b5468` with `i ≤ len` and `powers[j]` for `j < i` filled (`PwT`). `fillP`: from the
pointer store `0x1b5460` (both write-barrier branches join there) to `FillJ (i+1)`. `fillB`: `FillJ (i+1) → FillJ i`
for `i < len`. `fill_all`: `FillJ len → FillJ 0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.P2Pre

open FvModexp.Arm64.EvenHyp

theorem shl_ofNat (n k : Nat) (h : n * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by
      have : n ≤ n * 2 ^ k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
      omega)]

theorem mask_ofNat (a c : Nat) (ha : a < 2 ^ 64) (hc : 0 < c) (hc2 : c < 2 ^ 63) :
    BitVec.ofNat 64 a &&& (0#64 - BitVec.ofNat 64 c).sshiftRight 63 = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitArith.asr63_toNat, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : (2 ^ 64 - c % 2 ^ 64 + (0#64 : BitVec 64).toNat) % 2 ^ 64 = 2 ^ 64 - c := by
    rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]; simp only [BitVec.toNat_zero, Nat.add_zero]; omega
  rw [h1, if_neg (by omega), Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

/-- the fill loop's head -/
abbrev pcF : Nat := 1791080

def FillJ (impl : List Segment) (R : RtInv) (kc : Nat) (sqC : Nat → Nat → Nat) (mlC : Nat → Nat → Nat → Nat)
    (b : Nat) (L : List (Nat × Nat)) (st pw pl lm x xl : Nat) (s : State) (i : Nat) : Prop :=
  ∀ (S : State) (bp : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    S.pc = BitVec.ofNat 64 pcF → S.sp = BitVec.ofNat 64 (s.sp.toNat - 208) → S.regs 28 = s.regs 28 →
    S.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216) → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 bp → S.regs 1 = BitVec.ofNat 64 i → S.regs 2 = BitVec.ofNat 64 (NB pl lm) →
    S.regs 3 = BitVec.ofNat 64 pw → S.regs 4 = BitVec.ofNat 64 (W lm) → S.regs 5 = BitVec.ofNat 64 pl →
    Ctx R kc L st pw pl lm s bp S.mem L1 b1 → (∀ j, j < i → PwT S.mem pw bp lm j) → i ≤ pl →
    b - stackNatCost (stLen s.mem st) (NB pl lm) ≤ b1 →
    Goal impl R kc sqC mlC b L st pw pl lm x xl s S

section
variable {impl : List Segment} {R : RtInv} {kc : Nat} {sqC : Nat → Nat → Nat} {mlC : Nat → Nat → Nat → Nat}
    {b : Nat} {L : List (Nat × Nat)} {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fillP (hkc : 4608 ≤ kc) (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {i : Nat}
    (k : FillJ impl R kc sqC mlC b L st pw pl lm x xl s (i + 1)) (hi : i < pl) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat}
    (S : State) (hpc : S.pc = BitVec.ofNat 64 1791072) (hsp : S.sp = BitVec.ofNat 64 (s.sp.toNat - 208))
    (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = BitVec.ofNat 64 (s.sp.toNat - 216))
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h2 : S.regs 2 = BitVec.ofNat 64 (NB pl lm))
    (h3 : S.regs 3 = BitVec.ofNat 64 pw) (h4 : S.regs 4 = BitVec.ofNat 64 (W lm)) (h5 : S.regs 5 = BitVec.ofNat 64 pl)
    (h7 : S.regs 7 = BitVec.ofNat 64 (i + 1)) (h8 : S.regs 8 = BitVec.ofNat 64 (24 * i))
    (h9 : S.regs 9 = BitVec.ofNat 64 (bp + 8 * (i * W lm)))
    (hc : Ctx R kc L st pw pl lm s bp M L1 b1) (hd : ∀ j, j < i → PwT M pw bp lm j)
    (hh1 : M.readLE (pw + 24 * i + 8) 8 = W lm) (hh2 : M.readLE (pw + 24 * i + 16) 8 = 2 * W lm)
    (hb : b - stackNatCost (stLen s.mem st) (NB pl lm) ≤ b1) :
    ReachesRet (LibW.program.link impl) (s.regs 30) S (GoalQ R kc sqC mlC b L st pw pl lm x xl s) := by
  have hsl := s.sp.isLt
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hpw48 := hf.pw48
  have hpwa : M.accessible pw (24 * pl) true = true := by rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hpww
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hin : bp + 8 * (i * W lm) + 8 ≤ 2 ^ 48 := by
    have := pw_in (pl := pl) (lm := lm) (bp := bp) (j := i) (by omega); omega
  have hpe : pw + 24 * i + 24 ≤ pw + 24 * pl := by omega
  subst hm
  janus_run until [pcF]
  have hc' := ctx_own hc hf (bp + 8 * (i * W lm)) (a := pw + 24 * i) (k := 8) ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
  have hdt : ∀ j, j < i + 1 → PwT (S.mem.writeLE (pw + 24 * i) 8 (bp + 8 * (i * W lm))) pw bp lm j := by
    intro j hj
    rcases Nat.lt_or_ge j i with hj' | hj'
    · obtain ⟨e0, e1, e2⟩ := hd j hj'
      exact ⟨by rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact e0,
        by rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact e1,
        by rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact e2⟩
    · have hji : j = i := by omega
      subst hji
      refine ⟨?_, ?_, ?_⟩
      · rw [Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
      · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hh1
      · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hh2
  refine k _ bp L1 b1 rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hc' hdt (by omega) hb
  all_goals janus_simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fillB (hwb : WbLiveContract (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) {i : Nat}
    (k : FillJ impl R kc sqC mlC b L st pw pl lm x xl s (i + 1)) (hi : i < pl) :
    FillJ impl R kc sqC mlC b L st pw pl lm x xl s i := by
  intro S bp L1 b1 hpc hsp h28 h29 h18 h0 h1 h2 h3 h4 h5 hc hd hip hb
  have hsl := s.sp.isLt
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hpw48 := hf.pw48
  have hpwa : S.mem.accessible pw (24 * pl) true = true := by rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hpww := hf.pww
  simp only [K, A, win, outside_cons, outside_nil, and_true] at hpww
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hgl := globals_ctx hpre hc (S' := S) (by rw [hsp, BitVec.toNat_ofNat]; omega) (stk := 4096) (above := 8)
    (by omega) (by omega)
  have hwbf : S.mem.accessible RunIface.wbA 4 false = true := hgl.2.2.2.2.2.2.2.2.2.2.1
  have hwbv : RunIface.wbA = 7616064 := rfl
  rw [hwbv] at hwbf
  have ha1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm
  have ha2 : BitVec.ofNat 64 i + 2#64 = BitVec.ofNat 64 (i + 2) := (BitVec.ofNat_add i 2).symm
  have mo : ∀ a c : Nat, BitVec.ofNat 64 a * BitVec.ofNat 64 c = BitVec.ofNat 64 (a * c) := fun a c => by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]
  have m8 := mo (i + 2) (W lm)
  have m9 := mo i (W lm)
  have m10 := mo (i + 1) (W lm)
  have hl3 := lsl3_ofNat i (by omega)
  have hl24 : BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (8 * i * 2) = BitVec.ofNat 64 (24 * i) := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  have c1 : (i + 2) * W lm ≤ NB pl lm := Nat.mul_le_mul_right _ (by omega)
  have c2 : (i + 1) * W lm ≤ (i + 2) * W lm := Nat.mul_le_mul_right _ (by omega)
  have c3 : i * W lm ≤ (i + 1) * W lm := Nat.mul_le_mul_right _ (by omega)
  have hmask := mask_ofNat (i * W lm) (W lm * 2) (by omega) (by omega) (by omega)
  have hp9 : BitVec.ofNat 64 bp + BitVec.ofNat 64 (i * W lm * 8) = BitVec.ofNat 64 (bp + 8 * (i * W lm)) := by
    have : i * W lm ≤ 17 * 128 := by
      have := Nat.mul_le_mul (show i ≤ 17 by omega) hw128; omega
    rw [← BitVec.ofNat_add]; congr 1; omega
  have hpe : pw + 24 * i + 24 ≤ pw + 24 * pl := by omega
  have hc2 := ctx_own (ctx_own hc hf (W lm) (a := 24 * i + (pw + 8)) (k := 8)
    ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩) hf (W lm + W lm) (a := 24 * i + (pw + 8 + 8)) (k := 8)
    ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
  have hrd2 : ∀ a n, (a + n ≤ pw + 24 * i + 8 ∨ pw + 24 * i + 24 ≤ a) →
      ((S.mem.writeLE (24 * i + (pw + 8)) 8 (W lm)).writeLE (24 * i + (pw + 8 + 8)) 8 (W lm + W lm)).readLE a n =
        S.mem.readLE a n := fun a n h => by
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hd2 : ∀ j, j < i → PwT ((S.mem.writeLE (24 * i + (pw + 8)) 8 (W lm)).writeLE (24 * i + (pw + 8 + 8)) 8
      (W lm + W lm)) pw bp lm j := fun j hj => by
    obtain ⟨e0, e1, e2⟩ := hd j hj
    exact ⟨(hrd2 _ _ (by omega)).trans e0, (hrd2 _ _ (by omega)).trans e1, (hrd2 _ _ (by omega)).trans e2⟩
  have hh1 : ((S.mem.writeLE (24 * i + (pw + 8)) 8 (W lm)).writeLE (24 * i + (pw + 8 + 8)) 8 (W lm + W lm)).readLE
      (pw + 24 * i + 8) 8 = W lm := by
    rw [show pw + 24 * i + 8 = 24 * i + (pw + 8) by omega, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
  have hh2 : ((S.mem.writeLE (24 * i + (pw + 8)) 8 (W lm)).writeLE (24 * i + (pw + 8 + 8)) 8 (W lm + W lm)).readLE
      (pw + 24 * i + 16) 8 = 2 * W lm := by
    rw [show pw + 24 * i + 16 = 24 * i + (pw + 8 + 8) by omega, Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold Goal
  janus_run [hwbf, ha1, ha2, m8, m9, m10, hl3, hl24, hmask, hp9] until [wbE, 1791072]
  · -- the barrier is off
    refine fillP hkc hpre k hi _ rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hc2 hd2 hh1 hh2 hb
    all_goals janus_simp
  · -- the barrier is on
    refine wbCall hwb hpre hkc hc2 rfl rfl (by janus_simp) rfl (ra := 1791184) (by janus_simp) (by decide) (by decide)
      fun buf junk f v m' ex ep hb48 hbal hbacc hctx hrd => ?_
    have hb8a : m'.accessible buf.toNat 8 true = true := Memory.accessible_mono _ hbacc (Nat.le_refl _) (by omega)
    have hb8b : m'.accessible (buf.toNat + 8) 8 true = true := Memory.accessible_mono _ hbacc (by omega) (by omega)
    have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
    janus_run [hb8a, hb8b, hbuf64] until [1791072]
    have hr := hrd (bp + 8 * (i * W lm)) (S.mem.readLE (pw + 24 * i) 8)
    have hdW : ∀ j, j < i → PwT (W2 m' buf.toNat (bp + 8 * (i * W lm)) (S.mem.readLE (pw + 24 * i) 8)) pw bp lm j :=
      fun j hj => by
        obtain ⟨e0, e1, e2⟩ := hd2 j hj
        exact ⟨(hr _ 8 (by omega) (Or.inl ⟨by omega, by omega⟩)).trans e0,
          (hr _ 8 (by omega) (Or.inl ⟨by omega, by omega⟩)).trans e1,
          (hr _ 8 (by omega) (Or.inl ⟨by omega, by omega⟩)).trans e2⟩
    refine fillP hkc hpre k hi _ rfl rfl ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hctx _ _) hdW
      ((hr _ 8 (by omega) (Or.inl ⟨by omega, by omega⟩)).trans hh1)
      ((hr _ 8 (by omega) (Or.inl ⟨by omega, by omega⟩)).trans hh2) hb
    all_goals janus_simp
theorem fill_all (hwb : WbLiveContract (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqC mlC b L st pw pl ws lm x xl s) (kE : FillJ impl R kc sqC mlC b L st pw pl lm x xl s pl) :
    ∀ n i, i + n = pl → FillJ impl R kc sqC mlC b L st pw pl lm x xl s i := by
  intro n
  induction n with
  | zero => intro i h; rw [show i = pl by omega]; exact kE
  | succ n ih => intro i h; exact fillB hwb hkc hpre (ih (i + 1) (by omega)) (by omega)

end

end FvModexp.Arm64.P2Pre
