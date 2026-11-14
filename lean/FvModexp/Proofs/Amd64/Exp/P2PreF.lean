import FvModexp.Proofs.Amd64.Exp.P2PreWbC
import FvModexp.Proofs.Common.BitArith

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): the fill loop (nat.go:875-877) (agent divmc s62; twin of infra's
`Arm64/Exp/P2PreF`)

`for i := range powers { powers[i] = buf[i*w : (i+1)*w : (i+2)*w] }` after `buf = stk.nat((len+1)·w)`.
`FillJ i` (P2PreJ): the loop head `+0xd4`. `fillP`: from the pointer store `+0xcd` (both write-barrier branches join
there) to `FillJ (i+1)`. `fillB`: `FillJ (i+1) → FillJ i` for `i < len` (the slice checks `+0x100 … +0x115` pass, the
`len`/`cap` stores `+0x11f`/`+0x128`, the masked pointer `+0x12d … +0x13b`, the barrier test `+0x13e`, barrier on:
old pointer `+0x147`, `gcWriteBarrier2` `+0x14e`, buffer stores `+0x153`/`+0x156`). `fill_all`: `FillJ len → FillJ 0`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp

/-- the pointer store of the fill loop -/
abbrev pcS : Nat := 0x5e8900 + 0xcd

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fillP (hkc : 4608 ≤ kc) (hpre : Pre R kc b L st pw pl ws lm x xl s) {i : Nat}
    (k : FillJ impl R kc b L st pw pl ws lm x xl s (i + 1)) (hi : i < pl) {bp : Nat} {M : Memory}
    {L1 : List (Nat × Nat)} {b1 : Nat}
    (S : State) (hpc : S.rip = BitVec.ofNat 64 pcS) (hfr : Frm s S 176) (hm : S.mem = M)
    (h0 : S.regs 0 = BitVec.ofNat 64 bp) (h1 : S.regs 1 = BitVec.ofNat 64 (NB pl lm))
    (h2 : S.regs 2 = BitVec.ofNat 64 pw) (h6 : S.regs 6 = BitVec.ofNat 64 (W lm)) (h3 : S.regs 3 = BitVec.ofNat 64 pl)
    (h13 : S.regs 13 = BitVec.ofNat 64 (i + 1)) (h10 : S.regs 10 = BitVec.ofNat 64 (3 * i))
    (h11 : S.regs 11 = BitVec.ofNat 64 (bp + 8 * (i * W lm)))
    (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1) (hd : ∀ j, j < i → PwT M pw bp lm j)
    (hh1 : M.readLE (pw + 24 * i + 8) 8 = W lm) (hh2 : M.readLE (pw + 24 * i + 16) 8 = 2 * W lm)
    (hb : b ≤ b1) :
    Goal impl R kc b L st pw pl lm x xl s S := by
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hpw48 := hf.pw48
  have hpwa : M.accessible pw (24 * pl) true = true := by
    rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hin : bp + 8 * (i * W lm) + 8 ≤ 2 ^ 48 := by
    have : (i + 2) * W lm ≤ (pl + 1) * W lm := Nat.mul_le_mul_right _ (by omega)
    simp only [NB] at hb48; rw [Nat.add_mul] at this; omega
  have hpe : pw + 24 * i + 24 ≤ pw + 24 * pl := by omega
  have ha : BitVec.ofNat 64 pw + BitVec.ofNat 64 (3 * i) * 8#64 = BitVec.ofNat 64 (pw + 24 * i) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have hacc : M.accessible (pw + 24 * i) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hpwa (by omega) (by omega)
  obtain ⟨hsp, h5, h14, hfs, hx15, hdf⟩ := hfr
  subst hm
  unfold Goal
  janus64_run [ha, hacc] until [pcF]
  have hc' := ctx_own hc hf (bp + 8 * (i * W lm)) (a := pw + 3 * i * 8) (k := 8)
    ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
  have hdt : ∀ j, j < i + 1 → PwT (S.mem.writeLE (pw + 3 * i * 8) 8 (bp + 8 * (i * W lm))) pw bp lm j := by
    intro j hj
    rcases Nat.lt_or_ge j i with hj' | hj'
    · obtain ⟨e0, e1, e2⟩ := hd j hj'
      exact ⟨by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact e0,
        by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact e1,
        by rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact e2⟩
    · have hji : j = i := by omega
      subst hji
      refine ⟨?_, ?_, ?_⟩
      · rw [show pw + 24 * j = pw + 3 * j * 8 by omega, Janus.Arm64.Memory.readLE_writeLE_self,
          Nat.mod_eq_of_lt (by omega)]
      · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hh1
      · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hh2
  refine k _ bp L1 b1 hpre rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ hc' hdt (by omega) hb
  all_goals first | exact hfs | exact hx15 | exact hdf | janus64_simp

theorem mask_ofNat (a c : Nat) (ha : a < 2 ^ 64) (hc : 0 < c) (hc2 : c < 2 ^ 63) :
    (0#64 - BitVec.ofNat 64 c).sshiftRight 63 &&& BitVec.ofNat 64 a = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitArith.asr63_toNat, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : (2 ^ 64 - c % 2 ^ 64 + 0 % 2 ^ 64) % 2 ^ 64 = 2 ^ 64 - c := by omega
  rw [h1, if_neg (by omega), Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (BitVec.isLt _)

/-- the fill loop's masked pointer `buf + 8 i w` (`+0x124 … +0x13b`) -/
theorem ptr_eq (bp w iw : Nat) (hw : 0 < w) (hw2 : w ≤ 128) (hiw : iw ≤ 2176) (hb : bp + 8 * iw < 2 ^ 64) :
    ((0#64 - (BitVec.ofNat 64 w + BitVec.ofNat 64 w)).sshiftRight 63 &&& BitVec.ofNat 64 iw <<< 3) +
      BitVec.ofNat 64 bp = BitVec.ofNat 64 (bp + 8 * iw) := by
  have e1 : BitVec.ofNat 64 w + BitVec.ofNat 64 w = BitVec.ofNat 64 (2 * w) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e2 : BitVec.ofNat 64 iw <<< 3 = BitVec.ofNat 64 (8 * iw) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]; omega
  rw [e1, e2, mask_ofNat _ _ (by omega) (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem three_eq (i : Nat) (hi : i ≤ 16) :
    BitVec.ofNat 64 i + BitVec.ofNat 64 i <<< 1 = BitVec.ofNat 64 (3 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]; omega

/-- the header stores `(w, 2 w)` of `powers[i]` are read back -/
theorem hdr_rd (M : Memory) (a1 a2 c w : Nat) (h1 : a1 = c + 8) (h2 : a2 = c + 16) (hw : 2 * w < 2 ^ 64) :
    ((M.writeLE a1 8 w).writeLE a2 8 (w + w)).readLE (c + 8) 8 = w ∧
      ((M.writeLE a1 8 w).writeLE a2 8 (w + w)).readLE (c + 16) 8 = 2 * w := by
  subst h1 h2
  constructor
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt (by omega)]; omega

theorem hdr_keep (M : Memory) (a1 a2 c v1 v2 a n : Nat) (h1 : a1 = c + 8) (h2 : a2 = c + 16)
    (h : a + n ≤ c + 8 ∨ c + 24 ≤ a) : ((M.writeLE a1 8 v1).writeLE a2 8 v2).readLE a n = M.readLE a n := by
  subst h1 h2
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

theorem push_rd (M : Memory) {c a n v : Nat} (h : a + n ≤ c ∨ c + 8 ≤ a) :
    (M.writeLE c 8 v).readLE a n = M.readLE a n :=
  Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)

theorem pw_push {pw pl a n r kc : Nat} (h : pw + 24 * pl ≤ r - 184 - kc ∨ r + 80 ≤ pw) (h1 : pw ≤ a)
    (h2 : a + n ≤ pw + 24 * pl) : a + n ≤ r - 184 ∨ r - 184 + 8 ≤ a := by omega

theorem three8 (pw i : Nat) : pw + 3 * i * 8 + 8 = pw + 24 * i + 8 := by omega
theorem three16 (pw i : Nat) : pw + 3 * i * 8 + 16 = pw + 24 * i + 16 := by omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem fillB (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    {i : Nat} (k : FillJ impl R kc b L st pw pl ws lm x xl s (i + 1)) (hi : i < pl) :
    FillJ impl R kc b L st pw pl ws lm x xl s i := by
  intro S bp L1 b1 hpre hpc hfr h0 h1 h2 h6 h3 h7 hc hd hip hb
  have hf := pf_of hpre (by omega)
  obtain ⟨hw1, hw128⟩ := w_facts hpre
  obtain ⟨hpl4, hpl16, -⟩ := pl_facts hpre
  have hpw48 := hf.pw48
  have hpwa : S.mem.accessible pw (24 * pl) true = true := by
    rw [hc.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hb48 := hc.scr.b48
  have hnb := nb_le hpl16 hw128
  have hfr' := hfr
  obtain ⟨hsp, h5, h14, hfs, hx15, hdf⟩ := hfr'
  have hspN : (S.regs 4).toNat = (s.regs 4).toNat - 176 := by
    have := hpre.1.2.1.1; simp only [K, regSP] at this; rw [hsp]; exact tN (by omega)
  have hwbf : S.mem.accessible RunIface.wbA 4 false = true := by
    rw [hc.fr.accessible]; exact hpre.2.2.1.2.2.2.2.2.2.2.2.2.2.1
  have mo : ∀ a c : Nat, BitVec.ofNat 64 a * BitVec.ofNat 64 c = BitVec.ofNat 64 (a * c) := fun a c => by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]
  have ha1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm
  have ha2 : BitVec.ofNat 64 i + 2#64 = BitVec.ofNat 64 (i + 2) := (BitVec.ofNat_add i 2).symm
  have m8 := mo (i + 2) (W lm)
  have m9 := mo i (W lm)
  have m10 := mo (i + 1) (W lm)
  have c1 : (i + 2) * W lm ≤ NB pl lm := Nat.mul_le_mul_right _ (by omega)
  have c2 : (i + 1) * W lm ≤ (i + 2) * W lm := Nat.mul_le_mul_right _ (by omega)
  have c3 : i * W lm ≤ (i + 1) * W lm := Nat.mul_le_mul_right _ (by omega)
  have hpe : pw + 24 * i + 24 ≤ pw + 24 * pl := by omega
  have hRb : 184 + kc ≤ (s.regs 4).toNat := by have := hpre.1.2.1.1; simpa only [regSP, K] using this
  have hR64 := (s.regs 4).isLt
  have hsub8 : BitVec.ofNat 64 ((s.regs 4).toNat - 176) - 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have t184 : (BitVec.ofNat 64 ((s.regs 4).toNat - 184)).toNat = (s.regs 4).toNat - 184 := tN (by omega)
  have hacc184 : S.mem.accessible ((s.regs 4).toNat - 184) 8 true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2; simp only [regSP, K, A] at this
    exact Janus.Arm64.Memory.accessible_mono _ this (by omega) (by omega)
  unfold Goal
  have hiw : i * W lm ≤ 2176 := by
    have := Nat.mul_le_mul (show i ≤ 17 by omega) hw128; omega
  have hptr := ptr_eq bp (W lm) (i * W lm) (by omega) hw128 hiw (by have := hc.scr.b48; omega)
  have hl3 := three_eq i (by omega)
  have hd2 : ∀ (a1 a2 : Nat), a1 = pw + 24 * i + 8 → a2 = pw + 24 * i + 16 → ∀ j, j < i →
      PwT ((S.mem.writeLE a1 8 (W lm)).writeLE a2 8 (W lm + W lm)) pw bp lm j := fun a1 a2 e1 e2 j hj => by
    obtain ⟨f0, f1, f2⟩ := hd j hj
    exact ⟨(hdr_keep _ _ _ _ _ _ _ _ e1 e2 (by omega)).trans f0, (hdr_keep _ _ _ _ _ _ _ _ e1 e2 (by omega)).trans f1,
      (hdr_keep _ _ _ _ _ _ _ _ e1 e2 (by omega)).trans f2⟩
  have hwbpw : pw + 24 * pl ≤ 12283968 ∨ 12283968 + 4 ≤ pw := by
    have g := hpre.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2
    have v : RunIface.wbA = 12283968 := rfl
    simp only [v, win, outside_cons, outside_append, outside_nil, and_true] at g; omega
  janus64_run [hwbf, ha1, ha2, m8, m9, m10, hsp, hsub8, t184, hacc184, hptr, hl3, hwbpw]
    until [cA "runtime.gcWriteBarrier2", pcS]
  · -- the barrier is off
    have hh := hdr_rd S.mem (pw + 3 * i * 8 + 8) (pw + 3 * i * 8 + 16) (pw + 24 * i) (W lm) (by omega) (by omega)
      (by omega)
    have hc2 := ctx_own (ctx_own hc hf (W lm) (a := pw + 3 * i * 8 + 8) (k := 8)
      ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩) hf (W lm + W lm) (a := pw + 3 * i * 8 + 16) (k := 8)
        ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
    refine fillP hkc hpre k hi _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hc2
      (hd2 _ _ (three8 pw i) (three16 pw i)) hh.1 hh.2 hb
    all_goals first | exact hfs | exact hx15 | exact hdf | janus64_simp
  · -- the barrier is on
    have hh := hdr_rd S.mem (pw + 3 * i * 8 + 8) (pw + 3 * i * 8 + 16) (pw + 24 * i) (W lm) (by omega) (by omega)
      (by omega)
    have hc2 := ctx_own (ctx_own hc hf (W lm) (a := pw + 3 * i * 8 + 8) (k := 8)
      ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩) hf (W lm + W lm) (a := pw + 3 * i * 8 + 16) (k := 8)
        ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
    have hpwF : pw + 24 * pl ≤ (s.regs 4).toNat - 184 - kc ∨ (s.regs 4).toNat + 80 ≤ pw := by
      have g := hf.pww; simp only [win, K, A, outside_cons, outside_nil, and_true] at g; omega
    have hc3 := ctx_own hc2 hf 6195795 (a := (s.regs 4).toNat - 184) (k := 8)
      ⟨by omega, Or.inl ⟨Nat.le_refl _, by omega⟩⟩
    refine wbCall hwb hpre hkc hc3 rfl (by janus64_simp) (by janus64_simp) rfl ?_ ?_
    · rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide
    · intro buf f xm yh m' zh kr hb16 hb8 hbacc hctx hrdW
      have hb8a : m'.accessible buf.toNat 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hbacc (Nat.le_refl _) (by omega)
      have hb8b : m'.accessible (buf.toNat + 8) 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hbacc (by omega) (by omega)
      have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
      janus64_run [hb8a, hb8b, hbuf64, t184] until [pcS]
      have hadd8 : BitVec.ofNat 64 ((s.regs 4).toNat - 184) + 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 176) := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hrd : ∀ v1 v2 a n, 0 < n → pw ≤ a → a + n ≤ pw + 24 * pl →
          (W2 m' buf.toNat v1 v2).readLE a n = ((S.mem.writeLE (pw + 3 * i * 8 + 8) 8 (W lm)).writeLE
            (pw + 3 * i * 8 + 16) 8 (W lm + W lm)).readLE a n := fun v1 v2 a n h0 ha hb =>
        (hrdW _ _ _ _ h0 (Or.inl ⟨ha, hb⟩)).trans (push_rd _ (pw_push hpwF ha hb))
      have hdW : ∀ j, j < i → PwT (W2 m' buf.toNat (bp + 8 * (i * W lm)) (S.mem.readLE (pw + 3 * i * 8) 8))
          pw bp lm j := fun j hj => by
        obtain ⟨f0, f1, f2⟩ := hd2 _ _ (three8 pw i) (three16 pw i) j hj
        exact ⟨(hrd _ _ (pw + 24 * j) 8 (by decide) (by omega) (by omega)).trans f0,
          (hrd _ _ (pw + 24 * j + 8) 8 (by decide) (by omega) (by omega)).trans f1,
          (hrd _ _ (pw + 24 * j + 16) 8 (by decide) (by omega) (by omega)).trans f2⟩
      have hh1 := (hrd (bp + 8 * (i * W lm)) (S.mem.readLE (pw + 3 * i * 8) 8) (pw + 24 * i + 8) 8 (by decide)
        (by omega) (by omega)).trans hh.1
      have hh2 := (hrd (bp + 8 * (i * W lm)) (S.mem.readLE (pw + 3 * i * 8) 8) (pw + 24 * i + 16) 8 (by decide)
        (by omega) (by omega)).trans hh.2
      refine fillP hkc hpre k hi _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hctx _ _) hdW hh1 hh2 hb
      · janus64_simp <;> exact hadd8
      · janus64_simp
      · janus64_simp
      · exact hfs
      · janus64_simp
      · rfl
      all_goals janus64_simp

theorem fill_all (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (kE : FillJ impl R kc b L st pw pl ws lm x xl s pl) :
    ∀ n i, i + n = pl → FillJ impl R kc b L st pw pl ws lm x xl s i := by
  intro n
  induction n with
  | zero => intro i h; rw [show i = pl by omega]; exact kE
  | succ n ih => intro i h; exact fillB hwb hkc (ih (i + 1) (by omega)) (by omega)

end

end FvModexp.Amd64.P2Pre
