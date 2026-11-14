import FvModexp.Proofs.Amd64.Exp.P2PreXTr
import FvModexp.Proofs.Amd64.Exp.P2PreXJ

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): `X1J` → `trunc(x)` (agent divmc s64; twin of infra's
`Arm64/Exp/P2PreX1`)

From the pointer store of `powers[0]` (`+0x2ba`): `powers[0].ptr = buf`, the reslice checks of `powers[0][:1:w]`
(`+0x2c0/+0x2c9`), `powers[0].len/cap = (1, w)` (now `PwD 0`: value `1 = p2Pow 0`), the bounds check of `powers[1]`
(`+0x2e0`), the argument loads and the call `powers[1].trunc(x, logM)` (`+0x316`, `callTrX` → `JT`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem jX1 (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) (hnf : ns.contains fn = false)
    {stkT aboveT : Nat} (htr : Trunc.Hyp2 impl R ns stkT aboveT) (hkT : stkT ≤ kc) (haT : aboveT ≤ 88)
    (hkc : 4608 ≤ kc) (kT : JT impl R kc b L st pw pl ws lm x xl s) :
    X1J impl R kc b L st pw pl ws lm x xl s := by
  intro S bp L1 b1 hpre hpc hfr h2 h3 h6 h10 h12 h1 hc hd hone hb
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
  have hRb : 184 + kc ≤ (s.regs 4).toNat := by have := hf.w.sp; simpa only [K] using this
  have hR64 := (s.regs 4).isLt
  have hsp48 : (s.regs 4).toNat + 80 ≤ 2 ^ 48 := hf.sp48
  have hsub8 : BitVec.ofNat 64 ((s.regs 4).toNat - 176) - 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have t184 : (BitVec.ofNat 64 ((s.regs 4).toNat - 184)).toNat = (s.regs 4).toNat - 184 := tN (by omega)
  have hwm : S.mem.accessible ((s.regs 4).toNat - (184 + kc)) (184 + kc + 80) true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2; simpa only [regSP, K, A] using this
  have hpwF : pw + 24 * pl ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ pw := by
    have g := hf.pww; simp only [win, K, A, outside_cons, outside_nil, and_true] at g; omega
  have hboF : bp + 8 * NB pl lm ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ bp := by
    have := wok_win (wok_buf (zp := bp) (zn := 8 * NB pl lm) hc.scr (Nat.le_refl _) (Nat.le_refl _)) hf.w
      (by have := nb_pos (pl := pl) (lm := lm) (by omega) hw1; simp only; omega)
    simp only [K, A] at this; omega
  have hnb0 : 8 ≤ 8 * NB pl lm := by have := nb_pos (pl := pl) (lm := lm) (by omega) hw1; omega
  have hbpw : pw + 24 * pl ≤ bp ∨ bp + 8 * NB pl lm ≤ pw := by
    have := hc.scr.apart (p := pw) (n := 24 * pl) (Or.inr hf.pwrt) fun _ => (pw_sep_stk hpre).2.1
    unfold Apart at this; omega
  obtain ⟨-, -, -, -, e4, e5, e6, e7, -, -, -⟩ := hc.sl
  have f224 : S.mem.readLE ((s.regs 4).toNat - 176 + 224) 8 = lm := by
    rw [show (s.regs 4).toNat - 176 + 224 = (s.regs 4).toNat + 48 by omega]; exact e4
  have f232 : S.mem.readLE ((s.regs 4).toNat - 176 + 232) 8 = x := by
    rw [show (s.regs 4).toNat - 176 + 232 = (s.regs 4).toNat + 56 by omega]; exact e5
  have f240 : S.mem.readLE ((s.regs 4).toNat - 176 + 240) 8 = xl := by
    rw [show (s.regs 4).toNat - 176 + 240 = (s.regs 4).toNat + 64 by omega]; exact e6
  have f248 : S.mem.readLE ((s.regs 4).toNat - 176 + 248) 8 = (s.regs 11).toNat := by
    rw [show (s.regs 4).toNat - 176 + 248 = (s.regs 4).toNat + 72 by omega]; exact e7
  obtain ⟨t0, t1, t2⟩ := hd 1 (by omega) (by omega)
  have t0' : S.mem.readLE (pw + 24) 8 = bp + 8 * (1 * W lm) := t0
  have t1' : S.mem.readLE (pw + 32) 8 = W lm := t1
  have t2' : S.mem.readLE (pw + 40) 8 = 2 * W lm := t2
  have wr : ∀ (M0 : Memory) (c v a n : Nat), a + n ≤ c ∨ c + 8 ≤ a → (M0.writeLE c 8 v).readLE a n = M0.readLE a n :=
    fun M0 c v a n h => Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have wself : ∀ (M0 : Memory) (c v : Nat), v < 2 ^ 64 → (M0.writeLE c 8 v).readLE c 8 = v :=
    fun M0 c v h => by rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt h]
  -- the memory at the `trunc` entry: the three header stores of `powers[0]`, the return address
  have hc4 := ctx_own (ctx_own (ctx_own (ctx_own hc hf bp (a := pw) (k := 8)
    ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩) hf 1 (a := pw + 8) (k := 8)
    ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩) hf (W lm) (a := pw + 16) (k := 8)
    ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩) hf pcT (a := (s.regs 4).toNat - 184) (k := 8)
    ⟨by omega, Or.inl ⟨Nat.le_refl _, by omega⟩⟩
  have hr4 : ∀ a n, (a + n ≤ pw ∨ pw + 24 ≤ a) → (a + n ≤ (s.regs 4).toNat - 184 ∨ (s.regs 4).toNat - 176 ≤ a) →
      ((((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (W lm)).writeLE
        ((s.regs 4).toNat - 184) 8 pcT).readLE a n = S.mem.readLE a n := fun a n h h' => by
    rw [wr _ _ _ _ _ (by omega), wr _ _ _ _ _ (by omega), wr _ _ _ _ _ (by omega), wr _ _ _ _ _ (by omega)]
  have hone4 : ((((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (W lm)).writeLE
      ((s.regs 4).toNat - 184) 8 pcT).readLE bp 8 = 1 := by
    rw [hr4 _ _ (by omega) (by omega)]; exact hone
  have hd0 : PwD ((((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (W lm)).writeLE
      ((s.regs 4).toNat - 184) 8 pcT) pw bp lm (natVal s.mem x xl) 0 := by
    have r0 : ((((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (W lm)).writeLE
        ((s.regs 4).toNat - 184) 8 pcT).readLE pw 8 = bp := by
      rw [wr _ ((s.regs 4).toNat - 184) _ pw 8 (by omega), wr _ (pw + 16) _ pw 8 (by omega),
        wr _ (pw + 8) _ pw 8 (by omega), wself _ pw bp (by omega)]
    have r8 : ((((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (W lm)).writeLE
        ((s.regs 4).toNat - 184) 8 pcT).readLE (pw + 8) 8 = 1 := by
      rw [wr _ ((s.regs 4).toNat - 184) _ (pw + 8) 8 (by omega), wr _ (pw + 16) _ (pw + 8) 8 (by omega),
        wself _ (pw + 8) 1 (by decide)]
    have r16 : ((((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (W lm)).writeLE
        ((s.regs 4).toNat - 184) 8 pcT).readLE (pw + 16) 8 = W lm := by
      rw [wr _ ((s.regs 4).toNat - 184) _ (pw + 16) 8 (by omega), wself _ (pw + 16) (W lm) (by omega)]
    simp only [PwD, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    rw [r0, r8, r16]
    refine ⟨rfl, rfl, hw1, ?_, Or.inr ?_⟩
    · simp only [natVal, Nat.mul_one]; rw [hone4, Exp.p2Pow]; simp
    · simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; rw [hone4]; decide
  have hrs : RS0 R kc L st pw pl lm x xl s (natVal s.mem x xl) bp
      ((((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (W lm)).writeLE
        ((s.regs 4).toNat - 184) 8 pcT) L1 b1 1 :=
    ⟨hc4, fun j hj => by rw [show j = 0 by omega]; exact hd0, fun j hj hjp => by
      obtain ⟨e0, e1, e2⟩ := hd j (by omega) hjp
      exact ⟨(hr4 _ _ (by omega) (by omega)).trans e0, (hr4 _ _ (by omega) (by omega)).trans e1,
        (hr4 _ _ (by omega) (by omega)).trans e2⟩⟩
  have hra : ((((S.mem.writeLE pw 8 bp).writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (W lm)).writeLE
      ((s.regs 4).toNat - 184) 8 pcT).readLE ((s.regs 4).toNat - 184) 8 = pcT := wself _ _ _ (by decide)
  have hpreB : Hide (Pre R kc b L st pw pl ws lm x xl s) := ⟨hpre⟩
  clear hd hc hc4 hr4 hd0 hone4 hpre e4 e5 e6 e7 t0 t1 t2 hone
  unfold Goal
  janus64_run [f224, f232, f240, f248, t0', t1', t2', hwm, hpwa, hsub8, t184] until [6188320]
  refine callTrX hap hns hnf htr hkT haT hkc hpreB.h kT (xc := (s.regs 11).toNat) hrs hb _ rfl
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ rfl hra ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hx15 | rfl)

end

end FvModexp.Amd64.P2Pre
