import FvModexp.Proofs.Amd64.Exp.P2PreXJ
import FvModexp.Proofs.Amd64.Exp.P2PreMv
import FvModexp.Proofs.Amd64.Exp.P2PreWbC
import FvModexp.Proofs.Common.BitArith

set_option autoImplicit false

/-!
# `buildPrecomputationWindowModPower2` (amd64): `powers[0] = powers[0].set(natOne)` (nat.go:878) (agent divmc s63;
twin of infra's `Arm64/Exp/P2PreX`)

`exitF`: `FillJ len` (the fill loop exits at `+0xd7`) → `X1J`: `natOne`'s header read (`+0x16e … +0x185`, the
capacity `2 w ≥ 1` kept), `memmove(buf, natOne.ptr, 8)` `+0x268` (spills `[RSP-80] = 2 w`, `[RSP-88] = 1`,
`[RSP-24] = buf`), the header store `(1, 2 w)` `+0x297`, the barrier test `+0x29f` and (barrier on) `gcWriteBarrier2`
`+0x2ae` with its buffer stores.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2Pre

open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkSep)

section
variable {impl : List Amd64.Segment} {R : RtInv} {kc : Nat} {b : Nat} {L : List (Nat × Nat)}
    {st pw pl ws lm x xl : Nat} {s : State}

set_option maxRecDepth 20000 in
/-- `natOne` at a memory with the context: its header / word reads, readable, held, apart from `buf` -/
theorem one_ctx {bp : Nat} {M : Memory} {L1 : List (Nat × Nat)} {b1 op : Nat}
    (hc : Ctx R kc L st pw pl lm x xl s bp M L1 b1)
    (hone : NatOne R L s.mem op (win s (K kc) A ++ LW s pw pl st)) (hsop : StkSep s.mem st op 8) :
    M.readLE natOneA 8 = op ∧ M.readLE (natOneA + 8) 8 = 1 ∧ M.readLE op 8 = 1 ∧
      M.accessible natOneA 24 false = true ∧ M.accessible op 8 false = true ∧ op + 8 ≤ 2 ^ 48 ∧
      Held R L1 op 8 ∧ Outside op 8 (win s (K kc) A ++ LW s pw pl st) ∧ Apart bp (8 * NB pl lm) op 8 := by
  obtain ⟨o0, o1, -, o3, oa, ort, ow, oacc, o48, oh, oow⟩ := hone
  have hO : ∀ a n, Outside a n R.rt → Outside a n (win s (K kc) A ++ LW s pw pl st) →
      M.readLE a n = s.mem.readLE a n :=
    fun a n h1 h2 => hc.fr.readLE a n (by simp only [AW, outside_append] at h2 ⊢; exact ⟨⟨h1, h2.1⟩, h2.2⟩)
  have hop : M.readLE op 8 = s.mem.readLE op 8 := by
    rcases oh with hL | hR
    · refine hc.lf.readLE op 8 hL ?_
      simp only [LW, outside_append] at oow ⊢
      exact oow.2
    · exact hO op 8 hR oow
  refine ⟨?_, ?_, hop.trans o3, by rw [hc.fr.accessible]; exact oa, by rw [hc.fr.accessible]; exact oacc, o48,
    hc.le.held oh, oow, hc.scr.apart oh fun _ => hsop.2.1⟩
  · rw [hO natOneA 8 (ort.of_sub (by omega) (by omega)) (ow.of_sub (by omega) (by omega))]; exact o0
  · rw [hO (natOneA + 8) 8 (ort.of_sub (by omega) (by omega)) (ow.of_sub (by omega) (by omega))]; exact o1

/-- the return address of the `memmove` call -/
abbrev mvR : Nat := 0x5e8900 + 0x26d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem exitF (hmv : MemmoveLive64 (LibW.program.link impl) mvE 4096 R)
    (hwb : WbLiveContract64 (LibW.program.link impl) wbE 4096 R 2) (hkc : 4608 ≤ kc)
    (kX : X1J impl R kc b L st pw pl ws lm x xl s) :
    FillJ impl R kc b L st pw pl ws lm x xl s pl := by
  intro S bp L1 b1 hpre hpc hfr h0 h1 h2 h6 h3 h7 hc hd _ hb
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
  have hRb : 184 + kc ≤ (s.regs 4).toNat := by have := hpre.1.2.1.1; simpa only [regSP, K] using this
  have hR64 := (s.regs 4).isLt
  have hsub8 : BitVec.ofNat 64 ((s.regs 4).toNat - 176) - 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 184) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have t184 : (BitVec.ofNat 64 ((s.regs 4).toNat - 184)).toNat = (s.regs 4).toNat - 184 := tN (by omega)
  have hwS : S.mem.accessible ((s.regs 4).toNat - (184 + kc)) (184 + kc + 80) true = true := by
    rw [hc.fr.accessible]; have := hpre.1.2.1.2.2; simpa only [regSP, K, A] using this
  have hacc : ∀ c, (s.regs 4).toNat - 184 ≤ c → c + 8 ≤ (s.regs 4).toNat + 80 → S.mem.accessible c 8 true = true :=
    fun c e1 e2 => Janus.Arm64.Memory.accessible_mono _ hwS (by omega) (by omega)
  have a184 := hacc ((s.regs 4).toNat - 184) (Nat.le_refl _) (by omega)
  have a80 := hacc ((s.regs 4).toNat - 80) (by omega) (by omega)
  have a88 := hacc ((s.regs 4).toNat - 88) (by omega) (by omega)
  have a24 := hacc ((s.regs 4).toNat - 24) (by omega) (by omega)
  obtain ⟨t0, t1, t2⟩ := hd 0 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_mul] at t0 t1 t2
  obtain ⟨op, hone, hsop⟩ := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨n0, n8, n1, nacc, oacc, o48, oheld, oout, obuf⟩ := one_ctx hc hone hsop
  have hne : (BitVec.ofNat 64 bp = BitVec.ofNat 64 op) = False := by
    simp only [eq_iff_iff, iff_false]; intro e
    have := congrArg BitVec.toNat e
    rw [tN (by omega), tN (by omega)] at this
    subst this; unfold Apart at obuf; have := nb_pos (pl := pl) (lm := lm) (by omega) hw1; omega
  have hne' : (BitVec.ofNat 64 op = BitVec.ofNat 64 bp) = False := by
    simp only [eq_iff_iff, iff_false]; intro e; rw [e] at hne; simp at hne
  have hnA : natOneA = 12050400 := rfl
  rw [hnA] at n0 n8 nacc
  unfold Goal
  janus64_run [n0, n8, nacc, t0, t2, hsp, hsub8, t184, a184, a80, a88, a24, hne, hne', BitVec.msb_eq_decide] until [mvE, 0x5e8900 + 0x297]
  · exfalso
    unfold Apart at obuf; have := nb_pos (pl := pl) (lm := lm) (by omega) hw1; omega
  have hX : s.xmm 15 = 0 ∧ s.df = false := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hopH : Hide (op + 8 ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ op) := by
    simp only [win, LW, K, A, outside_append, outside_cons, outside_nil, and_true] at oout
    exact ⟨by omega⟩
  have hsw : op + 8 ≤ (s.regs 4).toNat - 184 - 4096 ∨ (s.regs 4).toNat - 184 + 32 ≤ op := by
    have := hopH.h; omega
  have hboH : Hide (bp + 8 * NB pl lm ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ bp) := by
    have := wok_win (wok_buf (zp := bp) (zn := 8 * NB pl lm) hc.scr (Nat.le_refl _) (Nat.le_refl _)) hf.w
      (by have := nb_pos (pl := pl) (lm := lm) (by omega) hw1; simp only; omega)
    simp only [K, A] at this; exact ⟨by omega⟩
  have hpwF : Hide (pw + 24 * pl ≤ (s.regs 4).toNat - (184 + kc) ∨ (s.regs 4).toNat + 80 ≤ pw) := by
    have g := hf.pww; simp only [win, K, A, outside_cons, outside_nil, and_true] at g; exact ⟨by omega⟩
  have hbpw : Hide (pw + 24 * pl ≤ bp ∨ bp + 8 * NB pl lm ≤ pw) := by
    have := hc.scr.apart (p := pw) (n := 24 * pl) (Or.inr hf.pwrt) fun _ => hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
    unfold Apart at this; exact ⟨by omega⟩
  have hc3 := ctx_own (ctx_own (ctx_own (ctx_own hc hf (2 * W lm) (a := (s.regs 4).toNat - 176 + 96) (k := 8)
    ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩) hf 1 (a := (s.regs 4).toNat - 176 + 88) (k := 8)
    ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩) hf bp (a := (s.regs 4).toNat - 176 + 152) (k := 8)
    ⟨by omega, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩) hf mvR (a := (s.regs 4).toNat - 184) (k := 8)
    ⟨by omega, Or.inl ⟨Nat.le_refl _, by omega⟩⟩
  refine mvCall hmv hpre hkc hc3 rfl (by janus64_simp) (by janus64_simp) rfl ?_ (by rw [← hX.1]; exact hx15)
    (by rw [← hX.2]) (d := bp) (src := op) (by janus64_simp) (by janus64_simp) (by janus64_simp) (Nat.le_refl _)
    (by have := nb_pos (pl := pl) (lm := lm) (by omega) hw1; omega)
    (by simp only [Janus.Arm64.Memory.accessible_writeLE]; exact oacc) o48 hsw
    fun junk f xm yh m zh kr hcm hrd hcp => ?_
  · rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide
  have hR := (s.regs 4).toNat
  have wr : ∀ (M0 : Memory) (c v a n : Nat), a + n ≤ c ∨ c + 8 ≤ a → (M0.writeLE c 8 v).readLE a n = M0.readLE a n :=
    fun M0 c v a n h => Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have wself : ∀ (M0 : Memory) (c v : Nat), v < 2 ^ 64 → (M0.writeLE c 8 v).readLE c 8 = v :=
    fun M0 c v h => by rw [Janus.Arm64.Memory.readLE_writeLE_self, Nat.mod_eq_of_lt h]
  have hbo := hboH.h
  have g96 : m.readLE ((s.regs 4).toNat - 176 + 96) 8 = 2 * W lm := by
    rw [hrd _ 8 (by decide) (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by omega), wr _ _ _ _ _ (by omega),
      wr _ _ _ _ _ (by omega), wr _ _ _ _ _ (by omega), wself _ _ _ (by omega)]
  have g88 : m.readLE ((s.regs 4).toNat - 176 + 88) 8 = 1 := by
    rw [hrd _ 8 (by decide) (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by omega), wr _ _ _ _ _ (by omega),
      wr _ _ _ _ _ (by omega), wself _ _ _ (by omega)]
  have g152 : m.readLE ((s.regs 4).toNat - 176 + 152) 8 = bp := by
    rw [hrd _ 8 (by decide) (Or.inr (Or.inr ⟨by omega, by omega⟩)) (by omega), wr _ _ _ _ _ (by omega),
      wself _ _ _ (by omega)]
  obtain ⟨-, -, -, e3, -, -, -, -, -, e9, e10⟩ := hcm.sl
  have f192 : m.readLE ((s.regs 4).toNat - 176 + 192) 8 = pw := by
    rw [show (s.regs 4).toNat - 176 + 192 = (s.regs 4).toNat + 16 by omega]; exact e3
  have f136 : m.readLE ((s.regs 4).toNat - 176 + 136) 8 = pl := by
    rw [show (s.regs 4).toNat - 176 + 136 = (s.regs 4).toNat - 40 by omega]; exact e9
  have f128 : m.readLE ((s.regs 4).toNat - 176 + 128) 8 = W lm := by
    rw [show (s.regs 4).toNat - 176 + 128 = (s.regs 4).toNat - 48 by omega]; exact e10
  have hpwm : m.accessible pw (24 * pl) true = true := by rw [hcm.fr.accessible]; exact hpre.2.2.2.2.2.2.2.2.2.1
  have hwbf : m.accessible RunIface.wbA 4 false = true := by
    rw [hcm.fr.accessible]; exact hpre.2.2.1.2.2.2.2.2.2.2.2.2.2.1
  have hwbv : RunIface.wbA = 12283968 := rfl
  rw [hwbv] at hwbf
  have hwbpw : pw + 24 * pl ≤ 12283968 ∨ 12283968 + 4 ≤ pw := by
    have g := hpre.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2
    simp only [win, outside_cons, outside_append, outside_nil, and_true] at g; omega
  have hwm : m.accessible ((s.regs 4).toNat - (184 + kc)) (184 + kc + 80) true = true := by
    rw [hcm.fr.accessible]; have := hpre.1.2.1.2.2; simpa only [regSP, K, A] using this
  have hadd8 : BitVec.ofNat 64 ((s.regs 4).toNat - 184) + 8#64 = BitVec.ofNat 64 ((s.regs 4).toNat - 176) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hbw := hbpw.h
  have hpf := hpwF.h
  have hoo := hopH.h
  -- after the header store `(1, 2 w)`
  have hc5 := ctx_own (ctx_own hcm hf 1 (a := pw + 8) (k := 8) ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩) hf
    (2 * W lm) (a := pw + 16) (k := 8) ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
  have hr5 : ∀ a n, (a + n ≤ pw + 8 ∨ pw + 24 ≤ a) →
      ((m.writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (2 * W lm)).readLE a n = m.readLE a n := fun a n h => by
    rw [wr _ _ _ _ _ (by omega), wr _ _ _ _ _ (by omega)]
  have hdm : ∀ j, 1 ≤ j → j < pl → ∀ c, pw + 24 * j ≤ c → c + 8 ≤ pw + 24 * j + 24 →
      ((m.writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (2 * W lm)).readLE c 8 = S.mem.readLE c 8 := by
    intro j h1 h2 c c1 c2
    rw [hr5 _ _ (by omega), hrd c 8 (by decide) (Or.inl ⟨by omega, by omega⟩) (by omega), wr _ _ _ _ _ (by omega),
      wr _ _ _ _ _ (by omega), wr _ _ _ _ _ (by omega), wr _ _ _ _ _ (by omega)]
  have hd5 : ∀ j, 1 ≤ j → j < pl → PwT ((m.writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (2 * W lm)) pw bp lm j :=
    fun j h1 h2 => by
      obtain ⟨d0, d1, d2⟩ := hd j h2
      exact ⟨(hdm j h1 h2 (pw + 24 * j) (by omega) (by omega)).trans d0,
        (hdm j h1 h2 (pw + 24 * j + 8) (by omega) (by omega)).trans d1,
        (hdm j h1 h2 (pw + 24 * j + 16) (by omega) (by omega)).trans d2⟩
  have ho5 : ((m.writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (2 * W lm)).readLE bp 8 = 1 := by
    rw [hr5 _ _ (by omega), hcp, wr _ _ _ _ _ (by omega), wr _ _ _ _ _ (by omega), wr _ _ _ _ _ (by omega),
      wr _ _ _ _ _ (by omega)]; exact n1
  have hpreB : Hide (Pre R kc b L st pw pl ws lm x xl s) := ⟨hpre⟩
  have hbpR : bp + 8 ≤ (s.regs 4).toNat - 184 ∨ (s.regs 4).toNat - 184 + 8 ≤ bp := by omega
  have hbNB : bp + 8 ≤ bp + 8 * NB pl lm := by have := nb_pos (pl := pl) (lm := lm) (by omega) hw1; omega
  clear hrd hdm hd hone hsop oout hcp hc hc3 hcm hr5 obuf oheld
  janus64_run [g96, g88, g152, f192, f136, f128, hwbf, hpwm, hwbpw, hwm, hadd8, hsub8, t184] until [wbE, pcX1]
  · -- the barrier is off
    refine kX _ bp L1 b1 hpreB.h rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ hc5 hd5 ho5 hb
    all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hadd8 | exact hx15)
  · -- the barrier is on
    have hc6 := ctx_own hc5 hf 6196147 (a := (s.regs 4).toNat - 184) (k := 8)
      ⟨by omega, Or.inl ⟨Nat.le_refl _, by omega⟩⟩
    refine wbCall hwb hpreB.h hkc hc6 rfl (by janus64_simp) (by janus64_simp) rfl ?_ ?_
    · rw [Janus.Arm64.Memory.readLE_writeLE_self]; decide
    · intro buf f2 xm2 yh2 m' zh2 kr2 hb16 hb8 hbacc hctx hrdW
      have hb8a : m'.accessible buf.toNat 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hbacc (Nat.le_refl _) (by omega)
      have hb8b : m'.accessible (buf.toNat + 8) 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hbacc (by omega) (by omega)
      have hbuf64 : buf.toNat + 8 < 2 ^ 64 := by omega
      janus64_run [hb8a, hb8b, hbuf64, hadd8] until [pcX1]
      have hr : ∀ c n, 0 < n → RdR s pw pl lm bp c n →
          (c + n ≤ (s.regs 4).toNat - 184 ∨ (s.regs 4).toNat - 184 + 8 ≤ c) →
          (W2 m' buf.toNat bp (m.readLE pw 8)).readLE c n =
            ((m.writeLE (pw + 8) 8 1).writeLE (pw + 16) 8 (2 * W lm)).readLE c n :=
        fun c n h0 h h' => (hrdW _ _ c n h0 h).trans (wr _ _ _ _ _ h')
      have hdW : ∀ j, 1 ≤ j → j < pl → PwT (W2 m' buf.toNat bp (m.readLE pw 8)) pw bp lm j := fun j h1 h2 => by
        obtain ⟨d0, d1, d2⟩ := hd5 j h1 h2
        exact ⟨(hr (pw + 24 * j) 8 (by decide) (Or.inl ⟨by omega, by omega⟩) (by omega)).trans d0,
          (hr (pw + 24 * j + 8) 8 (by decide) (Or.inl ⟨by omega, by omega⟩) (by omega)).trans d1,
          (hr (pw + 24 * j + 16) 8 (by decide) (Or.inl ⟨by omega, by omega⟩) (by omega)).trans d2⟩
      have ho6 := (hr bp 8 (by decide) (Or.inr (Or.inl ⟨Nat.le_refl _, hbNB⟩)) hbpR).trans ho5
      refine kX _ bp L1 b1 hpreB.h rfl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ (hctx _ _) hdW ho6 hb
      all_goals first | exact hfs | exact hdf | (janus64_simp <;> first | exact hadd8 | exact hx15)

end

end FvModexp.Amd64.P2Pre
