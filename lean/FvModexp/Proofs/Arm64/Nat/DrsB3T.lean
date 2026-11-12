import FvModexp.Proofs.Arm64.Nat.DrsB3S

set_option autoImplicit false

/-!
# `divRecursiveStep` (arm64), loop body segment 3b: after `stk.nat(3n)` (natdiv.go:829; pure)

`t3_post`: `StackNat.PostL` of the call → `T3` (stack length `l1 + rnd(3n)`, `qhatv` at `stW + 8·l1`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

set_option maxHeartbeats 16000000 in
/-- **after `stk.nat(3n)`** (pure) -/
theorem t3_post {R : RtInv} {c : Cx} {s X T : State} {Lk : List (Nat × Nat)} {bk j qn : Nat} {Z U : List Nat}
    (hN : N3 R c s Lk bk X j Z U qn) (hspn : X.sp.toNat = s.sp.toNat - 400)
    (hq : StackNat.PostL R bk Lk 4208 24 c.st (3 * c.vl) X T) (hreg : T.mem.regions = X.mem.regions) :
    T.regs 0 = BitVec.ofNat 64 (c.qv s T.mem) ∧ T.regs 1 = BitVec.ofNat 64 (3 * c.vl) ∧
      T.regs 2 = BitVec.ofNat 64 (3 * c.vl) ∧ ∃ L' b', T3 R c s L' b' T.mem j Z U qn := by
  have hcr := hN.cr; have hev := hN.ev; have hfp := hN.fp
  have hW := hcr.hW; have hWg := drsW_ge c.vl; have h40 := hcr.h40
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨-, -, hqh, hqo, -⟩, ⟨-, -, huh, huo, -⟩, ⟨-, -, hvh, hvo, -, -, -⟩, -, -, -,
    ⟨-, hstw, -, -⟩, -, ⟨hqs, -⟩, ⟨hus, -⟩, ⟨hvs, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, hw⟩, -, hout, -, -, -, -⟩ := hce
  obtain ⟨hq0, hq1, hq2, L', b', ⟨hx, hbud, hinv⟩, hok, hlen, hsame, hgrow, hMF, hLF, hmem⟩ := hq
  have hl := hfp.len
  have hlc : stLen X.mem c.st ≤ stCap X.mem c.st := hev.sok.2.2.2.2.2.1
  have fq := hfp.fq; have fu := hfp.fu; have fv := hfp.fv; have ffw := hfp.fw; have ft0 := hfp.ft0
  rw [← hl] at fq fu fv ffw ft0
  have h0 : 408 ≤ s.sp.toNat := by omega
  have hws504 : Outside (s.sp.toNat - 408) 504 (stkWs X.mem c.st) := by
    have a3 := out504 hstw (by omega) (by omega)
    have a4 := out504 ffw (by omega) (by omega)
    simp only [stkWs, outside_cons, outside_nil, and_true] at a3 a4 ⊢
    refine ⟨a3, ?_⟩
    rw [show stW X.mem c.st + 8 * stCap X.mem c.st = stW X.mem c.st + 8 * stLen X.mem c.st +
      8 * (stCap X.mem c.st - stLen X.mem c.st) by omega]; exact a4
  obtain ⟨fo, io, bo⟩ := fo504 hws504 h0
  have hhi : HiOut s (R.rt ++ winA X 4208 24 ++ stkWs X.mem c.st) :=
    hiOut_callee hout (by omega) (by omega) hspn (by omega) (hws504.of_sub (by omega) (by omega))
  -- reads kept
  have kp : ∀ {x n : Nat}, Held R Lk x n → Outside x n (win s c.W 96) → Apart x n c.st 24 →
      Apart x n (stW X.mem c.st + 8 * stLen X.mem c.st) (8 * (stCap X.mem c.st - stLen X.mem c.st)) →
      T.mem.readLE x n = X.mem.readLE x n := fun hh hw' h3 h4 => by
    refine keepRd hcr hspn (by omega) (by omega) hMF hLF hh hw' ?_
    unfold Apart at h3 h4
    simp only [stkWs, outside_cons, outside_nil, and_true]
    omega
  have kv : T.mem.readLE c.vp (8 * c.vl) = X.mem.readLE c.vp (8 * c.vl) := kp (hext.held hvh) hvo hvs fv.symm
  have ku : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → T.mem.readLE x n = X.mem.readLE x n := fun x n h1 h2 =>
    kp (hext.held (huh.sub h1 h2)) (huo.of_sub h1 h2) (apS hus h1 h2) (apS fu.symm h1 h2)
  have kz : T.mem.readLE c.qp (8 * c.ql) = X.mem.readLE c.qp (8 * c.ql) := kp (hext.held hqh) hqo hqs fq.symm
  have kt0 : T.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = X.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) :=
    kp (hev.ext.held hcr.t0h) hcr.t0w hcr.t0st ft0.symm
  have ft : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → T.mem.readLE x n = X.mem.readLE x n :=
    fun x n h1 h2 => rd_sub kt0 h1 h2
  -- the environment
  rw [hl] at hlen hsame hgrow hbud hmem
  have hS : ∀ x k, Outside x k (winA s c.W 96) → Outside x k (winA X 4208 24) := fun x k ho => by
    simp only [winA, outside_cons, outside_nil, and_true] at ho ⊢; rw [hspn]; omega
  have hsar : (stW T.mem c.st = stW X.mem c.st ∧ stCap T.mem c.st = stCap X.mem c.st) ∨
      (InRanges (stW T.mem c.st) (8 * stCap T.mem c.st) R.rt ∧
        ApartAll (stW T.mem c.st) (8 * stCap T.mem c.st) Lk) := by
    by_cases hg : c.l1 s + StackNat.rnd (3 * c.vl) ≤ stCap X.mem c.st
    · exact Or.inl (hsame hg)
    · exact Or.inr (hgrow (by omega))
  have hMF' : MemFrame X.mem T.mem (R.rt ++ winA X 4208 24 ++ [] ++ stkWs X.mem c.st) := by
    rw [List.append_nil]; exact hMF
  have hl' : stLen s.mem c.st ≤ stLen X.mem c.st := by rw [hl]; simp only [Cx.l1]; omega
  rw [hN.r28] at hinv
  have hEv : Ev R c s L' b' T.mem := Ev.callG hcr hev hl' hMF' hLF hS
    (fun _ _ _ => by simp only [outside_nil]) (fun _ _ _ _ => by simp only [outside_nil]) hx hinv hok hsar hreg
    (ArrIn.of_nat (L1 := L') (m0 := X.mem) (m := T.mem) hok.2.2.2.2.2.1 hlen hsame hmem)
  obtain ⟨hFp, hRg, hFL⟩ := Fp.grow (lM' := c.l1 s + StackNat.rnd (3 * c.vl)) hcr hev hfp (by omega)
    (by simp only [Cx.l1, StackNat.rnd]; omega) hok hlen hsar
  have hrg : Rg R c s L' (c.qv s T.mem) (8 * (3 * c.vl)) :=
    hRg.sub (Nat.le_refl _) (by simp only [Cx.qv, StackNat.rnd]; omega)
  have hBd : Bd c s T.mem j Z := hN.bd.frame hMF
    (fixOut_callee hout (by omega) (by omega) hspn (by omega) fo)
    (iOut_callee hout (by omega) (by omega) hspn (by omega) io) kv (ku _ _ (by omega) (by omega)) kz
  have hBs : Bs c s T.mem j := hN.bs.frame hMF (bOut_callee hout (by omega) (by omega) hspn (by omega) bo)
  refine ⟨by rw [hq0 (by omega), hl], hq1, hq2, L', b', hcr, hEv, hFp, hBd, hBs, hN.jB, hN.li,
    by rw [limbs_congr kt0]; exact hN.qk, by rw [limbs_congr (ku _ _ (Nat.le_refl _) (by omega))]; exact hN.uk,
    hN.qle, ?_, ?_, hN.q3.frame hMF hhi h0, hrg, hFL, by have := hN.bud; omega⟩
  · show T.mem.readLE c.t0 (8 * qn) = T.mem.readLE c.t0 (8 * (c.vl / 2 + 1))
    rw [ft _ _ (Nat.le_refl _) (by have := hN.qle; omega), ft _ _ (Nat.le_refl _) (Nat.le_refl _)]; exact hN.qv
  · rcases hN.qN with h | h
    · exact Or.inl h
    · right; rw [ft _ _ (by omega) (by have := hN.qle; omega)]; exact h

end FvModexp.Arm64.DivRec
