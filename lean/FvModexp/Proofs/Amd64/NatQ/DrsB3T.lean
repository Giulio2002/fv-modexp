import FvModexp.Proofs.Amd64.NatQ.DrsA3
import FvModexp.Proofs.Amd64.Nat.StackNatXDefs

set_option autoImplicit false

/-! (amd64 twin (asm s47) of Arm64/NatQ/DrsB3T.lean + the `T3`/`arr_loc` part of DrsB3S.lean)
# `divRecursiveStep` (amd64), loop body segment 3: after `qhatv := stk.nat(3n)` (pure)

* `T3`: the memory facts after `stk.nat(3n)`; `arr_loc`: a part of the stack's array beyond the entry length is `Loc`.
* `t3_post`: `T3` and the result registers (`RAX = qhatv`, `RBX = RCX = 3n`) from `StackNatX.PostQ`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the memory facts after `stk.nat(3n)` -/
structure T3 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) (j : Nat)
    (Z U : List Nat) (qn : Nat) : Prop where
  cr : Cr R c s
  ev : Ev R c s Lk bk M
  fp : Fp R c s Lk M (c.l1 s + StackNat.rnd (3 * c.vl))
  bd : Bd c s M j Z
  bs : Bs c s M j
  jB : c.vl / 2 < j
  li : c.LI s j Z U
  qk : Asm.limbs M c.t0 (c.vl / 2 + 1) = (c.R s j U).1
  uk : Asm.limbs M c.up c.u1 = Mdl.upd U (j - 1) (c.R s j U).2
  qle : qn ≤ c.vl / 2 + 1
  qv : natVal M c.t0 qn = natVal M c.t0 (c.vl / 2 + 1)
  qN : NatNorm M c.t0 qn
  q3 : Q3 c s M qn
  rg : Rg R c s Lk (c.qv s M) (8 * (3 * c.vl))
  fl : FL R c s Lk M
  bud : c.lo s + (j / (c.vl / 2)) * c.K s + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq M c.st ≤ bk

/-- a range of the stack's array from a length `≥` the entry length is a `Loc` range -/
theorem arr_loc {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M : Memory} {l a n : Nat}
    (h : Ev R c s Lk bk M) (hl : stLen s.mem c.st ≤ l) (h1 : stW M c.st + 8 * l ≤ a)
    (h2 : a + n ≤ stW M c.st + 8 * stCap M c.st) : Loc R c s a n := by
  rcases h.sarr with ⟨e1, e2⟩ | ⟨hin, hap⟩
  · left; rw [e1, e2] at h2; rw [e1] at h1; omega
  · right
    exact ⟨hin.sub (by omega) (by omega), ApartAll.sub' hap (by omega) (by omega)⟩

set_option maxHeartbeats 16000000 in
/-- **after `stk.nat(3n)`** (pure) -/
theorem t3_post {R : RtInv} {c : Cx} {s X T : State} {Lk : List (Nat × Nat)} {bk j qn : Nat} {Z U : List Nat}
    (hN : N3 R c s Lk bk X j Z U qn) (hspn : (X.regs 4).toNat = (s.regs 4).toNat - 400)
    (hq : StackNatX.PostQ R bk Lk c.Hq 4192 24 c.st (3 * c.vl) X T) (hreg : T.mem.regions = X.mem.regions) :
    T.regs 0 = BitVec.ofNat 64 (c.qv s T.mem) ∧ T.regs 3 = BitVec.ofNat 64 (3 * c.vl) ∧
      T.regs 1 = BitVec.ofNat 64 (3 * c.vl) ∧ ∃ L' b', T3 R c s L' b' T.mem j Z U qn := by
  have hcr := hN.cr; have hev := hN.ev; have hfp := hN.fp
  have hW := hcr.hW; have hWg := drsW64_ge c.vl; have h40 := hcr.h40
  have hu1 := hcr.u1ul; have hvu := hcr.vu1
  have hext : LiveExt R c.L Lk := hcr.ext1.trans hev.ext
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', -, -⟩, -, -, hout, -⟩ := hpre.ce
  simp only [regSP] at hb'
  obtain ⟨-, -, hqh, hqo, -⟩ := hpre.qa
  obtain ⟨-, -, huh, huo, -⟩ := hpre.ua
  obtain ⟨-, -, hvh, hvo, -, -, -⟩ := hpre.va
  obtain ⟨-, hstw, -, -⟩ := hpre.sti
  have hqs := hpre.sq.1; have hus := hpre.su.1; have hvs := hpre.sv2.1
  obtain ⟨-, -, hq0, hq3, hq1, L', b', ⟨hx, hbud, hinv⟩, hok, hlen, hsame, hgrow, hMF, hLF, hmem⟩ := hq
  have hl := hfp.len
  have hlc : stLen X.mem c.st ≤ stCap X.mem c.st := hev.sok.2.2.2.2.2.1
  have fq := hfp.fq; have fu := hfp.fu; have fv := hfp.fv; have ffw := hfp.fw; have ft0 := hfp.ft0
  rw [← hl] at fq fu fv ffw ft0
  have h0 : 408 ≤ (s.regs 4).toNat := by omega
  have hws504 : Outside ((s.regs 4).toNat - 408) 504 (stkWs X.mem c.st) := by
    have a3 := out504 hstw (by omega) (by omega)
    have a4 := out504 ffw (by omega) (by omega)
    simp only [stkWs, outside_cons, outside_nil, and_true] at a3 a4 ⊢
    refine ⟨a3, ?_⟩
    rw [show stW X.mem c.st + 8 * stCap X.mem c.st = stW X.mem c.st + 8 * stLen X.mem c.st +
      8 * (stCap X.mem c.st - stLen X.mem c.st) by omega]; exact a4
  obtain ⟨fo, io, bo⟩ := fo504 hws504 h0
  have hhi : HiOut s (R.rt ++ win X 4192 24 ++ stkWs X.mem c.st) :=
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
    kp (hext.held (huh.sub h1 h2)) (huo.of_sub h1 h2) (apL hus h1 h2) (apL fu.symm h1 h2)
  have kz : T.mem.readLE c.qp (8 * c.ql) = X.mem.readLE c.qp (8 * c.ql) := kp (hext.held hqh) hqo hqs fq.symm
  have kt0 : T.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) = X.mem.readLE c.t0 (8 * (c.vl / 2 + 1)) :=
    kp (hev.ext.held hcr.t0h) hcr.t0w hcr.t0st ft0.symm
  have ft : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → T.mem.readLE x n = X.mem.readLE x n :=
    fun x n h1 h2 => rd_sub kt0 h1 h2
  -- the environment
  rw [hl] at hlen hsame hgrow hmem
  have hS : ∀ x k, Outside x k (win s c.W 96) → Outside x k (win X 4192 24) := fun x k ho => by
    simp only [win, outside_cons, outside_nil, and_true] at ho ⊢; rw [hspn]; omega
  have hsar : (stW T.mem c.st = stW X.mem c.st ∧ stCap T.mem c.st = stCap X.mem c.st) ∨
      (InRanges (stW T.mem c.st) (8 * stCap T.mem c.st) R.rt ∧
        ApartAll (stW T.mem c.st) (8 * stCap T.mem c.st) Lk) := by
    by_cases hg : c.l1 s + StackNat.rnd (3 * c.vl) ≤ stCap X.mem c.st
    · exact Or.inl (hsame hg)
    · exact Or.inr (hgrow (by omega))
  have hMF' : MemFrame X.mem T.mem (R.rt ++ win X 4192 24 ++ [] ++ stkWs X.mem c.st) := by
    rw [List.append_nil]; exact hMF
  have hl' : stLen s.mem c.st ≤ stLen X.mem c.st := by rw [hl]; simp only [Cx.l1]; omega
  rw [hN.r14] at hinv
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
  refine ⟨by rw [hq0 (by omega), hl], hq3, hq1, L', b', hcr, hEv, hFp, hBd, hBs, hN.jB, hN.li,
    by rw [limbs_congr kt0]; exact hN.qk, by rw [limbs_congr (ku _ _ (Nat.le_refl _) (by omega))]; exact hN.uk,
    hN.qle, ?_, ?_, hN.q3.frame hMF hhi h0, hrg, hFL, by have := hN.bud; omega⟩
  · show T.mem.readLE c.t0 (8 * qn) = T.mem.readLE c.t0 (8 * (c.vl / 2 + 1))
    rw [ft _ _ (Nat.le_refl _) (by have := hN.qle; omega), ft _ _ (Nat.le_refl _) (Nat.le_refl _)]; exact hN.qv
  · rcases hN.qN with h | h
    · exact Or.inl h
    · right; rw [ft _ _ (by omega) (by have := hN.qle; omega)]; exact h

end FvModexp.Amd64.Q.DivRec
