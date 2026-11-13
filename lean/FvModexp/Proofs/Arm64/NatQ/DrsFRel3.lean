import FvModexp.Proofs.Arm64.NatQ.DrsDefs
import FvModexp.Proofs.Arm64.NatQ.DrsIfaceQ
import FvModexp.Proofs.Arm64.Nat.StackNatXDefs
import FvModexp.Proofs.Arm64.NatQ.DrsFRel
import FvModexp.Proofs.Arm64.Nat.WinIn

/-! (Q-form copy of Arm64/Nat/DrsFRel3.lean, TIGHT COSTS, asm s38)
# `divRecursiveStep` (arm64), final block segment 3: relations of `qhat.norm()`, `stk.nat(3n)`, `clear(qhatv)` (pure)

* `QF3`: `len(qhat.norm())` at `SP'+200`; `V3F`: `qhatv` at `SP'+320` (ptr), `+144` (len), `+160` (cap).
* `NF3`: at `CALL (*stack).nat(3n)` (`0x1baa48`, return `0x1baa4c`); `TF3`: the memory facts after it (`t3F_post`);
  `AF3`: after `clear(qhatv)` (`0x1baa64`). No `mark`/`restore` in the final block. Adapted from DrsA3/DrsB3S/DrsB3T.
-/

set_option autoImplicit false

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.Q.DivRec
open FvModexp.Arm64.DivRec

open FvModexp.Arm64.Q.DivLarge (DrsPreW DrsPostW)

/-- `len(qhat.norm())` (`SP'+200`) -/
structure QF3 (s : State) (M : Memory) (qn : Nat) : Prop where
  s200 : M.readLE (s.sp.toNat - 200) 8 = qn

theorem QF3.frame {s : State} {M M' : Memory} {qn : Nat} {rs : List (Nat × Nat)} (h : QF3 s M qn)
    (hF : MemFrame M M' rs) (ho : HiOut s rs) (h0 : 408 ≤ s.sp.toNat) : QF3 s M' qn :=
  ⟨by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s200⟩

/-- `qhatv` (`SP'+320` ptr, `+144` len, `+160` cap) -/
structure V3F (c : Cx) (s : State) (M : Memory) (qv ql : Nat) : Prop where
  s320 : M.readLE (s.sp.toNat - 80) 8 = qv
  s144 : M.readLE (s.sp.toNat - 256) 8 = ql
  s160 : M.readLE (s.sp.toNat - 240) 8 = 3 * c.vl

theorem V3F.frame {c : Cx} {s : State} {M M' : Memory} {qv ql : Nat} {rs : List (Nat × Nat)} (h : V3F c s M qv ql)
    (hF : MemFrame M M' rs) (ho : HiOut s rs) (h0 : 408 ≤ s.sp.toNat) : V3F c s M' qv ql :=
  ⟨by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s320,
    by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s144,
    by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s160⟩

/-- the return address of the final block's `stk.nat(3n)` -/
abbrev rF3n : Nat := 0x1baa4c

/-- **at the final block's `CALL (*stack).nat(3n)`** (`qn` = `len(qhat.norm())`) -/
structure NF3 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (X : State) (j : Nat)
    (Z U : List Nat) (qn : Nat) : Prop where
  pc : X.pc = BitVec.ofNat 64 (segAddr Extracted.program StackNat.fn)
  sp : X.sp = s.sp - 400#64
  r28 : X.regs 28 = s.regs 28
  r29 : X.regs 29 = s.sp - 408#64
  r18 : X.regs 18 = s.regs 18
  r0 : X.regs 0 = BitVec.ofNat 64 c.st
  r1 : X.regs 1 = BitVec.ofNat 64 (3 * c.vl)
  r30 : X.regs 30 = BitVec.ofNat 64 rF3n
  cr : Cr R c s
  ev : Ev R c s Lk bk X.mem
  fp : Fp R c s Lk X.mem (c.l1 s)
  bd : BdF c s X.mem Z
  jB : j ≤ c.vl / 2
  li : c.LI s j Z U
  qk : Asm.limbs X.mem c.t0 (c.vl / 2 + 1) = (c.RF s U).1
  uk : Asm.limbs X.mem c.up c.u1 = c.UF s U
  qle : qn ≤ c.vl / 2 + 1
  qv : natVal X.mem c.t0 qn = natVal X.mem c.t0 (c.vl / 2 + 1)
  qN : NatNorm X.mem c.t0 qn
  q3 : QF3 s X.mem qn
  bud : c.lo s + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq X.mem c.st ≤ bk

/-- the memory facts after the final block's `stk.nat(3n)` -/
structure TF3 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) (j : Nat)
    (Z U : List Nat) (qn : Nat) : Prop where
  cr : Cr R c s
  ev : Ev R c s Lk bk M
  fp : Fp R c s Lk M (c.l1 s + StackNat.rnd (3 * c.vl))
  bd : BdF c s M Z
  jB : j ≤ c.vl / 2
  li : c.LI s j Z U
  qk : Asm.limbs M c.t0 (c.vl / 2 + 1) = (c.RF s U).1
  uk : Asm.limbs M c.up c.u1 = c.UF s U
  qle : qn ≤ c.vl / 2 + 1
  qv : natVal M c.t0 qn = natVal M c.t0 (c.vl / 2 + 1)
  qN : NatNorm M c.t0 qn
  q3 : QF3 s M qn
  rg : Rg R c s Lk (c.qv s M) (8 * (3 * c.vl))
  fl : FL R c s Lk M
  bud : c.lo s + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq M c.st ≤ bk

/-- the return address of the final block's `clear(qhatv)` -/
abbrev rF3c : Nat := 0x1baa64

/-- **after the final block's `clear(qhatv)`** (`0x1baa64`) -/
structure AF3 (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) (qn : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 rF3c
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  cr : Cr R c s
  ev : Ev R c s Lk bk S.mem
  fp : Fp R c s Lk S.mem (c.l1 s + StackNat.rnd (3 * c.vl))
  bd : BdF c s S.mem Z
  jB : j ≤ c.vl / 2
  li : c.LI s j Z U
  qk : Asm.limbs S.mem c.t0 (c.vl / 2 + 1) = (c.RF s U).1
  uk : Asm.limbs S.mem c.up c.u1 = c.UF s U
  qle : qn ≤ c.vl / 2 + 1
  qv : natVal S.mem c.t0 qn = natVal S.mem c.t0 (c.vl / 2 + 1)
  qN : NatNorm S.mem c.t0 qn
  q3 : QF3 s S.mem qn
  v3 : V3F c s S.mem (c.qv s S.mem) (3 * c.vl)
  rg : Rg R c s Lk (c.qv s S.mem) (8 * (3 * c.vl))
  fl : FL R c s Lk S.mem
  z0 : S.mem.readLE (c.qv s S.mem) (8 * (3 * c.vl)) = 0
  bud : c.lo s + mulCQ (c.vl / 2 + 1) (c.vl / 2 - 1) + stkR c.Hq S.mem c.st ≤ bk

set_option maxHeartbeats 16000000 in
/-- **after `stk.nat(3n)`** (pure) -/
theorem t3F_post {R : RtInv} {c : Cx} {s X T : State} {Lk : List (Nat × Nat)} {bk j qn : Nat} {Z U : List Nat}
    (hN : NF3 R c s Lk bk X j Z U qn) (hspn : X.sp.toNat = s.sp.toNat - 400)
    (hq : StackNatX.PostQ R bk Lk c.Hq 4208 24 c.st (3 * c.vl) X T) (hreg : T.mem.regions = X.mem.regions) :
    T.regs 0 = BitVec.ofNat 64 (c.qv s T.mem) ∧ T.regs 1 = BitVec.ofNat 64 (3 * c.vl) ∧
      T.regs 2 = BitVec.ofNat 64 (3 * c.vl) ∧ ∃ L' b', TF3 R c s L' b' T.mem j Z U qn := by
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
  obtain ⟨fo, -, -⟩ := fo504 hws504 h0
  have ffo := fo504F hws504 h0
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
  rw [hl] at hlen hsame hgrow hmem
  have hS : ∀ x k, Outside x k (winA s c.W 96) → Outside x k (winA X 4208 24) := fun _ _ ho =>
    winA_in ho hspn (by omega) (by omega) (by omega)
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
  have hBd : BdF c s T.mem Z := hN.bd.frame hMF
    (fixOut_callee hout (by omega) (by omega) hspn (by omega) fo)
    (fOut_callee hout (by omega) (by omega) hspn (by omega) ffo) kv (ku _ _ (by omega) (by omega)) kz
  refine ⟨by rw [hq0 (by omega), hl], hq1, hq2, L', b', hcr, hEv, hFp, hBd, hN.jB, hN.li,
    by rw [limbs_congr kt0]; exact hN.qk, by rw [limbs_congr (ku _ _ (Nat.le_refl _) (by omega))]; exact hN.uk,
    hN.qle, ?_, ?_, hN.q3.frame hMF hhi h0, hrg, hFL, by have := hN.bud; omega⟩
  · show T.mem.readLE c.t0 (8 * qn) = T.mem.readLE c.t0 (8 * (c.vl / 2 + 1))
    rw [ft _ _ (Nat.le_refl _) (by have := hN.qle; omega), ft _ _ (Nat.le_refl _) (Nat.le_refl _)]; exact hN.qv
  · rcases hN.qN with h | h
    · exact Or.inl h
    · right; rw [ft _ _ (by omega) (by have := hN.qle; omega)]; exact h

end FvModexp.Arm64.Q.DivRec
