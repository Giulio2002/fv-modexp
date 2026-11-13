import FvModexp.Proofs.Amd64.NatQ.DrsFRel4
import FvModexp.Proofs.Amd64.NatQ.DrsCE

set_option autoImplicit false

/-! (amd64 twin (asm s53) of Arm64/NatQ/DrsFCE.lean; adapted from Amd64/NatQ/DrsCE.lean)
# `divRecursiveStep` (amd64), final correction loop (natdiv.go:869-878): relations (pure)

* `EF`: the loop's exit `0x5f050a` (`i = 2` at the head `0x5f0360`, `RAX/RBX/RCX = qhatv`) at the model state `Cx.sFF`
  (= `corr2 … 2 sF0`).
* `BxF`: inside a round `i < 2` whose comparison was `> 0` (base state `stb` at the head), at memory model `st`;
  slot `i` at `0xd0(SP')` = `r - 184`.
* `BxF.next` / `CF.skip` / `CF.done`: the head's invariant after a correcting / non-correcting round, and at `i = 2`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)

/-- the exit of the final correction loop -/
abbrev cExitF : Nat := 0x5f050a

/-- **the final correction loop's exit** (`0x5f050a`) at the final model state -/
structure EF (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) (qv : Nat) : Prop where
  pc : S.rip = BitVec.ofNat 64 cExitF
  sp : S.regs 4 = s.regs 4 - 392#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  df : S.df = false
  x15 : S.xmm 15 = 0#128
  r0 : S.regs 0 = BitVec.ofNat 64 qv
  r3 : S.regs 3 = BitVec.ofNat 64 (c.PF s U).length
  r1 : S.regs 1 = BitVec.ofNat 64 (3 * c.vl)
  mc : McF R c s Lk bk S.mem j Z U qv (c.sFF s U)
  v3 : V3F c s S.mem qv (c.PF s U).length

/-- **inside a correction** (`i < 2`, comparison `> 0` at the base state `stb`), memory at model state `st` -/
structure BxF (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) (qv i : Nat) (stb st : Mdl.St) : Prop where
  sp : S.regs 4 = s.regs 4 - 392#64
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  fs : S.fsBase = s.fsBase
  df : S.df = false
  x15 : S.xmm 15 = 0#128
  mc : McF R c s Lk bk S.mem j Z U qv st
  v3 : V3F c s S.mem qv (c.PF s U).length
  si : S.mem.readLE ((s.regs 4).toNat - 184) 8 = i
  hi : i < 2
  pos : 0 < Mdl.cmpQ (c.PF s U).length stb
  inv : Mdl.corr2 (c.V s) (c.vl / 2 - 1) (c.PF s U).length (2 - i) stb = c.sFF s U

/-- the own stores of a round's head: the return slot `r - 400` (`CALL nat.cmp`) and the loop counter `i`
(`0xd0(SP')` = `r - 184`) -/
@[reducible] def is1F (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - 400, (s.regs 4).toNat - 392), ((s.regs 4).toNat - 184, (s.regs 4).toNat - 176)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `McF` across the own stores `is1F` -/
theorem McF.own1 {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : McF R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (is1F s))
    (hreg : M'.regions = M.regions) : McF R c s Lk bk M' j Z U qv st := by
  have hcr := h.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', -, -⟩, -⟩ := hpre.ce
  simp only [regSP] at hb'
  obtain ⟨-, -, -, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, -, huw, -⟩ := hpre.ua
  obtain ⟨-, -, -, hvw, -, -, -⟩ := hpre.va
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame M M' (fw s) := hF3.mono fun x n ho => by
    simp only [fw, win, is1F, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → M'.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, is1F, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have hrw := h.rg.w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (huw.of_sub h1 h2)
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  refine ⟨hcr, Ev.own hcr h.ev hF hreg, Fp.own hcr h.fp hF,
    h.bd.frame hF3 (by simp only [FixOut, is1F, outside_cons, outside_nil, and_true]; omega)
      (by simp only [FOut, is1F, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw), h.jB, h.li,
    ⟨by rw [hF3.readLE _ _ (by simp only [is1F, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s200⟩,
    h.rg, by rw [limbs_congr (rt _ _ (Nat.le_refl _) (by omega))]; exact h.qk,
    by rw [limbs_congr (rd _ _ hrw)]; exact h.bf,
    by rw [limbs_congr (ru _ _ (Nat.le_refl _) (by omega))]; exact h.wk, bud_cap (Cr.capOwn hcr hF) h.bud,
    by rw [hF3.accessible]; exact h.qa, h.qloc, h.qal, FL.own hcr h.fl rd⟩

theorem V3F.own1 {c : Cx} {s : State} {M M' : Memory} {qv ql : Nat} (h : V3F c s M qv ql)
    (hF : MemFrame M M' (is1F s)) (h0 : 408 ≤ (s.regs 4).toNat) : V3F c s M' qv ql :=
  ⟨by rw [hF.readLE _ _ (by simp only [is1F, outside_cons, outside_nil, and_true]; omega)]; exact h.s320,
    by rw [hF.readLE _ _ (by simp only [is1F, outside_cons, outside_nil, and_true]; omega)]; exact h.s144,
    by rw [hF.readLE _ _ (by simp only [is1F, outside_cons, outside_nil, and_true]; omega)]; exact h.s160⟩

/-- the head's invariant after a correcting round (`e > 0`) -/
theorem BxF.next {v : List Nat} {s0 ql i : Nat} {stb sF : Mdl.St} (hi : i < 2) (hpos : 0 < Mdl.cmpQ ql stb)
    (hinv : Mdl.corr2 v s0 ql (2 - i) stb = sF) :
    Mdl.corr2 v s0 ql (2 - (i + 1)) (Mdl.corrOnce v s0 ql stb) = sF := by
  rw [← hinv, show 2 - i = (2 - (i + 1)) + 1 by omega, Mdl.corr2, if_pos (by omega)]

/-- the head's invariant after a non-correcting round (`e ≤ 0`) -/
theorem CF.skip {v : List Nat} {s0 ql i : Nat} {stb sF : Mdl.St} (hi : i < 2) (hle : Mdl.cmpQ ql stb ≤ 0)
    (hinv : Mdl.corr2 v s0 ql (2 - i) stb = sF) : Mdl.corr2 v s0 ql (2 - (i + 1)) stb = sF := by
  rw [← hinv, show 2 - i = (2 - (i + 1)) + 1 by omega, Mdl.corr2, if_neg (by omega)]

/-- the head's invariant at `i = 2`: the state is final -/
theorem CF.done {v : List Nat} {s0 ql i : Nat} {stb sF : Mdl.St} (hi : i ≤ 2) (h2 : ¬ i < 2)
    (hinv : Mdl.corr2 v s0 ql (2 - i) stb = sF) : stb = sF := by
  rw [← hinv, show 2 - i = 0 by omega, Mdl.corr2]

end FvModexp.Amd64.Q.DivRec
