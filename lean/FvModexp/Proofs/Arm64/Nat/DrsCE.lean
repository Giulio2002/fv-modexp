import FvModexp.Proofs.Arm64.Nat.DrsCN

/-!
# `divRecursiveStep` (arm64), correction loop (natdiv.go:832-843): relations (pure)

* `E`: the loop's exit `0x1ba80c` (both `i = 2` at the head and the `e ≤ 0` break jump there with `R0..R2 = qhatv`),
  at the model state `corr1 … 2 st0`.
* `Bx`: inside an iteration `i < 2` whose comparison was `> 0` (base state `stb` at the head), at memory model `st`
  (`stb` → `qhat--` → `qhatv -= v[:s]` → `uu[s:] += v[s:]`); slot `i` stored at `SP'+240`.
* `Bx.next`: the head's invariant after the iteration (`corrOnce stb`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- the model after `qhat--` -/
@[reducible] def stQ (st : Mdl.St) : Mdl.St := { st with qhat := (Mdl.subVW st.qhat 1).1 }

/-- the exit of the correction loop -/
abbrev cExit : Nat := 0x1ba80c

/-- **the correction loop's exit** (`0x1ba80c`) at the final model state -/
structure E (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) (qv : Nat) : Prop where
  pc : S.pc = BitVec.ofNat 64 cExit
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 qv
  r1 : S.regs 1 = BitVec.ofNat 64 (c.P s j U).length
  r2 : S.regs 2 = BitVec.ofNat 64 (3 * c.vl)
  mc : Mc R c s Lk bk S.mem j Z U qv
    (Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length 2 (c.st0 s j U))
  v4 : V4 c s S.mem qv (c.P s j U).length

/-- **inside a correction** (`i < 2`, comparison `> 0` at the base state `stb`), memory at model state `st` -/
structure Bx (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) (qv i : Nat) (stb st : Mdl.St) : Prop where
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  mc : Mc R c s Lk bk S.mem j Z U qv st
  v4 : V4 c s S.mem qv (c.P s j U).length
  si : S.mem.readLE (s.sp.toNat - 160) 8 = i
  hi : i < 2
  pos : 0 < Mdl.cmpQ (c.P s j U).length stb
  inv : Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length (2 - i) stb =
    Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length 2 (c.st0 s j U)

/-- the own store of the loop counter `i` (`SP'+240`) -/
@[reducible] def is1 (s : State) : List (Nat × Nat) := [(s.sp.toNat - 160, s.sp.toNat - 152)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `Mc` across the own stores of `qhatv`'s slots (`is1`: the slot `i`, `SP'+240`) -/
theorem Mc.own1 {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : Mc R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (is1 s))
    (hreg : M'.regions = M.regions) : Mc R c s Lk bk M' j Z U qv st := by
  have hcr := h.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hqw, -⟩, ⟨-, -, -, huw, -⟩,
    ⟨-, -, -, hvw, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, -⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame M M' (fw s) := hF3.mono fun x n ho => by
    simp only [fw, winA, is1, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → M'.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, is1, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have hrw := h.rg.w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (huw.of_sub h1 h2)
  have hjm : j ≤ c.u1 - c.vl := by have := h.li.2.2.2.2.2.2.2; omega
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  refine ⟨hcr, Ev.own hcr h.ev hF hreg, Fp.own hcr h.fp hF,
    h.bd.frame hF3 (by simp only [FixOut, is1, outside_cons, outside_nil, and_true]; omega)
      (by simp only [IOut, is1, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw),
    h.bs.frame hF3 (by simp only [BOut, is1, outside_cons, outside_nil, and_true]; omega), h.jB, h.li,
    ⟨by rw [hF3.readLE _ _ (by simp only [is1, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s208,
      by rw [hF3.readLE _ _ (by simp only [is1, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s256⟩,
    h.rg, by rw [limbs_congr (rt _ _ (Nat.le_refl _) (by omega))]; exact h.qk,
    by rw [limbs_congr (rd _ _ hrw)]; exact h.bf,
    by rw [limbs_congr (ru _ _ (by omega) (by omega))]; exact h.wk,
    by rw [limbs_congr (ru _ _ (Nat.le_refl _) (by omega))]; exact h.lk, h.bud,
    by rw [hF3.accessible]; exact h.qa, h.qloc, h.qal⟩

theorem V4.own1 {c : Cx} {s : State} {M M' : Memory} {qv ql : Nat} (h : V4 c s M qv ql)
    (hF : MemFrame M M' (is1 s)) (h0 : 408 ≤ s.sp.toNat) : V4 c s M' qv ql :=
  ⟨by rw [hF.readLE _ _ (by simp only [is1, outside_cons, outside_nil, and_true]; omega)]; exact h.s328,
    by rw [hF.readLE _ _ (by simp only [is1, outside_cons, outside_nil, and_true]; omega)]; exact h.s152,
    by rw [hF.readLE _ _ (by simp only [is1, outside_cons, outside_nil, and_true]; omega)]; exact h.s168⟩

/-- the head's invariant after a correction -/
theorem Bx.next {v : List Nat} {s0 ql i : Nat} {stb st0 : Mdl.St} (hi : i < 2) (hpos : 0 < Mdl.cmpQ ql stb)
    (hinv : Mdl.corr1 v s0 ql (2 - i) stb = Mdl.corr1 v s0 ql 2 st0) :
    Mdl.corr1 v s0 ql (2 - (i + 1)) (Mdl.corrOnce v s0 ql stb) = Mdl.corr1 v s0 ql 2 st0 := by
  rw [← hinv, show 2 - i = (2 - (i + 1)) + 1 by omega, Mdl.corr1, if_neg (by omega)]

/-- the head's invariant at a break (`e ≤ 0`): the state is final -/
theorem C.brk {v : List Nat} {s0 ql i : Nat} {stb st0 : Mdl.St} (hi : i < 2) (hle : Mdl.cmpQ ql stb ≤ 0)
    (hinv : Mdl.corr1 v s0 ql (2 - i) stb = Mdl.corr1 v s0 ql 2 st0) : stb = Mdl.corr1 v s0 ql 2 st0 := by
  rw [← hinv, show 2 - i = (2 - (i + 1)) + 1 by omega, Mdl.corr1, if_pos hle]

/-- the head's invariant at `i = 2`: the state is final -/
theorem C.done {v : List Nat} {s0 ql i : Nat} {stb st0 : Mdl.St} (hi : i ≤ 2) (h2 : ¬ i < 2)
    (hinv : Mdl.corr1 v s0 ql (2 - i) stb = Mdl.corr1 v s0 ql 2 st0) : stb = Mdl.corr1 v s0 ql 2 st0 := by
  rw [← hinv, show 2 - i = 0 by omega, Mdl.corr1]

end FvModexp.Arm64.DivRec
