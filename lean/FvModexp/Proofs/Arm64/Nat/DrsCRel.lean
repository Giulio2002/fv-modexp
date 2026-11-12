import FvModexp.Proofs.Arm64.Nat.DrsB3S
import FvModexp.Proofs.Common.DrsMulVal

/-!
# `divRecursiveStep` (arm64), loop body segment 4–5: relations of the product and the correction loop (pure)

natdiv.go:831-842: `qhatv = qhatv.mul(stk, qhat, v[:s])`, then `for i := 0; i < 2; i++ { e := qhatv.cmp(uu.norm()); if
e <= 0 { break }; subVW(qhat, qhat, 1); c := subVV(qhatv[:s], qhatv[:s], v[:s]); if len(qhatv) > s { subVW(qhatv[s:],
qhatv[s:], c) }; addTo(uu[s:], v[s:]) }`.

The model (`Mdl.refMid` with `blk2 = false`): `p = mulI (norm qhat) v[:s]`, `ql = |p|`, the state `St = (qhat, buf, w)`
starts at `Cx.st0` (`buf = p ++ 0…` = the cleared `3n`-word buffer after the product, `w = uu`), one correction is
`Mdl.corrOnce`, the loop is `Mdl.corr1 … 2`.

* `Mc`: the memory facts during the loop at model state `st` (`qv` = `qhatv`'s array, fixed when it was allocated).
* `V4`: `qhatv`'s slots (`SP'+328` ptr, `+152` len `ql`, `+168` cap `3n`).
* `C`: the loop head `0x1ba700` (`CMP $2, R3`; `R3 = i`, `R0..R2 = qhatv`) after `i` corrections.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.DivRec

open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

/-- `qhat.norm()` after the recursive call (model) -/
@[reducible] def Cx.q0 (c : Cx) (s : State) (j : Nat) (U : List Nat) : List Nat := Mdl.norm (c.R s j U).1

/-- the product `qhat · v[:s]` (model, `Mdl.mulI`) -/
@[reducible] def Cx.P (c : Cx) (s : State) (j : Nat) (U : List Nat) : List Nat :=
  Mdl.mulI (c.q0 s j U) ((c.V s).take (c.vl / 2 - 1))

/-- the dividend after the recursive call (model) -/
@[reducible] def Cx.U2 (c : Cx) (s : State) (j : Nat) (U : List Nat) : List Nat := Mdl.upd U (j - 1) (c.R s j U).2

/-- the model state at the start of the correction loop -/
@[reducible] def Cx.st0 (c : Cx) (s : State) (j : Nat) (U : List Nat) : Mdl.St :=
  ⟨c.q0 s j U, c.P s j U ++ List.replicate (3 * c.vl - (c.P s j U).length) 0, (c.U2 s j U).drop (j - c.vl / 2)⟩

/-- the memory during the correction loop at model state `st` -/
structure Mc (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (M : Memory) (j : Nat)
    (Z U : List Nat) (qv : Nat) (st : Mdl.St) : Prop where
  cr : Cr R c s
  ev : Ev R c s Lk bk M
  fp : Fp R c s Lk M (c.l1 s + StackNat.rnd (3 * c.vl))
  bd : Bd c s M j Z
  bs : Bs c s M j
  jB : c.vl / 2 < j
  li : c.LI s j Z U
  q3 : Q3 c s M (c.q0 s j U).length
  rg : Rg R c s Lk qv (8 * (3 * c.vl))
  qk : Asm.limbs M c.t0 (c.q0 s j U).length = st.qhat
  bf : Asm.limbs M qv (3 * c.vl) = st.buf
  wk : Asm.limbs M (c.up + 8 * (j - c.vl / 2)) (c.u1 - (j - c.vl / 2)) = st.w
  lk : Asm.limbs M c.up (j - c.vl / 2) = (c.U2 s j U).take (j - c.vl / 2)
  bud : c.lo s + (j / (c.vl / 2)) * c.K s ≤ bk
  qa : M.accessible qv (8 * (3 * c.vl)) true = true
  qloc : Loc R c s qv (8 * (3 * c.vl))
  qal : qv % 8 = 0
  fl : FL R c s Lk M

/-- `qhatv`'s slots -/
structure V4 (c : Cx) (s : State) (M : Memory) (qv ql : Nat) : Prop where
  s328 : M.readLE (s.sp.toNat - 72) 8 = qv
  s152 : M.readLE (s.sp.toNat - 248) 8 = ql
  s168 : M.readLE (s.sp.toNat - 232) 8 = 3 * c.vl

theorem V4.frame {c : Cx} {s : State} {M M' : Memory} {qv ql : Nat} {rs : List (Nat × Nat)} (h : V4 c s M qv ql)
    (hF : MemFrame M M' rs) (ho : HiOut s rs) (h0 : 408 ≤ s.sp.toNat) : V4 c s M' qv ql :=
  ⟨by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s328,
    by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s152,
    by rw [hF.readLE _ _ (ho.of_sub (by omega) (by omega))]; exact h.s168⟩

theorem q0_len {c : Cx} {s : State} {j : Nat} {U : List Nat} : (c.q0 s j U).length ≤ c.vl / 2 + 1 := by
  have e : (c.R s j U).1.length = c.vl / 2 + 1 := by
    simp only [Cx.R, Mdl.blockR, Mdl.recI, Mdl.length_toL, List.length_replicate]
  exact Nat.le_trans (Mdl.length_norm_le _) (Nat.le_of_eq e)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `Mc` across the own stores of `qhatv`'s slots (`is3`) -/
theorem Mc.own3 {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : Mc R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (is3 s))
    (hreg : M'.regions = M.regions) : Mc R c s Lk bk M' j Z U qv st := by
  have hcr := h.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hqw, -⟩, ⟨-, -, -, huw, -⟩,
    ⟨-, -, -, hvw, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, -⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame M M' (fw s) := hF3.mono fun x n ho => by
    simp only [fw, winA, is3, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → M'.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, is3, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have hrw := h.rg.w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (huw.of_sub h1 h2)
  have hjm : j ≤ c.u1 - c.vl := by have := h.li.2.2.2.2.2.2.2; omega
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  refine ⟨hcr, Ev.own hcr h.ev hF hreg, Fp.own hcr h.fp hF,
    h.bd.frame hF3 (by simp only [FixOut, is3, outside_cons, outside_nil, and_true]; omega)
      (by simp only [IOut, is3, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw),
    h.bs.frame hF3 (by simp only [BOut, is3, outside_cons, outside_nil, and_true]; omega), h.jB, h.li,
    ⟨by rw [hF3.readLE _ _ (by simp only [is3, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s208,
      by rw [hF3.readLE _ _ (by simp only [is3, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s256⟩,
    h.rg, by rw [limbs_congr (rt _ _ (Nat.le_refl _) (by omega))]; exact h.qk,
    by rw [limbs_congr (rd _ _ hrw)]; exact h.bf,
    by rw [limbs_congr (ru _ _ (by omega) (by omega))]; exact h.wk,
    by rw [limbs_congr (ru _ _ (Nat.le_refl _) (by omega))]; exact h.lk, h.bud,
    by rw [hF3.accessible]; exact h.qa, h.qloc, h.qal, FL.own hcr h.fl rd⟩

/-- the head of the correction loop -/
abbrev cHead : Nat := 0x1ba700

/-- **the correction loop's head** after `i` corrections (`0x1ba700`) -/
structure C (R : RtInv) (c : Cx) (s : State) (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat)
    (Z U : List Nat) (qv i : Nat) (st : Mdl.St) : Prop where
  pc : S.pc = BitVec.ofNat 64 cHead
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  r0 : S.regs 0 = BitVec.ofNat 64 qv
  r1 : S.regs 1 = BitVec.ofNat 64 (c.P s j U).length
  r2 : S.regs 2 = BitVec.ofNat 64 (3 * c.vl)
  r3 : S.regs 3 = BitVec.ofNat 64 i
  mc : Mc R c s Lk bk S.mem j Z U qv st
  v4 : V4 c s S.mem qv (c.P s j U).length
  hi : i ≤ 2
  inv : Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length (2 - i) st =
    Mdl.corr1 (c.V s) (c.vl / 2 - 1) (c.P s j U).length 2 (c.st0 s j U)

end FvModexp.Arm64.DivRec
