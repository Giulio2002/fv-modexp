import FvModexp.Proofs.Amd64.CmpSum
import FvModexp.Proofs.Amd64.Nat.AddTo
import FvModexp.Proofs.Amd64.Nat.AsmCallees
import FvModexp.Proofs.Amd64.Nat.Restore
import FvModexp.Proofs.Amd64.NatQ.DrsCE
import FvModexp.Proofs.Amd64.NatQ.DrsCallS
import FvModexp.Proofs.Amd64.NatQ.DrsDG
import FvModexp.Proofs.Amd64.NatQ.DrsDV
import FvModexp.Proofs.Amd64.NatQ.DrsFCE
import FvModexp.Proofs.Amd64.NatQ.DrsFG
import FvModexp.Proofs.Amd64.NatQ.DrsFV
import FvModexp.Proofs.Amd64.NatQ.DrsFin
import FvModexp.Proofs.Amd64.NatQ.DrsMulQ
import FvModexp.Proofs.Amd64.NatQ.DrsNorm3
import FvModexp.Proofs.Amd64.NatQ.DrsNormF
import FvModexp.Proofs.Amd64.NatQ.DrsSN
import FvModexp.Proofs.Common.DrsCorrVal
import FvModexp.Proofs.Common.ExpmcFrame
import FvModexp.Proofs.Common.MaskWord
set_option autoImplicit false

/-! # amd64 `divRecursiveStep`: shared small definitions and lemmas of the loop / final-iteration segments

ROW-TIME (asm s72): the return addresses, slot lists, model updates and small call-instance lemmas that the segment
modules `DrsC*`, `DrsD*`, `DrsFC*`, `DrsFD*` (and `DrsB4D`) share, collected in ONE module that every segment imports
directly, so the segments compile independently (they formed a 16-deep import chain). Moved verbatim; names unchanged.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.GoABI0 Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Amd64.Q.DivRec

open FvModexp.Amd64.Q.DivLarge (DrsPreW DrsPostW)
open FvModexp.Amd64.Callees (VVLPre SubVVLQ SubVVHyp subVVHyp)

-- (moved from DrsB4D)
/-- a fact hidden from `janus64_run` (which destructures every conjunction in the context) -/
structure Box (P : Prop) : Prop where
  h : P

-- (moved from DrsB4D)
/-- the return address of the product -/
abbrev r4 : Nat := 0x5efd25

-- (moved from DrsC1)
/-- `nat.cmp`'s entry (`0x5e5cc0`) -/
abbrev cmpA : Nat := 6184128

-- (moved from DrsC1)
/-- the return address of the loop's `nat.cmp` -/
abbrev rC1 : Nat := 0x5efdf9

-- (moved from DrsC1)
/-- `uu`'s pointer / length / capacity in iteration `j` -/
@[reducible] def Cx.uuP (c : Cx) (j : Nat) : Nat := c.up + 8 * (j - c.vl / 2)

-- (moved from DrsC1)
@[reducible] def Cx.uuL (c : Cx) (j : Nat) : Nat := c.u1 - (j - c.vl / 2)

-- (moved from DrsC1)
theorem toIntC {a : Nat} (h : a < 2 ^ 63) : (BitVec.ofNat 64 a).toInt = (a : Int) := by
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

-- (moved from DrsC2)
/-- `nat.cmp` (segment 15) in `LibDrs.program` -/
theorem csumD (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) :
    Summary (LibDrs.program.link impl) cmpA CmpSum.Pre CmpSum.Post := by
  have hc : CodeIn64 FvModexp.Lib.CmpAmd64.program (LibDrs.program.link impl) := by
    rw [LibDrs.eq_only]
    exact Callees.codeIn_single hap (seg := Extracted.seg15) rfl
      (by simp only [Extracted.program, Extracted.segments, List.mem_cons, true_or, or_true]) (by decide)
  exact Summary.of_codeIn64 hc CmpSum.cmp_summary

-- (moved from DrsC2)
/-- the invariant survives writes inside a callee's window outside the runtime's ranges -/
theorem inv_win {R : RtInv} {b g : Nat} {L : List (Nat × Nat)} {X : State} {m m' : Memory} {k a : Nat}
    (hF : MemFrame m m' (win X k a)) (hout : Outside ((X.regs 4).toNat - k) (k + a) R.rt)
    (hsp : k ≤ (X.regs 4).toNat) (hi : R.inv b L g (view R.rt L m)) : R.inv b L g (view R.rt L m') := by
  refine RtInv.inv_frame' hF (fun r hr => ?_) hi
  simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; left; exact hout.of_sub (Nat.le_refl _) (by simp; omega)

-- (moved from DrsC2)
/-- the window-only frame keeps the live objects -/
theorem lf_winC {L : List (Nat × Nat)} {X : State} {k a : Nat} {m m' : Memory} (ws : List (Nat × Nat))
    (h : MemFrame m m' (win X k a)) (hs : LiveSep L (win X k a)) : LiveFrame m m' L ws :=
  ⟨fun x n hin _ => h.readLE x n (by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega)⟩

-- (moved from DrsC2B)
theorem cmpInt_range (a b : Nat) : Mdl.cmpInt a b = -1 ∨ Mdl.cmpInt a b = 0 ∨ Mdl.cmpInt a b = 1 := by
  unfold Mdl.cmpInt; split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

-- (moved from DrsC2B)
theorem cmpRev_range : ∀ (a b : List Nat), Mdl.cmpRev a b = -1 ∨ Mdl.cmpRev a b = 0 ∨ Mdl.cmpRev a b = 1
  | [], _ => by simp [Mdl.cmpRev]
  | [a], [] => by simp [Mdl.cmpRev]
  | [a], [b] => by simp only [Mdl.cmpRev]; exact cmpInt_range a b
  | [a], _ :: _ :: _ => by simp [Mdl.cmpRev]
  | _ :: _ :: _, [] => by simp [Mdl.cmpRev]
  | _ :: _ :: _, [_] => by simp [Mdl.cmpRev]
  | a :: a' :: xs, b :: b' :: ys => by
    simp only [Mdl.cmpRev]; split
    · exact cmpRev_range (a' :: xs) (b' :: ys)
    · exact cmpInt_range a b

-- (moved from DrsC2B)
theorem natCmp_range (x y : List Nat) : Mdl.natCmp x y = -1 ∨ Mdl.natCmp x y = 0 ∨ Mdl.natCmp x y = 1 := by
  unfold Mdl.natCmp; split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
  · exact cmpRev_range _ _

-- (moved from DrsC2B)
/-- `subVW(qhat, qhat, 1)`'s return address -/
abbrev rW1 : Nat := 0x5efe35

-- (moved from DrsC2B)
/-- the return slot of a loop call -/
@[reducible] def isR (s : State) : List (Nat × Nat) := [((s.regs 4).toNat - 400, (s.regs 4).toNat - 392)]

-- (moved from DrsC3)
theorem tN {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

-- (moved from DrsC3)
/-- `subVW` as a summary in `LibDrs` -/
theorem vwSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Summary (LibDrs.program.link impl) SubVW.entry
      (fun s => RetAddr ((Extracted.program.onlySegments [SubVW.fn]).link impl)
          (s.mem.readLE (s.regs regSP).toNat 8) ∧ s.xmm xmmZero = 0 ∧
        ArgsFrom64 s 0 [zp, zl, zc, xp, xl, xc, y] ∧ s.df = false ∧ (xl = zl ∧ SubVW.Pre R b L zp zl zc xp xc s))
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ SubVW.Post R b L zp zl xp y s s') := by
  have h := SubVW.sum impl hap R hmv b L zp zl zc xp xl xc y LibDrs.names (Callees.sub_of_all (by decide))
  rw [← LibDrs.eq_only] at h
  exact h

-- (moved from DrsC4R)
/-- `subVV.abi0`'s entry -/
abbrev subVVA : Nat := segAddr Extracted.program Callees.subVVfn

-- (moved from DrsC4R)
/-- `subVV.abi0`'s return address -/
abbrev rV1 : Nat := 0x5efe94

-- (moved from DrsC4R)
/-- the return slot and the argument words of the `subVV.abi0` call (`[r-400, r-320)`) -/
@[reducible] def isA (s : State) : List (Nat × Nat) := [((s.regs 4).toNat - 400, (s.regs 4).toNat - 320)]

-- (moved from DrsC4)
/-- the model after `qhatv[:s] -= v[:s]` -/
@[reducible] def stV (V : List Nat) (s0 : Nat) (st : Mdl.St) : Mdl.St :=
  { st with buf := (Mdl.subVV (st.buf.take s0) (V.take s0)).1 ++ st.buf.drop s0 }

-- (moved from DrsC4)
/-- the pc after the re-entry sequence of the `subVV.abi0` call -/
abbrev rV2 : Nat := 0x5efea1

-- (moved from DrsC4)
/-- `subVV.abi0` in `LibDrs` with the runtime invariant carried over -/
theorem svvD (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDrs.program.link impl) subVVA (VVLPre R b L) (SubVVLQ R b L) := by
  have c : CodeIn64 ((Extracted.program.onlySegments [Callees.subVVfn]).link impl) (LibDrs.program.link impl) := by
    rw [LibDrs.eq_only]; exact A64.codeIn_restrict_mono64 hap (Callees.sub_of_all (by decide))
  exact SubVVHyp.live (Summary.of_codeIn64 c (subVVHyp impl hap)) R b L

-- (moved from DrsC4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `Mc` across the argument stores (`isA`) -/
theorem Mc.ownA {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : Mc R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (isA s))
    (hreg : M'.regions = M.regions) : Mc R c s Lk bk M' j Z U qv st := by
  have hcr := h.cr
  have hpre := hcr.pre
  obtain ⟨-, ⟨hb', -, -⟩, -⟩ := hpre.ce
  simp only [regSP] at hb'
  obtain ⟨-, -, -, hqw, -⟩ := hpre.qa
  obtain ⟨-, -, -, huw, -⟩ := hpre.ua
  obtain ⟨-, -, -, hvw, -, -, -⟩ := hpre.va
  have hWg := drsW64_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame M M' (fw s) := hF3.mono fun x n ho => by
    simp only [fw, win, isA, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → M'.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, isA, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have hrw := h.rg.w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (huw.of_sub h1 h2)
  have hjm : j ≤ c.u1 - c.vl := by have := h.li.2.2.2.2.2.2.2; omega
  have hql : (c.q0 s j U).length ≤ c.vl / 2 + 1 := q0_len
  refine ⟨hcr, Ev.own hcr h.ev hF hreg, Fp.own hcr h.fp hF,
    h.bd.frame hF3 (by simp only [FixOut, isA, outside_cons, outside_nil, and_true]; omega)
      (by simp only [IOut, isA, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw),
    h.bs.frame hF3 (by simp only [BOut, isA, outside_cons, outside_nil, and_true]; omega), h.jB, h.li,
    ⟨by rw [hF3.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s208,
      by rw [hF3.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s256⟩,
    h.rg, by rw [limbs_congr (rt _ _ (Nat.le_refl _) (by omega))]; exact h.qk,
    by rw [limbs_congr (rd _ _ hrw)]; exact h.bf,
    by rw [limbs_congr (ru _ _ (by omega) (by omega))]; exact h.wk,
    by rw [limbs_congr (ru _ _ (Nat.le_refl _) (by omega))]; exact h.lk, bud_cap (Cr.capOwn hcr hF) h.bud,
    by rw [hF3.accessible]; exact h.qa, h.qloc, h.qal, FL.own hcr h.fl rd⟩

-- (moved from DrsC5R)
/-- `addTo`'s entry -/
abbrev addToC : Nat := 0x5e62c0

-- (moved from DrsC5R)
/-- the return address of the correction loop's `CALL addTo` -/
abbrev rA : Nat := 0x5efd85

-- (moved from DrsC5R)
/-- the return address of the correction loop's `CALL subVW(qhatv[s:], …)` -/
abbrev rW2 : Nat := 0x5eff0b

-- (moved from DrsC5R)
/-- the model after `qhat--` and `qhatv -= v[:s]` (with the borrow into `qhatv[s:]`) -/
@[reducible] def stC (V : List Nat) (s0 ql : Nat) (stb : Mdl.St) : Mdl.St :=
  { stQ stb with buf := Mdl.corrSub stb.buf (V.take s0) s0 ql }

-- (moved from DrsC5R)
theorem stC_le {V : List Nat} {s0 ql : Nat} {stb : Mdl.St} (h : ¬ s0 < ql) :
    stV V s0 (stQ stb) = stC V s0 ql stb := by
  simp only [stC, stV, stQ, Mdl.corrSub, if_neg h]

-- (moved from DrsC5R)
theorem bvA {u j : Nat} (hj : j ≤ u) (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u - BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (u - j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

-- (moved from DrsC5R)
theorem bvM {q k x : Nat} (hx0 : 0 < x) (hx : x < 2 ^ 63) (hk : k < 2 ^ 64) (hq : q + k < 2 ^ 64) :
    BitVec.ofNat 64 q + ((0#64 - BitVec.ofNat 64 x).sshiftRight 63 &&& BitVec.ofNat 64 k) = BitVec.ofNat 64 (q + k) := by
  rw [FvModexp.sshr63_allOnes _ (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega), BitVec.allOnes_and]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

-- (moved from DrsC5R)
theorem toInt_small {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]
  rw [if_pos (by omega)]; congr 1; omega

-- (moved from DrsC5R)
theorem P_len_le {c : Cx} {s : State} {j : Nat} {U : List Nat} (h2v : 2 ≤ c.vl) : (c.P s j U).length ≤ 3 * c.vl := by
  have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.q0 s j U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
    ((c.q0 s j U).length + ((c.V s).take (c.vl / 2 - 1)).length))
  rw [Mdl.length_toL, List.length_take] at h1
  have h2 := q0_len (c := c) (s := s) (j := j) (U := U)
  have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
  show (Mdl.norm _).length ≤ _
  rw [List.length_take]
  omega

-- (moved from DrsC5)
theorem subVVc_le1 : ∀ (x y : List Nat) (c : Nat), c ≤ 1 → (Mdl.subVVc x y c).2 ≤ 1
  | x :: xs, y :: ys, c, _ => by
    simp only [Mdl.subVVc]
    exact subVVc_le1 xs ys _ (by show (if x < y + c then 1 else 0) ≤ 1; split <;> omega)
  | [], _, c, h => by simp only [Mdl.subVVc]; exact h
  | _ :: _, [], c, h => by simp only [Mdl.subVVc]; exact h

-- (moved from DrsC6)
theorem addTo_entryD : segAddr Extracted.program AddTo.fn = addToC := by decide

-- (moved from DrsC6)
/-- `addTo` as a summary in `LibDrs.program` -/
theorem atSum (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Summary (LibDrs.program.link impl) addToC
      (fun s => RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) (s.mem.readLE (s.regs regSP).toNat 8) ∧
        s.xmm xmmZero = 0 ∧ ArgsFrom64 s 0 [zp, zl, zc, xp, xl, xc] ∧ s.df = false ∧
        (CallEnv R L s 4232 48 ∧ xl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat < 2 ^ 40 ∧
          NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4232 48) ∧ zc.toNat < 2 ^ 63 ∧
          s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
          Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4232 48) ∧
          (0 < xl.toNat → Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * xl.toNat)) ∧
          Apart zp.toNat (8 * zl.toNat) ((s.regs 14).toNat + 16) 8 ∧ Apart zp.toNat (8 * zl.toNat) (s.fsBase.toNat - 8) 8 ∧
          R.inv b L (s.regs 14).toNat (view R.rt L s.mem)))
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
        (s'.fsBase = s.fsBase ∧ s'.df = s.df ∧ natVal s'.mem zp.toNat zl.toNat =
          (natVal s.mem zp.toNat zl.toNat + natVal s.mem xp.toNat xl.toNat) % 2 ^ (64 * zl.toNat) ∧
        ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
          R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
          MemFrame s.mem s'.mem (R.rt ++ win s 4232 48 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
          LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)])) := by
  have hS := Ensures.toSummaryIn (AddTo.ens impl hap R hmv b L zp zl zc xp xl xc)
    (A64.noExit_restrict64 hap AddTo.names) (by simp [numIntRegs])
    (A64.codeIn_restrict_mono64 hap (IntAS.sub_of_all (ms := LibDrs.names) (by decide)))
  rw [← LibDrs.eq_only, addTo_entryD] at hS
  exact hS

-- (moved from DrsC6)
theorem ws_up0 {c : Cx} {s : State} {x k p n : Nat} (h : Outside x k (c.ws s)) (h1 : c.up ≤ p)
    (h2 : p + n ≤ c.up + 8 * c.ul) : Outside x k [(p, p + n)] := by
  simp only [Cx.ws, outside_append, outside_cons] at h
  simp only [outside_cons, outside_nil, and_true]; omega

-- (moved from DrsC6)
theorem ws_up {c : Cx} {s : State} {rs : List (Nat × Nat)} {x k p n : Nat} (h : Outside x k (rs ++ c.ws s))
    (h1 : c.up ≤ p) (h2 : p + n ≤ c.up + 8 * c.ul) : Outside x k [(p, p + n)] :=
  ws_up0 ((outside_append _ _ _ _).mp h).2 h1 h2

-- (moved from DrsD1)
/-- the return address of the `nat.cmp` after the correction loop -/
abbrev rD2 : Nat := 0x5eff71

-- (moved from DrsD3)
/-- the return address of the `subVV.abi0` after the correction loop -/
abbrev rD4 : Nat := 0x5effd9

-- (moved from DrsD3)
/-- `|P| ≤ 2B ≤ n` -/
theorem P_len_le2 {c : Cx} {s : State} {j : Nat} {U : List Nat} (hB : 1 ≤ c.vl / 2) :
    (c.P s j U).length ≤ 2 * (c.vl / 2) := by
  have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.q0 s j U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
    ((c.q0 s j U).length + ((c.V s).take (c.vl / 2 - 1)).length))
  rw [Mdl.length_toL, List.length_take] at h1
  have h2 := q0_len (c := c) (s := s) (j := j) (U := U)
  have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
  show (Mdl.norm _).length ≤ _
  rw [List.length_take]
  omega

-- (moved from DrsD4)
/-- the model after `uu[:ql] -= qhatv[:ql]` -/
@[reducible] def stS (ql : Nat) (st : Mdl.St) : Mdl.St :=
  { st with w := (Mdl.subVV (st.w.take ql) (st.buf.take ql)).1 ++ st.w.drop ql }

-- (moved from DrsD4)
/-- the pc after the re-entry sequence of the second `subVV.abi0` call -/
abbrev rD5 : Nat := 0x5effe6

-- (moved from DrsD5R)
/-- the join after `subVW(uu[ql:], uu[ql:], 1)` (natdiv.go:851) -/
abbrev rJ6 : Nat := 0x5f003f

-- (moved from DrsD5R)
theorem bvS2 {a u : Nat} (h : a ≤ u) (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u - BitVec.ofNat 64 a = BitVec.ofNat 64 (u - a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

-- (moved from DrsD5R)
theorem bvM2 {q a x : Nat} (h : a < x) (hx : x < 2 ^ 63) (hq : q + 8 * a < 2 ^ 64) :
    BitVec.ofNat 64 q + ((0#64 - BitVec.ofNat 64 (x - a)).sshiftRight 63 &&& BitVec.ofNat 64 a <<< 3) =
      BitVec.ofNat 64 (q + 8 * a) := by
  have hsh : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft]; simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
  rw [hsh]
  exact bvM (by omega) (by omega) (by omega) (by omega)

-- (moved from DrsD5)
theorem upd_app_full (A D X : List Nat) (h : X.length = D.length) : Mdl.upd (A ++ D) A.length X = A ++ X := by
  unfold Mdl.upd
  rw [List.take_left, List.drop_eq_nil_of_le (by simp; omega)]; simp

-- (moved from DrsD6)
theorem ws_qp0 {c : Cx} {s : State} {x k p n : Nat} (h : Outside x k (c.ws s)) (h1 : c.qp ≤ p)
    (h2 : p + n ≤ c.qp + 8 * c.ql) : Outside x k [(p, p + n)] := by
  simp only [Cx.ws, outside_append, outside_cons] at h
  simp only [outside_cons, outside_nil, and_true]; omega

-- (moved from DrsD6)
theorem ws_qp {c : Cx} {s : State} {rs : List (Nat × Nat)} {x k p n : Nat} (h : Outside x k (rs ++ c.ws s))
    (h1 : c.qp ≤ p) (h2 : p + n ≤ c.qp + 8 * c.ql) : Outside x k [(p, p + n)] :=
  ws_qp0 ((outside_append _ _ _ _).mp h).2 h1 h2

-- (moved from DrsFC1)
/-- the return address of the final loop's `nat.cmp` -/
abbrev rFC1 : Nat := 0x5f03bc

-- (moved from DrsFC2B)
/-- `subVW(qhat, qhat, 1)`'s return address (final loop) -/
abbrev rFW1 : Nat := 0x5f03f5

-- (moved from DrsFC4R)
/-- `subVV.abi0`'s return address (final loop) -/
abbrev rFV1 : Nat := 0x5f0457

-- (moved from DrsFC4)
/-- the pc after the re-entry sequence of the final loop's `subVV.abi0` call -/
abbrev rFV2 : Nat := 0x5f0464

-- (moved from DrsFC4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `McF` across the argument stores (`isA`) -/
theorem McF.ownA {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : McF R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (isA s))
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
    simp only [fw, win, isA, outside_cons, outside_nil, and_true] at ho ⊢; omega
  have rd : ∀ x n, Outside x n (win s c.W 96) → M'.readLE x n = M.readLE x n := fun x n ho =>
    hF3.readLE _ _ (by simp only [win, isA, outside_cons, outside_nil, and_true] at ho ⊢; omega)
  have ht0 := hcr.t0w
  have hrw := h.rg.w
  have rt : ∀ x n, c.t0 ≤ x → x + n ≤ c.t0 + 8 * (c.vl / 2 + 1) → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (ht0.of_sub h1 h2)
  have ru : ∀ x n, c.up ≤ x → x + n ≤ c.up + 8 * c.ul → M'.readLE x n = M.readLE x n :=
    fun x n h1 h2 => rd _ _ (huw.of_sub h1 h2)
  have hql : (c.qF s U).length ≤ c.vl / 2 + 1 := qF_len
  refine ⟨hcr, Ev.own hcr h.ev hF hreg, Fp.own hcr h.fp hF,
    h.bd.frame hF3 (by simp only [FixOut, isA, outside_cons, outside_nil, and_true]; omega)
      (by simp only [FOut, isA, outside_cons, outside_nil, and_true]; omega) (rd _ _ hvw)
      (rd _ _ (huw.of_sub (by omega) (by omega))) (rd _ _ hqw), h.jB, h.li,
    ⟨by rw [hF3.readLE _ _ (by simp only [isA, outside_cons, outside_nil, and_true]; omega)]; exact h.q3.s200⟩,
    h.rg, by rw [limbs_congr (rt _ _ (Nat.le_refl _) (by omega))]; exact h.qk,
    by rw [limbs_congr (rd _ _ hrw)]; exact h.bf,
    by rw [limbs_congr (ru _ _ (Nat.le_refl _) (by omega))]; exact h.wk, bud_cap (Cr.capOwn hcr hF) h.bud,
    by rw [hF3.accessible]; exact h.qa, h.qloc, h.qal, FL.own hcr h.fl rd⟩

-- (moved from DrsFC5R)
/-- the return address of the final loop's `CALL addTo` -/
abbrev rFA : Nat := 0x5f0505

-- (moved from DrsFC5R)
/-- the return address of the final loop's `CALL subVW(qhatv[s:], …)` (= the join) -/
abbrev rFW2 : Nat := 0x5f04d1

-- (moved from DrsFC5R)
theorem PF_len_le {c : Cx} {s : State} {U : List Nat} (h2v : 2 ≤ c.vl) : (c.PF s U).length ≤ 3 * c.vl := by
  have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.qF s U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
    ((c.qF s U).length + ((c.V s).take (c.vl / 2 - 1)).length))
  rw [Mdl.length_toL, List.length_take] at h1
  have h2 := qF_len (c := c) (s := s) (U := U)
  have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
  show (Mdl.norm _).length ≤ _
  rw [List.length_take]
  omega

-- (moved from DrsFD1)
/-- the return address of the `nat.cmp` after the final correction loop -/
abbrev rFD2 : Nat := 0x5f0554

-- (moved from DrsFD3)
/-- the return address of the `subVV.abi0` after the correction loop -/
abbrev rFD4 : Nat := 0x5f05bf

-- (moved from DrsFD3)
/-- `|P| ≤ 2B ≤ n` -/
theorem PF_len_le2 {c : Cx} {s : State} {U : List Nat} (hB : 1 ≤ c.vl / 2) :
    (c.PF s U).length ≤ 2 * (c.vl / 2) := by
  have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.qF s U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
    ((c.qF s U).length + ((c.V s).take (c.vl / 2 - 1)).length))
  rw [Mdl.length_toL, List.length_take] at h1
  have h2 := qF_len (c := c) (s := s) (U := U)
  have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
  show (Mdl.norm _).length ≤ _
  rw [List.length_take]
  omega

-- (moved from DrsFD4)
/-- the pc after the re-entry sequence of the second `subVV.abi0` call -/
abbrev rFD5 : Nat := 0x5f05cc

-- (moved from DrsFD5R)
/-- after the `if c > 0 { panic }` test (natdiv.go:886-887): `0x5f0630` -/
abbrev rJF6 : Nat := 0x5f0630

-- (moved from DrsFD5R)
/-- the return address of the final block's `subVW(u[ql:], u[ql:], 1)` (`MOVQ AX, R9`) -/
abbrev rFD5W : Nat := 0x5f0628

-- (moved from DrsFD5)
/-- the model state after `u -= qhatv` (with the borrow) at the end of the final block -/
@[reducible] def Cx.sGF (c : Cx) (s : State) (U : List Nat) : Mdl.St := { c.sFF s U with w := (c.sTF s U).1 }

-- (moved from DrsFD6R)
/-- the return address of `addTo(z, qhat.norm())` -/
abbrev rFD6 : Nat := 0x5f0685

-- (moved from DrsC1)
@[reducible] def Cx.uuC (c : Cx) (j : Nat) : Nat := c.uc - (j - c.vl / 2)

-- (moved from DrsD4)
/-- `2·B ≤ len uu` -/
theorem uuL_ge {c : Cx} {j : Nat} (h : j ≤ c.u1 - c.vl) (hv : c.vl ≤ c.u1) : 2 * (c.vl / 2) ≤ c.uuL j := by
  simp only [Cx.uuL]; omega

end FvModexp.Amd64.Q.DivRec
