import FvModexp.Proofs.Arm64.Nat.DrsCE
import FvModexp.Proofs.Arm64.Nat.DrsNorm
import FvModexp.Proofs.Arm64.CmpSum
import FvModexp.Proofs.Arm64.Nat.SubVW
import FvModexp.Proofs.Common.DrsCorrVal
import FvModexp.Proofs.Arm64.Nat.AsmCallees
import FvModexp.Proofs.Common.DivBasicMem
import FvModexp.Proofs.Common.MaskWord
import FvModexp.Proofs.Arm64.Nat.AddTo
import FvModexp.Proofs.Arm64.Nat.DrsWs
import FvModexp.Proofs.Arm64.Nat.DrsDV
import FvModexp.Proofs.Arm64.Nat.DrsDG
import FvModexp.Proofs.Arm64.Nat.WinIn
import FvModexp.Proofs.Arm64.Nat.DrsFCE
import FvModexp.Proofs.Arm64.Nat.DrsFV
import FvModexp.Proofs.Arm64.Nat.DrsFG
import FvModexp.Proofs.Arm64.Nat.DrsFin
import FvModexp.Proofs.Arm64.Nat.Restore

set_option autoImplicit false

/-! # arm64 `divRecursiveStep`: shared small definitions and lemmas of the loop / final-iteration segments

ROW-TIME (asm s81, twin of the amd64 `NatQ/DrsSegD`): the return addresses, slot lists, model updates and small
call-instance lemmas that the segment modules `DrsC*`, `DrsD*`, `DrsFC*`, `DrsFD*` share, collected in ONE module that
every segment imports directly, so the segments compile independently (they formed a deep import chain).
Moved verbatim; names unchanged.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel
open Janus Janus.Arm64 Janus.GoABI Janus.GoABI0 Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees
open FvModexp.Arm64.DivLarge (DrsPreW DrsPostW)

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

-- (moved from DrsC1)
/-- `nat.cmp`'s entry -/
abbrev cmpA : Nat := 1782608

/-- the return address of the loop's `nat.cmp` -/
abbrev rC1 : Nat := 0x1ba74c

/-- `uu`'s pointer / length / capacity in iteration `j` -/
@[reducible] def Cx.uuP (c : Cx) (j : Nat) : Nat := c.up + 8 * (j - c.vl / 2)

@[reducible] def Cx.uuL (c : Cx) (j : Nat) : Nat := c.u1 - (j - c.vl / 2)

@[reducible] def Cx.uuC (c : Cx) (j : Nat) : Nat := c.uc - (j - c.vl / 2)

-- (moved from DrsC2)
theorem cmpInt_range (a b : Nat) : Mdl.cmpInt a b = -1 ∨ Mdl.cmpInt a b = 0 ∨ Mdl.cmpInt a b = 1 := by
  unfold Mdl.cmpInt; split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

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

theorem natCmp_range (x y : List Nat) : Mdl.natCmp x y = -1 ∨ Mdl.natCmp x y = 0 ∨ Mdl.natCmp x y = 1 := by
  unfold Mdl.natCmp; split
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
  · exact cmpRev_range _ _

/-- `nat.cmp` (segment 15) in `LibDrs.program` -/
theorem csumD (impl : List Segment) (hap : ImplApart Extracted.program impl) :
    Summary (LibDrs.program.link impl) cmpA CmpSum.Pre CmpSum.Post := by
  have hseg : FvModexp.Lib.CmpA64.program.segments = [Extracted.program.segments[15]'(by decide)] := rfl
  have hc := Callees.codeIn_single (lp := FvModexp.Lib.CmpA64.program) (ns := LibDrs.names) hap hseg
    (List.getElem_mem (l := Extracted.program.segments) (n := 15) (by decide)) (by decide)
  rw [← LibDrs.eq_only] at hc
  exact Summary.of_codeIn hc CmpSum.cmp_summary

theorem lf_winX {L : List (Nat × Nat)} {X : State} {k a : Nat} {m m' : Memory} (ws : List (Nat × Nat))
    (h : MemFrame m m' (winA X k a)) (hs : LiveSep L (win X k a)) : LiveFrame m m' L ws :=
  ⟨fun x n hin _ => h.readLE x n (by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hs r hr
    simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢; omega)⟩

-- (moved from DrsC3)
theorem tN {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- `subVW` as a summary in `LibDrs` -/
theorem vwSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Summary (LibDrs.program.link impl) SubVW.entry
      (fun s => RetAddr ((Extracted.program.onlySegments [SubVW.fn]).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [zp, zl, zc, xp, xl, xc, y] ∧ (xl = zl ∧ SubVW.Pre R b L zp zl zc xp xc s))
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        SubVW.Post R b L zp zl xp y s s') := by
  have h := SubVW.sum impl hap R hmv b L zp zl zc xp xl xc y LibDrs.names (sub_of_all (by decide))
  rw [← LibDrs.eq_only] at h
  exact h

-- (moved from DrsC4R)
/-- `subVV.abi0`'s entry -/
abbrev subVVA : Nat := segAddr Extracted.program subVVfn

/-- the argument words of the `subVV.abi0` call (`SP'+8 … SP'+80`) -/
@[reducible] def isA (s : State) : List (Nat × Nat) := [(s.sp.toNat - 392, s.sp.toNat - 320)]

/-- the nine argument stores read back (`z`, `len z`, `x`, `y`) -/
theorem rd9 (M : Memory) (p a b c d e f g h i : Nat) (hp : 392 ≤ p) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hd : d < 2 ^ 64) (hg : g < 2 ^ 64) :
    let W := ((((((((M.writeLE (p - 392) 8 a).writeLE (p - 384) 8 b).writeLE (p - 376) 8 c).writeLE (p - 368) 8 d).writeLE
      (p - 360) 8 e).writeLE (p - 352) 8 f).writeLE (p - 344) 8 g).writeLE (p - 336) 8 h).writeLE (p - 328) 8 i
    W.readLE (p - 392) 8 = a ∧ W.readLE (p - 384) 8 = b ∧ W.readLE (p - 368) 8 = d ∧ W.readLE (p - 344) 8 = g := by
  intro W
  have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [W]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt ha]
  · simp only [W]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt hb]
  · simp only [W]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt hd]
  · simp only [W]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt hg]

-- (moved from DrsC4)
/-- the model after `qhatv[:s] -= v[:s]` -/
@[reducible] def stV (V : List Nat) (s0 : Nat) (st : Mdl.St) : Mdl.St :=
  { st with buf := (Mdl.subVV (st.buf.take s0) (V.take s0)).1 ++ st.buf.drop s0 }

/-- `subVV.abi0` in `LibDrs` with the runtime invariant carried over -/
theorem svvD (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (b : Nat)
    (L : List (Nat × Nat)) :
    Summary0 (LibDrs.program.link impl) subVVA (VVLPre R b L) (SubVVLQ R b L) := by
  have c : CodeIn ((Extracted.program.onlySegments [subVVfn]).link impl) (LibDrs.program.link impl) := by
    rw [LibDrs.eq_only]; exact codeIn_restrict_mono hap (sub_of_all (by decide))
  exact SubVVHyp.live (Summary.of_codeIn c (subVVHyp impl hap)) R b L

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `Mc` across the argument stores (`isA`) -/
theorem Mc.ownA {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : Mc R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (isA s))
    (hreg : M'.regions = M.regions) : Mc R c s Lk bk M' j Z U qv st := by
  have hcr := h.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hqw, -⟩, ⟨-, -, -, huw, -⟩,
    ⟨-, -, -, hvw, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, -⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame M M' (fw s) := hF3.mono fun x n ho => by
    simp only [fw, winA, isA, outside_cons, outside_nil, and_true] at ho ⊢; omega
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
    by rw [limbs_congr (ru _ _ (Nat.le_refl _) (by omega))]; exact h.lk, h.bud,
    by rw [hF3.accessible]; exact h.qa, h.qloc, h.qal, FL.own hcr h.fl rd⟩

theorem ret0_r (X : State) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (fpsr : BitVec 32) (m : Memory)
    (i : Nat) (hi : i = 18 ∨ i = 28 ∨ i = 29) : (retState0 X junk f v fpsr m).regs i = X.regs i := by
  simp only [retState0, regs0, regPlatform, regG, regFP]
  rw [if_pos hi]

-- (moved from DrsC5R)
/-- `addTo`'s entry -/
abbrev addToA : Nat := 0x1b37f0

/-- the model after `qhat--` and `qhatv -= v[:s]` (with the borrow into `qhatv[s:]`) -/
@[reducible] def stC (V : List Nat) (s0 ql : Nat) (stb : Mdl.St) : Mdl.St :=
  { stQ stb with buf := Mdl.corrSub stb.buf (V.take s0) s0 ql }

theorem stC_le {V : List Nat} {s0 ql : Nat} {stb : Mdl.St} (h : ¬ s0 < ql) :
    stV V s0 (stQ stb) = stC V s0 ql stb := by
  simp only [stC, stV, stQ, Mdl.corrSub, if_neg h]

theorem bvA {u j : Nat} (hj : j ≤ u) (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u - BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (u - j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem bvB {a n : Nat} (h : n / 2 ≤ a) (ha : a < 2 ^ 63) (hn : n < 2 ^ 63) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 n >>> 1 + 1#64 = BitVec.ofNat 64 (a - n / 2 + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem bvC {q k x : Nat} (hx0 : 0 < x) (hx : x < 2 ^ 63) (hk : k < 2 ^ 60) (hq : q + 8 * k < 2 ^ 64) :
    BitVec.ofNat 64 q + (BitVec.ofNat 64 k &&& (0#64 - BitVec.ofNat 64 x).sshiftRight 63) <<< 3 =
      BitVec.ofNat 64 (q + 8 * k) := by
  rw [FvModexp.sshr63_allOnes _ (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega),
    BitVec.and_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem toInt_small {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]
  rw [if_pos (by omega)]; congr 1; omega

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
theorem addToA_eq : segAddr Extracted.program AddTo.fn = addToA := by decide

/-- `addTo` as a summary in `LibDrs` -/
theorem atSum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc : BitVec 64) :
    Summary (LibDrs.program.link impl) addToA
      (fun s => RetAddr ((Extracted.program.onlySegments AddTo.names).link impl) (s.regs 30).toNat ∧
        ArgsFrom s 0 [zp, zl, zc, xp, xl, xc] ∧
        (CallEnv R L s 4240 48 ∧ xl.toNat ≤ zl.toNat ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat < 2 ^ 40 ∧
          NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4240 48) ∧ zc.toNat < 2 ^ 63 ∧
          s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
          Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4240 48) ∧
          (0 < xl.toNat → Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * xl.toNat)) ∧
          Apart zp.toNat (8 * zl.toNat) ((s.regs 28).toNat + 16) 8 ∧
          R.inv b L (s.regs 28).toNat (view R.rt L s.mem)))
      (fun s s' => (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        (natVal s'.mem zp.toNat zl.toNat =
            (natVal s.mem zp.toNat zl.toNat + natVal s.mem xp.toNat xl.toNat) % 2 ^ (64 * zl.toNat) ∧
          ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
            R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
            MemFrame s.mem s'.mem (R.rt ++ winA s 4240 48 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
            LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)])) := by
  have h := Ensures.toSummaryIn (AddTo.ens impl hap R hmv b L zp zl zc xp xl xc) (noExit_restrict hap AddTo.names)
    (codeIn_restrict_mono hap (sub_of_all (ms := LibDrs.names) (by decide)))
  rw [← LibDrs.eq_only, addToA_eq] at h
  exact h

-- (moved from DrsD1)
/-- the return address of the `nat.cmp` after the correction loop -/
abbrev rD2 : Nat := 0x1ba848

-- (moved from DrsD3)
/-- `2·B ≤ len uu` (small context, for the `hqlu` facts of D4/D5) -/
theorem uuL_ge {c : Cx} {j : Nat} (h : j ≤ c.u1 - c.vl) (hv : c.vl ≤ c.u1) : 2 * (c.vl / 2) ≤ c.uuL j := by
  simp only [Cx.uuL]; omega

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
/-- the model after `uu[:ql] -= qhatv` -/
@[reducible] def stS (ql : Nat) (st : Mdl.St) : Mdl.St :=
  { st with w := (Mdl.subVV (st.w.take ql) (st.buf.take ql)).1 ++ st.w.drop ql }

-- (moved from DrsD5R)
/-- the return address of the borrow `subVW` (and the `addTo` preparation) -/
abbrev rD5 : Nat := 0x1ba8d4

-- (moved from DrsD5)
theorem upd_app_full (A D X : List Nat) (h : X.length = D.length) : Mdl.upd (A ++ D) A.length X = A ++ X := by
  unfold Mdl.upd
  rw [List.take_left, List.drop_eq_nil_of_le (by simp; omega)]; simp

-- (moved from DrsD6R)
theorem bvS1 {b u : Nat} (h : b ≤ u) (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u - BitVec.ofNat 64 b = BitVec.ofNat 64 (u - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem bvM1 {q a x : Nat} (h : a < x) (hx : x < 2 ^ 63) (hq : q + 8 * a < 2 ^ 64) :
    BitVec.ofNat 64 q + (BitVec.ofNat 64 a &&& (BitVec.ofNat 64 a - BitVec.ofNat 64 x).sshiftRight 63) <<< 3 =
      BitVec.ofNat 64 (q + 8 * a) := by
  rw [FvModexp.sshr63_allOnes _ (by simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega), BitVec.and_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

-- (moved from DrsFC1)
/-- the return address of the final loop's `nat.cmp` -/
abbrev rFC1 : Nat := 0x1bab08

-- (moved from DrsFC2B)
/-- `subVW(qhat, qhat, 1)`'s return address in the final block -/
abbrev rFW1 : Nat := 0x1bab30

-- (moved from DrsFC4R)
/-- `subVV.abi0`'s return address in the final block -/
abbrev rFVV : Nat := 0x1bab64

-- (moved from DrsFC4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- `Mc` across the argument stores (`isA`) -/
theorem McF.ownA {R : RtInv} {c : Cx} {s : State} {Lk : List (Nat × Nat)} {bk : Nat} {M M' : Memory} {j : Nat}
    {Z U : List Nat} {qv : Nat} {st : Mdl.St} (h : McF R c s Lk bk M j Z U qv st) (hF3 : MemFrame M M' (isA s))
    (hreg : M'.regions = M.regions) : McF R c s Lk bk M' j Z U qv st := by
  have hcr := h.cr
  obtain ⟨hce, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, hqw, -⟩, ⟨-, -, -, huw, -⟩,
    ⟨-, -, -, hvw, -, -, -⟩, -⟩ := hcr.pre
  obtain ⟨-, ⟨-, hb', -, -⟩, -⟩ := hce
  have hWg := drsW_ge c.vl; have hW := hcr.hW; have hu1 := hcr.u1ul
  have hF : MemFrame M M' (fw s) := hF3.mono fun x n ho => by
    simp only [fw, winA, isA, outside_cons, outside_nil, and_true] at ho ⊢; omega
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
    by rw [limbs_congr (ru _ _ (Nat.le_refl _) (by omega))]; exact h.wk, h.bud,
    by rw [hF3.accessible]; exact h.qa, h.qloc, h.qal, FL.own hcr h.fl rd⟩

-- (moved from DrsFC5R)
/-- the `addTo(u[s:], v[s:])` setup of the final correction loop -/
abbrev rFA : Nat := 0x1babb0

theorem PF_len_le {c : Cx} {s : State} {U : List Nat} (h2v : 2 ≤ c.vl) : (c.PF s U).length ≤ 3 * c.vl := by
  have h1 := Mdl.length_norm_le (Mdl.toL (Mdl.val (c.qF s U) * Mdl.val ((c.V s).take (c.vl / 2 - 1)))
    ((c.qF s U).length + ((c.V s).take (c.vl / 2 - 1)).length))
  rw [Mdl.length_toL, List.length_take] at h1
  have h2 := qF_len (c := c) (s := s) (U := U)
  have h3 : min (c.vl / 2 - 1) (c.V s).length ≤ c.vl / 2 - 1 := Nat.min_le_left _ _
  show (Mdl.norm _).length ≤ _
  rw [List.length_take]
  omega

-- (moved from DrsFC5S)
/-- `addTo(u[s:], v[s:])`'s return address in the final block -/
abbrev rFA2 : Nat := 0x1babcc

-- (moved from DrsFD1)
/-- the return address of the `nat.cmp` after the final correction loop -/
abbrev rFD2 : Nat := 0x1bac10

-- (moved from DrsFD3)
/-- the return address of the final `subVV.abi0(u[:ql], u[:ql], qhatv)` -/
abbrev rFD4 : Nat := 0x1bac4c

/-- `|PF| ≤ 2B ≤ n` -/
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

-- (moved from DrsFD5R)
/-- after the final borrow test (`0x1bac98`: `qhat.norm()` for `addTo(z, qhat.norm())`) -/
abbrev rFD5 : Nat := 0x1bac98

/-- `subVW(u[ql:], u[ql:], c)`'s return address -/
abbrev rFD5W : Nat := 0x1bac90

-- (moved from DrsFD5)
/-- the model state after `u -= qhatv` (with the borrow) at the end of the final block -/
@[reducible] def Cx.sGF (c : Cx) (s : State) (U : List Nat) : Mdl.St := { c.sFF s U with w := (c.sTF s U).1 }

-- (moved from DrsFD6R)
/-- the return address of `addTo(z, qhat.norm())` -/
abbrev rFD6 : Nat := 0x1bacdc

end FvModexp.Arm64.DivRec
