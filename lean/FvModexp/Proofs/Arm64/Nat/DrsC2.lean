import FvModexp.Proofs.Arm64.Nat.DrsC1
import FvModexp.Proofs.Arm64.CmpSum

/-!
# `divRecursiveStep` (arm64), correction loop: `e := qhatv.cmp(uu.norm())` (natdiv.go:833)

`c2`: from the `CALL nat.cmp` state of `c1` → `nat.cmp` (`CmpSum.cmp_summary` on `LibDrs`) → its return `0x1ba74c`
with `X0 = cmpQ |P| st` (as `BitVec.ofInt`), `Mc`/`V4`/the slot `i` kept.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Janus.Contracts.EqHashModel

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **the loop's `nat.cmp` call**, from `c1`'s call state -/
theorem c2 (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv) (c : Cx) (s : State)
    (Lk : List (Nat × Nat)) (bk : Nat) (S : State) (j : Nat) (Z U : List Nat) (qv i : Nat) (st : Mdl.St)
    (hC : C R c s Lk bk S j Z U qv i st) (Q : State → Prop)
    (X : State) (n' : Nat) (hpc : X.pc = BitVec.ofNat 64 cmpA) (hsp : X.sp = s.sp - 400#64)
    (h28 : X.regs 28 = s.regs 28) (h29 : X.regs 29 = s.sp - 408#64) (h18 : X.regs 18 = s.regs 18)
    (h30 : X.regs 30 = BitVec.ofNat 64 rC1) (h0 : X.regs 0 = BitVec.ofNat 64 qv)
    (h1 : X.regs 1 = BitVec.ofNat 64 (c.P s j U).length) (h2 : X.regs 2 = BitVec.ofNat 64 (3 * c.vl))
    (h3 : X.regs 3 = BitVec.ofNat 64 (c.uuP j)) (h4 : X.regs 4 = BitVec.ofNat 64 n')
    (hF1 : MemFrame S.mem X.mem (is1 s)) (hreg : X.mem.regions = S.mem.regions)
    (hsi : X.mem.readLE (s.sp.toNat - 160) 8 = i) (hi : i < 2) (hle : n' ≤ c.uuL j)
    (hv : natVal S.mem (c.uuP j) n' = natVal S.mem (c.uuP j) (c.uuL j)) (hN : NatNorm S.mem (c.uuP j) n')
    (k : ∀ T : State, T.pc = BitVec.ofNat 64 rC1 → T.sp = s.sp - 400#64 → T.regs 28 = s.regs 28 →
      T.regs 29 = s.sp - 408#64 → T.regs 18 = s.regs 18 →
      T.regs 0 = BitVec.ofInt 64 (Mdl.cmpQ (c.P s j U).length st) →
      Mc R c s Lk bk T.mem j Z U qv st → V4 c s T.mem qv (c.P s j U).length →
      T.mem.readLE (s.sp.toNat - 160) 8 = i →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) T Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) X Q := by
  sorry

end FvModexp.Arm64.DivRec
