import FvModexp.Proofs.Arm64.Exp.ModInvSeg
import FvModexp.Proofs.Common.StkFrame

/-!
# `nat.modularInverseModPowerOfTwo` (arm64): the `n > 64` joins (agent infra)

* `J0` (`+0x6c`) → `JM` (`+0x15c`): spills, the alias test (false: `Pre`'s `Apart z x`), `z = z.make(numWords + 1)`
  (reuse when `cap z ≥ numWords + 1`, else `makeslice(Word, numWords + 1, numWords + 5)`);
* `JM` → the loop head (`+0x3c0`): `zz := nat(nil).make(2·numWords)`, `z.setWord(k0)` (result discarded).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.ModInv

open FvModexp.Arm64.RunIface (Serves)
open FvModexp.Arm64.EvenHyp
open FvModexp.Arm64.ExpHyp (stWs)

/-- the saved LR / FP and the spills written at `J0` (`stk`, `x`, `n`, `k0`, `n + 63`, `numWords`) -/
@[reducible] def Fw1 (s : State) (M : Memory) (st xp xl xc n k : Nat) : Prop :=
  Fw0 s M ∧ M.readLE (s.sp.toNat + 32) 8 = st ∧ M.readLE (s.sp.toNat + 40) 8 = xp ∧
    M.readLE (s.sp.toNat + 48) 8 = xl ∧ M.readLE (s.sp.toNat + 56) 8 = xc ∧ M.readLE (s.sp.toNat + 64) 8 = n ∧
    M.readLE (s.sp.toNat - 40) 8 = n + 63 ∧ M.readLE (s.sp.toNat - 112) 8 = NW n ∧ M.readLE (s.sp.toNat - 88) 8 = k

/-- the runtime-side facts at memory `M` (live set `L1`, invariant at budget `b1`), relative to the entry state:
the writes so far are in the runtime ranges, the window, `z`'s array and the stack object's writable parts; the stack
object is back (`StkOK`, same length, old or fresh array) -/
@[reducible] def RtM (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (s : State) (zp zc st : Nat) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop :=
  M.regions = s.mem.regions ∧ MemFrame s.mem M (R.rt ++ winA s (K kc) A ++ [(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧
    LiveFrame s.mem M L ([(zp, zp + 8 * zc)] ++ stWs s.mem st) ∧ LiveExt R L L1 ∧
    R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M) ∧
    StkOK M R L1 st ∧ stLen M st = stLen s.mem st ∧
    ((stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st) ∨
      (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L))

/-- an array `(p, c)` the function writes from now on: live, the caller's `z` or fresh, outside the window, apart from
`x` and from the stack object -/
@[reducible] def Own (R : RtInv) (kc : Nat) (L L1 : List (Nat × Nat)) (s : State) (zp zc st xp xl : Nat) (M : Memory)
    (p c : Nat) : Prop :=
  c < 2 ^ 40 ∧ p < 2 ^ 64 ∧ NatLive M R L1 p c ∧
    ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
    Outside p (8 * c) (win s (K kc) A) ∧ Apart p (8 * c) ((s.regs 28).toNat + 16) 8 ∧ Apart p (8 * c) xp (8 * xl) ∧
    StkApart M st p (8 * c)

/-- **JM** (`+0x15c`, after `z = z.make(numWords + 1)`): `X0 = z'.ptr`, `X1 = numWords + 1`, `X2 = cap z'`, `X3 … X10` =
`stk, x, n, n + 63, numWords, k0` -/
def JM (impl : List Segment) (R : RtInv) (kc : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  ∀ (S : State) (zp' zc' : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s → 64 < n →
    S.pc = BitVec.ofNat 64 (1797104 + 0x15c) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 240) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 zp' → S.regs 1 = BitVec.ofNat 64 (NW n + 1) → S.regs 2 = BitVec.ofNat 64 zc' →
    S.regs 3 = BitVec.ofNat 64 st → S.regs 4 = BitVec.ofNat 64 xp → S.regs 5 = BitVec.ofNat 64 xl →
    S.regs 6 = BitVec.ofNat 64 xc → S.regs 7 = BitVec.ofNat 64 n → S.regs 8 = BitVec.ofNat 64 (n + 63) →
    S.regs 9 = BitVec.ofNat 64 (NW n) → S.regs 10 = BitVec.ofNat 64 (k0 s xp xl n) →
    Fw1 s S.mem st xp xl xc n (k0 s xp xl n) → RtM R kc L s zp zc st S.mem L1 b1 →
    b - makeCost (NW n + 1) ≤ b1 → Own R kc L L1 s zp zc st xp xl S.mem zp' zc' → NW n + 1 ≤ zc' →
    Goal impl R kc sqrC mulC b L zp zc st xp xl n s S

set_option maxRecDepth 20000 in
/-- after stack-only stores: the runtime facts with the entry live set and budget, and `z` owned -/
theorem rt0 {R : RtInv} {kc : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State} (hkc : 4608 ≤ kc)
    (hpre : Pre R kc sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory}
    (hF : MemFrame s.mem M (winA s (K kc) A)) (hreg : M.regions = s.mem.regions) :
    RtM R kc L s zp zc st M L b ∧ Own R kc L L s zp zc st xp xl M zp zc := by
  have hpre' := hpre
  obtain ⟨⟨-, ⟨hal, -, -, -⟩, -, hout, -, -, hLs, -⟩, -, -, -, -, -, hzp, hzc0, ⟨hzc40, hzlive, hzw⟩, hx0, hxc, -, -,
    -, -, -, hzx, ⟨hst, hstw, -, -⟩, -, hsz, -, -, hinv, -⟩ := hpre'
  have hst' : Outside st 24 (winA s (K kc) A) := by
    simp only [win, winA, outside_cons, outside_nil, and_true] at hstw ⊢; simp only [K] at hstw ⊢; omega
  obtain ⟨hstk, e0, e1, e2⟩ := stkOK_frame hst hF hst' (LiveExt.refl R L)
  refine ⟨⟨hreg, hF.mono fun a k h => ?_, ?_, LiveExt.refl R L, ?_, hstk, e1, Or.inl ⟨e0, e2⟩⟩,
    hzc40, hzp, ?_, Or.inl ⟨rfl, rfl⟩, (hzw hzc0).1, (hzw hzc0).2, (hzx hzc0).mono (Nat.le_refl _) (by omega), ?_⟩
  · simp only [outside_append] at h; exact h.1.1.2
  · refine Expmc.liveFrame_of_frame hF fun a k hin hws => ?_
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, winA, outside_cons, outside_nil, and_true] at this ⊢; omega
  · refine Expmc.inv_frame hF (fun r hr => Or.inr ?_) hinv
    simp only [winA, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [K, A] at hal hout
    rcases hr with rfl | rfl <;> (dsimp only; simp only [K, A]; exact hout.of_sub (by omega) (by omega))
  · intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hzlive hc
    exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · unfold StkApart; rw [e0, e1, e2]; exact hsz

end FvModexp.Arm64.ModInv
