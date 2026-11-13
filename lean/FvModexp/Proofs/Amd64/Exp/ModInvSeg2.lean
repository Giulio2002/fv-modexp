import FvModexp.Proofs.Amd64.Exp.ModInvSeg
import FvModexp.Proofs.Common.StkFrame
import FvModexp.Proofs.Common.ExpmcFrame

set_option autoImplicit false

/-!
# `nat.modularInverseModPowerOfTwo` (amd64): the `n > 64` statements (agent infra s54; twin of `Arm64/Exp/ModInvSeg2`)

* `J0` (`+0x7b`) → `JM` (`+0x1b6`): `numWords`, the alias test (false: `Pre`'s `Apart z x`), the spills, `z =
  z.make(numWords + 1)` (reuse when `cap z ≥ numWords + 1`, else `makeslice(Word, numWords + 1, numWords + 5)`);
* `JM` → the loop head (`+0x4ef`): `zz := nat(nil).make(2·numWords)`, `z.setWord(k0)` (result discarded), `i = 2`.

Frame `RSP' = RSP - 224`; the spills of `J0`: `stk` `0x100(SP') = RSP + 32`, `x` `RSP + 40 … + 56`, `n` `RSP + 64`,
`k0` `0x90(SP') = RSP - 80`, `numWords` `0x78(SP') = RSP - 104`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ModInv

open FvModexp.Amd64.RunIface (Serves Globals)
open FvModexp.Amd64.EvenHyp
open FvModexp.Amd64.Q.NatSqr (StkPre StkSep tls guard)

/-- the return address, the saved `RBP` and the spills written at `J0` (`stk`, `x`, `n`, `k0`, `numWords`) -/
@[reducible] def Fw1 (s : State) (M : Memory) (st xp xl xc n k : Nat) : Prop :=
  Fw0 s M ∧ M.readLE ((s.regs 4).toNat + 32) 8 = st ∧ M.readLE ((s.regs 4).toNat + 40) 8 = xp ∧
    M.readLE ((s.regs 4).toNat + 48) 8 = xl ∧ M.readLE ((s.regs 4).toNat + 56) 8 = xc ∧
    M.readLE ((s.regs 4).toNat + 64) 8 = n ∧ M.readLE ((s.regs 4).toNat - 80) 8 = k ∧
    M.readLE ((s.regs 4).toNat - 104) 8 = NW n

/-- the runtime-side facts at memory `M` (live set `L1`, invariant at budget `b1`), relative to the entry state:
the writes so far are in the runtime ranges, the window, `z`'s array and the stack object's writable parts; the stack
object is back (`StkOK`, same length, old or fresh array, a fresh one in `L1`) -/
@[reducible] def RtM (R : RtInv) (kc : Nat) (L : List (Nat × Nat)) (s : State) (zp zc st : Nat) (M : Memory)
    (L1 : List (Nat × Nat)) (b1 : Nat) : Prop :=
  M.regions = s.mem.regions ∧ MemFrame s.mem M (R.rt ++ win s (K kc) A ++ [(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧
    LiveFrame s.mem M L ([(zp, zp + 8 * zc)] ++ stkWs s.mem st) ∧ LiveExt R L L1 ∧
    R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M) ∧
    StkOK M R L1 st ∧ stLen M st = stLen s.mem st ∧
    ((stW M st = stW s.mem st ∧ stCap M st = stCap s.mem st) ∨
      (InRanges (stW M st) (8 * stCap M st) R.rt ∧ ApartAll (stW M st) (8 * stCap M st) L)) ∧ ArrIn L1 st s.mem M

/-- an owned array other than the caller's `z` is apart from the stack's whole array (`ResSep`) -/
def WA (zp zc st : Nat) (M : Memory) (p c : Nat) : Prop :=
  ¬(p = zp ∧ c = zc) → 0 < c → 0 < stCap M st → Apart p (8 * c) (stW M st) (8 * stCap M st)

/-- an array `(p, c)` the function writes from now on: live, the caller's `z` or fresh, outside the window, apart from
the guard word, the TLS slot, `x` and (`StkSep`) the stack object's header / free part and the threshold globals -/
@[reducible] def Own (R : RtInv) (kc : Nat) (L L1 : List (Nat × Nat)) (s : State) (zp zc st xp xl : Nat) (M : Memory)
    (p c : Nat) : Prop :=
  c < 2 ^ 40 ∧ p < 2 ^ 64 ∧ NatLive M R L1 p c ∧
    ((p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
    Outside p (8 * c) (win s (K kc) A) ∧ Apart p (8 * c) (guard s) 8 ∧ Apart p (8 * c) (tls s) 8 ∧
    Apart p (8 * c) xp (8 * xl) ∧ StkSep M st p (8 * c) ∧ WA zp zc st M p c

/-- **JM** (`+0x1b6`, after `z = z.make(numWords + 1)`): `RAX = z'.ptr`, `RDX = numWords + 1`, `RCX = cap z'`,
`RBX = numWords`, `RDI = stk`, `RSI, R8, R9 = x`, `R10 = n`, `R12 = k0` -/
def JM (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  ∀ (S : State) (zp' zc' : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s → 64 < n →
    S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x1b6) → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224) →
    S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) → Abi s S →
    S.regs 0 = BitVec.ofNat 64 zp' → S.regs 2 = BitVec.ofNat 64 (NW n + 1) → S.regs 1 = BitVec.ofNat 64 zc' →
    S.regs 3 = BitVec.ofNat 64 (NW n) → S.regs 7 = BitVec.ofNat 64 st → S.regs 6 = BitVec.ofNat 64 xp →
    S.regs 8 = BitVec.ofNat 64 xl → S.regs 9 = BitVec.ofNat 64 xc → S.regs 10 = BitVec.ofNat 64 n →
    S.regs 12 = BitVec.ofNat 64 (k0 s xp xl n) →
    Fw1 s S.mem st xp xl xc n (k0 s xp xl n) → RtM R kc L s zp zc st S.mem L1 b1 →
    b - makeCost (NW n + 1) + stkR H S.mem st ≤ b1 → Own R kc L L1 s zp zc st xp xl S.mem zp' zc' → NW n + 1 ≤ zc' →
    Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

/-- **JA** (`+0x154`, `cap z < numWords + 1`: the allocating `make`): `RBX = numWords`, `RDX = numWords + 1`, the
arguments as at `JM`; memory changed in the window only -/
def JA (impl : List Amd64.Segment) (R : RtInv) (kc H : Nat) (sqrC : Nat → Nat) (mulC : Nat → Nat → Nat) (b : Nat)
    (L : List (Nat × Nat)) (zp zl zc st xp xl xc n : Nat) (s : State) : Prop :=
  ∀ S : State, Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s → 64 < n → zc < NW n + 1 →
    S.rip = BitVec.ofNat 64 (0x5ea8c0 + 0x154) → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 224) →
    S.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 8) → Abi s S →
    S.regs 2 = BitVec.ofNat 64 (NW n + 1) → S.regs 3 = BitVec.ofNat 64 (NW n) → S.regs 7 = BitVec.ofNat 64 st →
    S.regs 6 = BitVec.ofNat 64 xp → S.regs 8 = BitVec.ofNat 64 xl → S.regs 9 = BitVec.ofNat 64 xc →
    S.regs 10 = BitVec.ofNat 64 n → S.regs 12 = BitVec.ofNat 64 (k0 s xp xl n) →
    Fw1 s S.mem st xp xl xc n (k0 s xp xl n) → MemFrame s.mem S.mem (win s (K kc) A) →
    S.mem.regions = s.mem.regions → Goal impl R kc H sqrC mulC b L zp zc st xp xl n s S

set_option maxRecDepth 20000 in
/-- after stack-only stores: the runtime facts with the entry live set and budget, and `z` owned -/
theorem rt0 {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory}
    (hF : MemFrame s.mem M (win s (K kc) A)) (hreg : M.regions = s.mem.regions) :
    RtM R kc L s zp zc st M L (b + stkR H s.mem st) ∧ Own R kc L L s zp zc st xp xl M zp zc := by
  have hpre' := hpre
  obtain ⟨⟨-, -, -, -, hout, -, -, hLs, -, -⟩, -, -, -, -, -, hzp, hzc0, ⟨hzc40, hzlive, hzw⟩, hx0, hxc, -, -,
    -, -, -, -, hzx, ⟨-, hst, hstw, -⟩, -, hzs, -, -, hinv, -⟩ := hpre'
  obtain ⟨hstk, e0, e1, e2⟩ := stkOK_frame hst hF hstw (LiveExt.refl R L)
  obtain ⟨hzw1, hzw2, hzw3⟩ := hzw hzc0
  refine ⟨⟨hreg, hF.mono fun a k h => ?_, ?_, LiveExt.refl R L, ?_, hstk, e1, Or.inl ⟨e0, e2⟩,
      fun hn => absurd ⟨e0, e2⟩ hn⟩,
    hzc40, hzp, ?_, Or.inl ⟨rfl, rfl⟩, hzw1, hzw2, hzw3, hzx.mono (Nat.le_refl _) (by omega), ?_,
    fun h => absurd ⟨rfl, rfl⟩ h⟩
  · simp only [outside_append] at h; exact h.1.1.2
  · refine Expmc.liveFrame_of_frame hF fun a k hin _ => ?_
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := hLs r hr
    simp only [win, outside_cons, outside_nil, and_true] at this ⊢; omega
  · refine Expmc.inv_frame hF (fun r hr => Or.inr ?_) hinv
    simp only [win, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    dsimp only
    exact hout.of_sub (by omega) (by omega)
  · intro hc
    obtain ⟨a1, a2, a3, a4⟩ := hzlive hc
    exact ⟨a1, a2, by rw [hF.accessible]; exact a3, a4⟩
  · simp only [StkSep, Q.BasicSqr.freeP, Q.BasicSqr.freeN] at hzs ⊢
    rw [e0, e1, e2]; exact hzs

set_option maxRecDepth 20000 in
/-- stack-only stores keep the stack's capacity (the reserve `stkR H · st` is unchanged) -/
theorem rt0_cap {R : RtInv} {kc : Nat} {H : Nat} {sqrC : Nat → Nat} {mulC : Nat → Nat → Nat} {b : Nat}
    {L : List (Nat × Nat)} {zp zl zc st xp xl xc n : Nat} {s : State}
    (hpre : Pre R kc H sqrC mulC b L zp zl zc st xp xl xc n s) {M : Memory}
    (hF : MemFrame s.mem M (win s (K kc) A)) : stCap M st = stCap s.mem st := by
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, hst, hstw, -⟩, -⟩ := hpre'
  exact (stkOK_frame hst hF hstw (LiveExt.refl R L)).2.2.2

end FvModexp.Amd64.ModInv
