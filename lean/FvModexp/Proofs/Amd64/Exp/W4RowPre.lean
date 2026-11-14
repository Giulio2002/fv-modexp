import FvModexp.Proofs.Amd64.Exp.W4FunP

set_option autoImplicit false

/-!
# window-4 (amd64): the ROW precondition `PreR` (agent divmc s80)

Janus v0.3.3's audit rejects a row precondition containing any memory read whose address mentions `RSP` but is not
literally `(RSP).toNat + k` with a numeral `k ≥ 8` (conservative `[RSP]`-word rule). `ExpW4.PreD` (the summary pre used
by callers) reads the stack arguments as `readLE (sp + 0x390)` with `sp = RSP - 0x388`, which expands to
`readLE (RSP - 0x388 + 0x390)`: refused, although it is the stack argument word `RSP + 8`, not the return address.
`PreR` = `PreD` with those five stack-argument reads written as `readLE ((s.regs 4).toNat + k)` (k = 8, 16, 32, 40, 48);
it says nothing about `[RSP, RSP + 8)`. `preD_of_preR` / `preR_of_preD`: the two are equivalent (`RSP ≥ 0x388` from
`EEnv`'s `RSP = sp + 0x388`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpW4

open FvModexp.Amd64.W4En (EEnv OE XnB free)

/-- `EPreA` without the stack-argument reads -/
def EPreR (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (g fs sp st zp zc xp xl xc yp ylen mp n mc : Nat)
    (s : State) : Prop :=
  EEnv R L g fs sp K s ∧ RunIface.Globals R s.mem [(sp - 8 - K, sp + 0x3f8)] ∧ Outside W4En.wTy 16 R.rt ∧
  s.mem.accessible MontHyp.hasADX 1 false = true ∧
  0 < n ∧ n ≤ 128 ∧ n ≤ mc ∧ mc < 2 ^ 40 ∧
  OE R L sp K st s.mem mp (8 * n) ∧ s.mem.accessible mp (8 * n) false = true ∧ mp + 8 * n ≤ 2 ^ 48 ∧
    NatNorm s.mem mp n ∧
  OE R L sp K st s.mem yp (8 * ylen) ∧ s.mem.accessible yp (8 * ylen) false = true ∧ yp + 8 * ylen ≤ 2 ^ 48 ∧
    NatNorm s.mem yp ylen ∧ 0 < ylen ∧ ylen < 2 ^ 40 ∧
  OE R L sp K st s.mem xp (8 * xc) ∧ s.mem.accessible xp (8 * xc) false = true ∧ xp + 8 * xc ≤ 2 ^ 48 ∧
    NatNorm s.mem xp xl ∧ 0 < xl ∧ xl ≤ 128 ∧ xl ≤ xc ∧ xc < 2 ^ 40 ∧
  zp < 2 ^ 64 ∧ zc < 2 ^ 40 ∧ (2 * n ≤ zc → OE R L sp K st s.mem zp (8 * zc) ∧
    s.mem.accessible zp (8 * zc) true = true ∧ zp + 8 * zc ≤ 2 ^ 48 ∧ zp % 8 = 0 ∧ Apart (g + 16) 8 zp (8 * zc) ∧
    Apart (fs - 8) 8 zp (8 * zc) ∧ Apart zp (8 * zc) mp (8 * n) ∧ Apart zp (8 * zc) yp (8 * ylen)) ∧
  OE R L sp K st s.mem RunIface.gA 32 ∧
  StkOK s.mem R L st ∧ Apart st 24 (sp - 8 - K) (K + 0x400) ∧ Apart st 24 (g + 16) 8 ∧ Apart st 24 (fs - 8) 8 ∧
  (0 < stCap s.mem st → Apart (stW s.mem st) (8 * stCap s.mem st) (sp - 8 - K) (K + 0x400) ∧
    Apart (stW s.mem st) (8 * stCap s.mem st) (g + 16) 8 ∧ Apart (stW s.mem st) (8 * stCap s.mem st) (fs - 8) 8) ∧
  Apart st 24 StackNat.wbA 4 ∧ Apart st 24 (free s.mem st).1 (free s.mem st).2 ∧
  stLen s.mem st + 23 * n + 3 ≤ 2 ^ 16 ∧
  R.inv b L g (view R.rt L s.mem)

/-- the ROW precondition: `PreD` with the stack arguments `y`, `m` read at `RSP + 8 …` -/
def PreR (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (K : Nat) (costF : Nat → Nat → Nat → Nat)
    (costD zp zc st xp xl xc yp ylen mp n mc : Nat) (s : State) : Prop :=
  EPreR R b L K (s.regs 14).toNat s.fsBase.toNat ((s.regs 4).toNat - 0x388) st zp zc xp xl xc yp ylen mp n mc s ∧
  (s.mem.readLE ((s.regs 4).toNat + 8) 8 = yp ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = ylen ∧
    s.mem.readLE ((s.regs 4).toNat + 32) 8 = mp ∧ s.mem.readLE ((s.regs 4).toNat + 40) 8 = n ∧ s.mem.readLE ((s.regs 4).toNat + 48) 8 = mc) ∧
  st ≠ 0 ∧ natVal s.mem mp n % 2 = 1 ∧ 1 < natVal s.mem mp n ∧
  XnB costF n costD (stLen s.mem st + StackNat.rnd (23 * n)) xl (b - stackNatCost (stLen s.mem st) (23 * n)) ∧
  stackNatCost (stLen s.mem st) (23 * n) ≤ b

theorem rowRsp_ge {x : BitVec 64} (h : x = BitVec.ofNat 64 (x.toNat - 0x388 + 0x388)) : 0x388 ≤ x.toNat := by
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat] at h1
  have h2 := x.isLt
  omega

theorem rowO8 {x : Nat} (h : 0x388 ≤ x) : x - 0x388 + 0x390 = x + 8 := by omega
theorem rowO16 {x : Nat} (h : 0x388 ≤ x) : x - 0x388 + 0x398 = x + 16 := by omega
theorem rowO32 {x : Nat} (h : 0x388 ≤ x) : x - 0x388 + 0x3a8 = x + 32 := by omega
theorem rowO40 {x : Nat} (h : 0x388 ≤ x) : x - 0x388 + 0x3b0 = x + 40 := by omega
theorem rowO48 {x : Nat} (h : 0x388 ≤ x) : x - 0x388 + 0x3b8 = x + 48 := by omega

theorem preD_of_preR {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costD zp zc st xp xl xc yp ylen mp n mc : Nat} {s : State}
    (h : PreR R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s) :
    PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a47⟩, ⟨r1, r2, r3, r4, r5⟩, h2⟩ := h
  have hge := rowRsp_ge a1.1
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38,
    by rw [rowO8 hge]; exact r1, by rw [rowO16 hge]; exact r2, by rw [rowO32 hge]; exact r3, by rw [rowO40 hge]; exact r4,
    by rw [rowO48 hge]; exact r5, a47⟩, h2⟩

theorem preR_of_preD {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {K : Nat} {costF : Nat → Nat → Nat → Nat}
    {costD zp zc st xp xl xc yp ylen mp n mc : Nat} {s : State}
    (h : PreD R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s) :
    PreR R b L K costF costD zp zc st xp xl xc yp ylen mp n mc s := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, r1, r2, r3, r4, r5, a47⟩, h2⟩ := h
  have hge := rowRsp_ge a1.1
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a47⟩,
    ⟨by rw [← rowO8 hge]; exact r1, by rw [← rowO16 hge]; exact r2, by rw [← rowO32 hge]; exact r3, by rw [← rowO40 hge]; exact r4,
      by rw [← rowO48 hge]; exact r5⟩, h2⟩

end FvModexp.Amd64.ExpW4
