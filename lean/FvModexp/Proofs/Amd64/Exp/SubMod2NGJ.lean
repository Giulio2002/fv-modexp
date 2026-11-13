import FvModexp.Proofs.Amd64.Exp.SubMod2NG
import FvModexp.Proofs.Amd64.Exp.SubMod2NSeg2
import FvModexp.Proofs.Amd64.Nat.NatSub0

set_option autoImplicit false

/-!
# `nat.subMod2N` (amd64), general form: the goal, the join points `J1G … J5G`, the `nat.sub` premise with empty-tolerant
operands, and the `LibW` call bridge (agent infra s48; twin of the join layer of Arm64/Exp/SubMod2NG.lean)

Same code split as the amd64 `Pre` chain (Arm64 → amd64 addresses: `J1` `+0x157`, `J2` `+0x246`, `J3` `+0x2ac`,
`J4` `+0x330`, `J5` `+0x347`), the program is `LibW` (NESTED-PROGRAM RULE), and the joins carry the general facts of
the arm64 G chain: empty `z` / `y` (pointer facts only when non-empty), the current array `(p, c)` of `z` after
`z.sub` (`z`'s own or a fresh runtime one), and the `append` loop's growth count `g` (budget base `b - g · gA n`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.EqHashModel FvModexp

namespace FvModexp.Amd64.SubMod2N

open FvModexp.Amd64.RunIface (Serves)
open FvModexp.Amd64.EvenHyp

/-! ## Calling a project callee from `LibW` -/

/-- an `Ensures` on `(onlySegments ns).link impl` (`ns ⊆ LibW.names`) as a `Summary` of `LibW.program.link impl` -/
theorem hypSumW {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl) {ns : List String}
    (hns : ∀ x, ns.contains x = true → LibW.names.contains x = true) {f : String} {args : List W64}
    {pre : State → Prop} {post : State → State → Prop} (hlen : args.length ≤ numIntRegs)
    (h : Ensures ((Extracted.program.onlySegments ns).link impl) (segAddr Extracted.program f) args pre post) :
    Summary (LibW.program.link impl) (segAddr Extracted.program f)
      (fun s => RetAddr ((Extracted.program.onlySegments ns).link impl) (s.mem.readLE (s.regs 4).toNat 8) ∧
        s.xmm 15 = 0 ∧ ArgsFrom64 s 0 args ∧ s.df = false ∧ pre s)
      (fun s s' => (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15) ∧ post s s') := by
  have hS := Ensures.toSummaryIn h (A64.noExit_restrict64 hap ns) hlen (A64.codeIn_restrict_mono64 hap hns)
  rw [← LibW.eq_only] at hS
  exact hS

theorem subW_names : ∀ x, NatSub.names.contains x = true → LibW.names.contains x = true :=
  sub_of_all (by decide)

theorem addW_names : ∀ x, NatAdd.names.contains x = true → LibW.names.contains x = true :=
  sub_of_all (by decide)

/-! ## `nat.sub` with empty-tolerant operands (divmc's `NatSub.ensR0`) -/

/-- the premise shape of divmc's amd64 `NatSub.ensR0` -/
def SubHypR0 (impl : List Amd64.Segment) (R : RtInv) : Prop :=
  ∀ (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64),
    Ensures ((Extracted.program.onlySegments NatSub.names).link impl) (segAddr Extracted.program NatSub.fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (NatSub.Pre0 R b L zp zc xp xl xc yp yl yc)
      (fun s s' => NatSub.Post R b L zp zc xp xl yp yl s s' ∧
        (xl.toNat ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 1).toNat = zc.toNat) ∧
        (xl.toNat < 2 ^ 39 → (s'.regs 1).toNat < 2 ^ 40))

theorem subHypR0_of (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hmk : MakesliceLiveContract64 (Extracted.program.ofImpl impl) (cA "runtime.makeslice") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R) : SubHypR0 impl R :=
  fun b L zp zl zc xp xl xc yp yl yc => NatSub.ensR0 impl hap R hmk hmv b L zp zl zc xp xl xc yp yl yc

/-! ## The goal and the join points -/

/-- what the function promises (general form), from a state `S` inside its frame (entry state `s`) -/
@[reducible] def GoalG (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc yp yl n : Nat) (s S : State) : Prop :=
  ReachesRet (LibW.program.link impl) (retAddrOf s) S (fun s' =>
    (s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15) ∧
      PostG R b L zp zl zc yp yl n s s')

/-- the current array `(p, c)` of `z` (after `z.sub`, the `append` loop): `z`'s own or a fresh runtime one -/
@[reducible] def CurA (R : RtInv) (L : List (Nat × Nat)) (zp zc p c : Nat) : Prop :=
  (p = zp ∧ c = zc) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)

/-- **J1G** (`+0x157`): `x' = x mod 2^n` in `z`'s array (`RAX..RCX = z`, `RDI, RSI, R8 = x'`, `R9..R11 = y`, `R12 = n`) -/
def J1G (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (l1 : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    PreG R b L op zp zl zc yp yl yc n s →
    S.rip = BitVec.ofNat 64 6216183 → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 3 = BitVec.ofNat 64 zl → S.regs 1 = BitVec.ofNat 64 zc →
    S.regs 7 = BitVec.ofNat 64 zp → S.regs 6 = BitVec.ofNat 64 l1 → S.regs 8 = BitVec.ofNat 64 zc →
    S.regs 9 = BitVec.ofNat 64 yp → S.regs 10 = BitVec.ofNat 64 yl → S.regs 11 = BitVec.ofNat 64 yc →
    S.regs 12 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 1 S.mem L1 b1 →
    natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n → NatNorm S.mem zp l1 → l1 ≤ zc →
    GoalG impl R b L zp zl zc yp yl n s S

/-- **J2G** (`+0x246`): `x'` as at `J1G` (`RDI, RSI, R8`), `y' = y mod 2^n` (`R9..R11`: `y`'s or a fresh array; its
pointer facts only when non-empty); the locals `x'` at `e - 16 / - 40 / - 32` stored -/
def J2G (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (l1 p2 l2 c2 : Nat) (L2 : List (Nat × Nat)) (b2 : Nat),
    PreG R b L op zp zl zc yp yl yc n s →
    S.rip = BitVec.ofNat 64 6216422 → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S →
    S.regs 7 = BitVec.ofNat 64 zp → S.regs 6 = BitVec.ofNat 64 l1 → S.regs 8 = BitVec.ofNat 64 zc →
    S.regs 9 = BitVec.ofNat 64 p2 → S.regs 10 = BitVec.ofNat 64 l2 → S.regs 11 = BitVec.ofNat 64 c2 →
    Fw s S.mem zp zl zc yp n → S.mem.readLE ((s.regs 4).toNat - 16) 8 = zp →
    S.mem.readLE ((s.regs 4).toNat - 40) 8 = l1 → S.mem.readLE ((s.regs 4).toNat - 32) 8 = zc →
    Rt R b L s zp zc n 2 S.mem L2 b2 →
    natVal S.mem zp l1 = natVal s.mem zp zl % 2 ^ n → NatNorm S.mem zp l1 → l1 ≤ W n → l1 ≤ zc →
    natVal S.mem p2 l2 = natVal s.mem yp yl % 2 ^ n → NatNorm S.mem p2 l2 → l2 ≤ W n → l2 ≤ c2 → c2 < 2 ^ 40 →
    p2 < 2 ^ 64 →
    (0 < l2 → S.mem.accessible p2 (8 * l2) false = true ∧ p2 + 8 * l2 ≤ 2 ^ 48 ∧ Held R L2 p2 (8 * l2) ∧
      (p2 + 8 * l2 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 88 ≤ p2) ∧
      (0 < zc → Apart zp (8 * zc) p2 (8 * l2))) →
    GoalG impl R b L zp zl zc yp yl n s S

/-- **J3G** (`+0x2ac`, after `z = z.sub(y', x')` with `x' < y'`): `z = (p3, l3, c3)` (`RAX, RBX, RCX`) holds `y' - x'`,
in `z`'s array or a fresh one -/
def J3G (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (p3 l3 c3 : Nat) (L3 : List (Nat × Nat)) (b3 : Nat),
    PreG R b L op zp zl zc yp yl yc n s →
    S.rip = BitVec.ofNat 64 6216524 → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S →
    S.regs 0 = BitVec.ofNat 64 p3 → S.regs 3 = BitVec.ofNat 64 l3 → S.regs 1 = BitVec.ofNat 64 c3 →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 3 S.mem L3 b3 →
    NatLive S.mem R L3 p3 c3 → CurA R L zp zc p3 c3 → c3 < 2 ^ 40 → p3 < 2 ^ 64 → l3 ≤ c3 →
    (W n ≤ zc → p3 = zp ∧ c3 = zc) →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem p3 l3 = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n → NatNorm S.mem p3 l3 → l3 ≤ W n →
    GoalG impl R b L zp zl zc yp yl n s S

/-- **J4G** (`+0x330`): after `for len(z)*64 < n { z = append(z, 0) }`: `z = (p, ⌈n/64⌉, c)` (`RAX, RSI, RCX`,
`RDX = n`), `g` growths so far (the budget `b - g · gA n` is what the runtime facts are relative to) -/
def J4G (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (p c g : Nat) (L3 : List (Nat × Nat)) (b3 : Nat),
    PreG R b L op zp zl zc yp yl yc n s →
    S.rip = BitVec.ofNat 64 6216656 → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S →
    S.regs 0 = BitVec.ofNat 64 p → S.regs 6 = BitVec.ofNat 64 (W n) → S.regs 1 = BitVec.ofNat 64 c →
    S.regs 2 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R (b - g * gA n) L s zp zc n 3 S.mem L3 b3 →
    NatLive S.mem R L3 p c → CurA R L zp zc p c → c < 2 ^ 40 → p < 2 ^ 64 → W n ≤ c → g ≤ W n →
    (W n ≤ zc → p = zp ∧ c = zc ∧ g = 0) →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem p (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n →
    GoalG impl R b L zp zl zc yp yl n s S

/-- **J5G** (`+0x347`): after `for i := range z { z[i] = ^z[i] }`: value `B^W - 1 - d` -/
def J5G (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (p c g : Nat) (L3 : List (Nat × Nat)) (b3 : Nat),
    PreG R b L op zp zl zc yp yl yc n s →
    S.rip = BitVec.ofNat 64 6216679 → S.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 128) → Abi s S →
    S.regs 0 = BitVec.ofNat 64 p → S.regs 6 = BitVec.ofNat 64 (W n) → S.regs 1 = BitVec.ofNat 64 c →
    S.regs 2 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R (b - g * gA n) L s zp zc n 3 S.mem L3 b3 →
    NatLive S.mem R L3 p c → CurA R L zp zc p c → c < 2 ^ 40 → p < 2 ^ 64 → W n ≤ c → g ≤ W n →
    (W n ≤ zc → p = zp ∧ c = zc ∧ g = 0) →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem p (W n) =
      2 ^ (64 * W n) - 1 - (natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n) →
    GoalG impl R b L zp zl zc yp yl n s S

end FvModexp.Amd64.SubMod2N
