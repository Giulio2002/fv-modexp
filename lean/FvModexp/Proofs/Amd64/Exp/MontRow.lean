import FvModexp.Proofs.Amd64.Exp.Mont
import FvModexp.Proofs.Amd64.Nat.RowLink
import FvModexp.Proofs.Amd64.Witness.Sites
import FvModexp.Proofs.Amd64.Witness.Stubs

set_option autoImplicit false

/-!
# Row: `nat.montgomery` (amd64) on the Run extraction — the twin of Arm64/Exp/MontRow.lean (agent divmc s83)

`correctness` = `Mont.ens` moved to `Extracted.program.link impl` (`Ensures.full64`). It is a release row of its own,
run right before `amd64 Exp/W4Row`, so the montgomery closure (MontLoop/Mont/MontExit/…, ~200 module-s, on window-4's
critical import path) is compiled and replayed by this row instead of by window-4 (docs/PERF.md "divmc s83").
`Witness.nonvacuous`: the shared witness runtime, `montgomery(z, x, y, m, k, n)` with `x = 3`, `y = 5`, `m = 7`,
`k = 0`, `n = 1`, `len z = cap z = 2`; `m`, `len m`, `cap m`, `k`, `n` are the stack arguments at `RSP + 8 …`;
the `math/big.hasADX` byte in memory; one call-site state per runtime contract.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Amd64.MontRow

/-- **`nat.montgomery`** (amd64): `z.montgomery(x, y, m, k, n)` with `len x = len y = len m = n > 0`, `cap z ≥ 2n`
stores `montgomery n x y m k` in `z[0:n]` and returns `z[0:n]`; writes only `z[0:cap]`, the runtime's memory and the
window; `fsBase` and `DF` kept. -/
theorem correctness (impl : List Amd64.Segment) (hap : Amd64.ImplApart Extracted.program impl) (R : RtInv)
    (hclr : MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc yp yl yc : BitVec 64) (mp ml mc k n : Nat) :
    Ensures (Extracted.program.link impl) (segAddr Extracted.program MontHyp.fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc]
      (Mont.Pre R b L zp zc xp xl yp yl mp ml mc k n) (Mont.Post R b L zp zc xp yp mp k n) :=
  Ensures.full64 hap (by simp [numIntRegs]) (Mont.ens impl hap R hclr hmv b L zp zl zc xp xl xc yp yl yc mp ml mc k n)

end FvModexp.Amd64.MontRow

namespace FvModexp.Amd64.MontRow.Witness

open FvModexp.Amd64.AsmWit Janus.Contracts.Toy

set_option maxRecDepth 100000

abbrev XP : Nat := OB
abbrev YP : Nat := OB + 8
abbrev MP : Nat := OB + 16

/-- `x = 3`, `y = 5`, `m = 7`; the stack arguments `mp = OB + 16` (`[SP0 + 8]`), `len m = cap m = 1`, `k = 0`, `n = 1`
(`[SP0 + 16 … SP0 + 48)`); all other witness bytes 0 (the return address `RET` at `SP0` comes from `toyBytes`) -/
def g (a : Nat) : Byte :=
  if a = XP then 3 else if a = YP then 5 else if a = MP then 7
  else if a = SP0 + 8 then 0x10 else if a = SP0 + 10 then 0xE0
  else if a = SP0 + 16 then 1 else if a = SP0 + 24 then 1 else if a = SP0 + 40 then 1 else 0

/-- the standard regions plus the `math/big.hasADX` byte -/
def regs : List Janus.Arm64.Region := stdRegs ++ [⟨MontHyp.hasADX, 1, false⟩]

abbrev mem0 : Janus.Arm64.Memory := wmem (toyBytes g) regs

def args : List (BitVec 64) :=
  [BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 XP, 1, 1, BitVec.ofNat 64 YP, 1, 1]

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 OA else if i = 3 then 2 else if i = 1 then 2
      else if i = 7 then BitVec.ofNat 64 XP else if i = 6 then 1 else if i = 8 then 1
      else if i = 9 then BitVec.ofNat 64 YP else if i = 10 then 1 else if i = 11 then 1
      else if i = 4 then BitVec.ofNat 64 SP0 else if i = 14 then BitVec.ofNat 64 G0 else 0,
    rip := BitVec.ofNat 64 (segAddr Extracted.program MontHyp.fn), flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0, fsBase := BitVec.ofNat 64 (T0 + 8) }

theorem hret : RetAddr (Extracted.program.link WStubs.impl) RET := RetAddr.of_check (by decide +kernel)

theorem setup : CallSetup ((Extracted.program.link WStubs.impl).withExit RET) (segAddr Extracted.program MontHyp.fn)
    args s0 :=
  ⟨rfl, by decide +kernel, rfl, by decide, by
    intro i h; simp only [args, List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem acc0 (a n : Nat) (w : Bool) :
    mem0.accessible a n w = (wmem (fun _ => 0) regs).accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem bump : mem0.readLE BUMP 8 = HEAP := by decide +kernel

theorem inv1 (gp : Nat) : R.inv 0x1000 [] gp (view R.rt [] mem0) := by
  refine toyInv_init_live (m := mem0) (g := gp) (p0 := HEAP) (by decide) (Nat.le_refl _)
    (by decide) (by intro r hr; simp at hr) bump (fun i hi hi' => ?_) (by rw [acc0]; decide +kernel)
    (by rw [acc0]; decide +kernel) (by rw [acc0]; decide +kernel)
  show wbytes (toyBytes g) i = 0
  rw [wbytes_high _ (by simp only [HEAP] at hi; omega)]
  unfold toyBytes
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [T0, HEAP] at *; omega),
    if_neg (by simp only [SP0, HEAP] at *; omega)]
  rw [if_neg (show ¬ i < HEAP from Nat.not_lt.mpr hi)]

theorem sg0 : StackGuardOK s0 4288 :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel⟩

theorem tls0 : TlsG s0 :=
  ⟨by decide, by show mem0.accessible _ 8 false = true; rw [acc0]; decide +kernel, by decide +kernel⟩

theorem pre : Mont.Pre R 0x1000 [] (BitVec.ofNat 64 OA) 2 (BitVec.ofNat 64 XP) 1 (BitVec.ofNat 64 YP) 1 MP 1 1 0 1
    s0 := by
  have hm : s0.mem = mem0 := rfl
  unfold Mont.Pre Mont.Env Mont.Input
  refine ⟨⟨sg0, ?_⟩, ?_⟩
  all_goals try rw [hm]
  repeat' (first | exact tls0 | apply And.intro)
  all_goals first
    | exact inv1 _
    | trivial
    | (intro r hr; simp at hr)
    | (right; rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide +kernel)
    | (simp only [Apart]; decide +kernel)
    | (rw [acc0]; decide +kernel)
    | decide +kernel

/-- Every hypothesis of `correctness` and every conjunct of its precondition hold together: the shared witness runtime,
budget `0x1000`, empty live set, `montgomery(z, x, y, m, 0, 1)` with `x = 3`, `y = 5`, `m = 7`, `len z = cap z = 2`;
one call-site state per runtime contract. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (zp zl zc xp xl xc yp yl yc : BitVec 64) (mp ml mc k n : Nat) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    MemclrNoHeapPointersLive64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") 4096 R ∧
    MemmoveLive64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) (segAddr Extracted.program MontHyp.fn)
      [zp, zl, zc, xp, xl, xc, yp, yl, yc] s ∧
    Mont.Pre R b L zp zc xp xl yp yl mp ml mc k n s ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") ∧
      clSite R (Extracted.program.contractAddr "runtime.memclrNoHeapPointers") L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧
      mvSite R (Extracted.program.contractAddr "runtime.memmove") L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' =>
      ABIReturn s s' ∧ Mont.Post R b L zp zc xp yp mp k n s s' :=
  ⟨WStubs.impl, R, 0x1000, [], BitVec.ofNat 64 OA, 2, 2, BitVec.ofNat 64 XP, 1, 1, BitVec.ofNat 64 YP, 1, 1,
    MP, 1, 1, 0, 1, RET, s0, WStubs.hap, by rw [WStubs.addr_cl]; exact WStubs.cl R,
    by rw [WStubs.addr_mv]; exact WStubs.mv R, hret, setup, pre,
    ⟨[], 0x1000, callS WStubs.clA OA 8 0, by rw [WStubs.addr_cl]; rfl, by rw [WStubs.addr_cl]; exact site_cl _⟩,
    ⟨[], 0x1000, callS WStubs.mvA OA OB 8, by rw [WStubs.addr_mv]; rfl, by rw [WStubs.addr_mv]; exact site_mv _⟩,
    correctness WStubs.impl WStubs.hap R (by rw [WStubs.addr_cl]; exact WStubs.cl R) (by rw [WStubs.addr_mv]; exact WStubs.mv R)
      0x1000 [] (BitVec.ofNat 64 OA) 2 2 (BitVec.ofNat 64 XP) 1 1 (BitVec.ofNat 64 YP) 1 1 MP 1 1 0 1 RET hret s0 setup
      pre⟩

end FvModexp.Amd64.MontRow.Witness
