import FvModexp.Proofs.Amd64.Nat.LibNatAdd
import FvModexp.Proofs.Amd64.Nat.AsmCallees

/-!
# `nat.add` (go-bigmodexpfix nat.go:98), amd64: statement pieces (see the arm64 twin `FvModexp.Arm64.NatAdd`)

Frame: `PUSHQ BP; SUBQ $0x88, SP` (`RSP' = RSP - 144`), spills `AX, DI, SI, R8, R9, R10, R11` at
`RSP + 8, 32, 40, 48, 56, 64, 72` (`above = 80`). Deepest callee in the body (`len y ≤ len x`): `addVW` (`stk 4136`,
called with its `RSP = RSP - 152`): body `stk = 152 + 4136 = 4288`; the self-call adds one frame: `stk = 152 + 4288 = 4440`.
Arguments `z = (AX, BX, CX)`, `x = (DI, SI, R8)`, `y = (R9, R10, R11)`; results `(AX, BX, CX)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.NatAdd

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.add"
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

@[reducible] def mx (xl yl : BitVec 64) : Nat := max xl.toNat yl.toNat

@[reducible] def need (xl yl : BitVec 64) : Nat := if min xl.toNat yl.toNat = 0 then mx xl yl else mx xl yl + 1

def PreS (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64) (s : State) : Prop :=
  CallEnv R L s stk 80 ∧ Outside wordT 16 R.rt ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧ xc.toNat < 2 ^ 40 ∧ yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    Outside zp.toNat (8 * zc.toNat) (win s stk 80) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 14).toNat + 16) 8 ∧
      Apart zp.toNat (8 * zc.toNat) (s.fsBase.toNat - 8) 8 ∧
      (zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * xl.toNat) ∧ NatNorm s.mem xp.toNat xl.toNat ∧ NatNorm s.mem yp.toNat yl.toNat ∧ Outside xp.toNat (8 * xl.toNat) (win s stk 80) ∧
    s.mem.accessible yp.toNat (8 * yl.toNat) false = true ∧ yp.toNat + 8 * yl.toNat ≤ 2 ^ 48 ∧
    Held R L yp.toNat (8 * yl.toNat) ∧ Outside yp.toNat (8 * yl.toNat) (win s stk 80) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    (zc.toNat < need xl yl → R.ok (cA "runtime.makeslice") [wordT, need xl yl, makeCap (need xl yl)] ∧
      makeCost (need xl yl) ≤ b) ∧
    (∀ d src k, k ≤ 8 * mx xl yl → R.ok (cA "runtime.memmove") [d, src, k])

@[reducible] def Pre := PreS 4440

@[reducible] def PostS (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64) (s s' : State) :
    Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 3).toNat = n' ∧ (s'.regs 1).toNat = c' ∧
    natVal s'.mem p' n' = natVal s.mem xp.toNat xl.toNat + natVal s.mem yp.toNat yl.toNat ∧
    NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ mx xl yl + 1 ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost (need xl yl) ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s stk 80 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

@[reducible] def Post := PostS 4440

/-- `PostS` with the facts a caller making a second call needs (infra s5/s6 requests): `z` reused when its capacity
suffices, the result capacity bounded. -/
@[reducible] def PostR (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64)
    (s s' : State) : Prop :=
  PostS stk R b L zp zc xp xl yp yl s s' ∧
    (need xl yl ≤ zc.toNat → (s'.regs 0).toNat = zp.toNat ∧ (s'.regs 1).toNat = zc.toNat) ∧
    (mx xl yl < 2 ^ 39 → (s'.regs 1).toNat < 2 ^ 40)

/-- `PostR` with the exact write set in `z`'s old array: only `z[0:min(max(len x, len y) + 1, cap z)]` (twin of the
arm64 `PostX`; karatsuba(Sqr) temporaries are slices of the result whose capacity reaches beyond what they may write). -/
@[reducible] def PostX (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl yp yl : BitVec 64)
    (s s' : State) : Prop :=
  PostR stk R b L zp zc xp xl yp yl s s' ∧
    MemFrame s.mem s'.mem (R.rt ++ win s stk 80 ++ [(zp.toNat, zp.toNat + 8 * min (max xl.toNat yl.toNat + 1) zc.toNat)]) ∧
    LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * min (max xl.toNat yl.toNat + 1) zc.toNat)]

/-- the exact write set implies `PostS`'s -/
theorem frames_of_x {stk : Nat} {R : RtInv} {L : List (Nat × Nat)} {zp zc xl yl : BitVec 64} {s s' : State}
    (hmf : MemFrame s.mem s'.mem (R.rt ++ win s stk 80 ++ [(zp.toNat, zp.toNat + 8 * min (max xl.toNat yl.toNat + 1) zc.toNat)]))
    (hlf : LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * min (max xl.toNat yl.toNat + 1) zc.toNat)]) :
    MemFrame s.mem s'.mem (R.rt ++ win s stk 80 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)] := by
  have hmo : ∀ a n, Outside a n [(zp.toNat, zp.toNat + 8 * zc.toNat)] →
      Outside a n [(zp.toNat, zp.toNat + 8 * min (max xl.toNat yl.toNat + 1) zc.toNat)] := fun a n ho => by
    simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega
  exact ⟨hmf.mono fun a n ho => by simp only [outside_append] at ho ⊢; exact ⟨ho.1, hmo a n ho.2⟩,
    ⟨fun a n hin ho => hlf.readLE a n hin (hmo a n ho)⟩⟩

end FvModexp.Amd64.NatAdd
