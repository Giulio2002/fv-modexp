import FvModexp.Proofs.Arm64.Conv
import FvModexp.Proofs.Common.SetBytesMath

/-!
# `nat.setBytes` (go-bigmodexpfix copy, arm64): statement pieces

`github.com/ethereum/go-bigmodexpfix/src/math/big.nat.setBytes` (`nat.go:1665`), see `Common/SetBytesMath.lean`.
Frame: 64 bytes (`str x30, [sp, #-0x40]!`), spills `X0`, `X3`, `X4` at `SP+8`, `SP+32`, `SP+40` (`above = 48`),
one runtime call (`makeslice`, 4096 bytes): `stk = 64 + 4096 = 4160`.

Loop heads (offsets in the function): word loop `+0xbc` (`cmp x4, #8`), byte loop `+0x140` (`cmp x4, #0`),
`nat.norm` loop `+0xf8` (`cmp x1, #0`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace FvModexp.Arm64.SetBytes

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.nat.setBytes"
/-- The functions this proof executes: only `fn` (no extracted callee). -/
def names : List String := [fn]
/-- `type:big.Word` (go-bigmodexpfix), the element type `nat.make` passes to `makeslice`. -/
def wordT : Nat := Extracted.dataAddr.«type:big.Word#51b931e8»

abbrev hWord : Nat := segAddr Extracted.program fn + 0xbc
abbrev hByte : Nat := segAddr Extracted.program fn + 0x140
abbrev hNorm : Nat := segAddr Extracted.program fn + 0xf8

/-- The number of limbs: `(len(buf) + 7) / 8`. -/
@[reducible] def nW (bl : BitVec 64) : Nat := (bl.toNat + 7) / 8

/-- The precondition. -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc bp bl : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4160 48 ∧ Outside wordT 16 R.rt ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧ bl.toNat < 2 ^ 40 ∧
    bp.toNat + bl.toNat ≤ 2 ^ 48 ∧ s.mem.accessible bp.toNat bl.toNat false = true ∧
    Held R L bp.toNat bl.toNat ∧ Outside bp.toNat bl.toNat (win s 4160 48) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) bp.toNat bl.toNat) ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4160 48) ∧
      Apart zp.toNat (8 * zc.toNat) ((s.regs 28).toNat + 16) 8) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (zc.toNat < nW bl → R.ok (cA "runtime.makeslice") [wordT, nW bl, makeCap (nW bl)] ∧ makeCost (nW bl) ≤ b)

/-- The postcondition: `z.setBytes(buf)` returns a normalised nat `(p', n', c')` holding the big-endian value of
`buf`, either `z`'s array or a fresh one, with the runtime invariant for the live set with it. -/
def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc bp bl : BitVec 64) (s s' : State) : Prop :=
  ∃ p' n' c' : Nat, (s'.regs 0).toNat = p' ∧ (s'.regs 1).toNat = n' ∧ (s'.regs 2).toNat = c' ∧
    natVal s'.mem p' n' = beVal s.mem bp.toNat bl.toNat ∧ NatNorm s'.mem p' n' ∧ n' ≤ c' ∧ n' ≤ nW bl ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b - makeCost (nW bl) ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ NatLive s'.mem R L' p' c' ∧
      ((p' = zp.toNat ∧ c' = zc.toNat) ∨ (InRanges p' (8 * c') R.rt ∧ ApartAll p' (8 * c') L)) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4160 48 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

/-- What holds at every loop head once the array `[p, p + 8c)` is chosen (`nat.make` done), about the memory `m`
there: the frame record, the buffer unchanged, the array (held, writable, apart from the buffer and the stack
window), the runtime invariant for the live set `L'` and budget `b'`, the frames. -/
def Mid (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc bp bl : BitVec 64) (s : State) (ret p c : Nat)
    (L' : List (Nat × Nat)) (b' : Nat) (m : Memory) : Prop :=
  m.readLE (s.sp.toNat - 64) 8 = ret ∧ m.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat ∧
    (∀ a k, bp.toNat ≤ a → a + k ≤ bp.toNat + bl.toNat → m.readLE a k = s.mem.readLE a k) ∧
    nW bl ≤ c ∧ p % 8 = 0 ∧ p + 8 * c ≤ 2 ^ 48 ∧ m.accessible p (8 * c) true = true ∧
    Apart p (8 * c) bp.toNat bl.toNat ∧ Apart p (8 * c) (s.sp.toNat - 4160) (4160 + 48) ∧
    Held R L' p (8 * c) ∧ LiveExt R L L' ∧ b - makeCost (nW bl) ≤ b' ∧
    R.inv b' L' (s.regs 28).toNat (view R.rt L' m) ∧
    ((p = zp.toNat ∧ c = zc.toNat) ∨ (InRanges p (8 * c) R.rt ∧ ApartAll p (8 * c) L)) ∧
    MemFrame s.mem m (R.rt ++ winA s 4160 48 ++ [(zp.toNat, zp.toNat + 8 * zc.toNat)]) ∧
    LiveFrame s.mem m L [(zp.toNat, zp.toNat + 8 * zc.toNat)]

end FvModexp.Arm64.SetBytes

namespace FvModexp.Arm64.SetBytes

open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

/-- A store of a limb into the array keeps the loop-head facts. -/
theorem Mid.store {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc bp bl : BitVec 64} {s : State}
    {ret p c : Nat} {L' : List (Nat × Nat)} {b' : Nat} {m : Memory}
    (h : Mid R b L zp zc bp bl s ret p c L' b' m) {a : Nat} (v : Nat) (h1 : p ≤ a) (h2 : a + 8 ≤ p + 8 * c) :
    Mid R b L zp zc bp bl s ret p c L' b' (m.writeLE a 8 v) := by
  obtain ⟨hm1, hm2, hbuf, hnc, hp8, hp48, hpacc, hpb, hpw, hpheld, hext, hb', hinv, hor, hfr, hlf⟩ := h
  unfold Apart at hpb hpw
  have hs : 4160 ≤ s.sp.toNat → True := fun _ => trivial
  refine ⟨?_, ?_, ?_, hnc, hp8, hp48, ?_, by unfold Apart; omega, by unfold Apart; omega, hpheld, hext, hb', ?_, hor, ?_, ?_⟩
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hm1
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hm2
  · intro x k hx1 hx2
    by_cases hk : k = 0
    · subst hk; rfl
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact hbuf x k hx1 hx2
  · simpa only [Memory.accessible_writeLE] using hpacc
  · exact inv_store_held hinv (hpheld.sub h1 h2)
  · rcases hor with ⟨rfl, rfl⟩ | ⟨hin, -⟩
    · exact MemFrame.writeLE_inRanges hfr v ⟨(zp.toNat, zp.toNat + 8 * zc.toNat), by simp, h1, h2⟩
    · obtain ⟨r, hr, hr1, hr2⟩ := hin
      exact MemFrame.writeLE_inRanges hfr v ⟨r, by simp [hr], by omega, by omega⟩
  · rcases hor with ⟨rfl, rfl⟩ | ⟨-, hap⟩
    · exact LiveFrame.writeLE_ws hlf v ⟨(zp.toNat, zp.toNat + 8 * zc.toNat), by simp, h1, h2⟩
    · exact LiveFrame.writeLE hlf v (ApartAll.outside (fun r hr => by
        have := hap r hr; unfold Apart at this ⊢; omega))

end FvModexp.Arm64.SetBytes
