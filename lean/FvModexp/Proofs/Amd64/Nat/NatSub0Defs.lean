import FvModexp.Proofs.Amd64.Nat.NatSubMid

set_option autoImplicit false

/-!
# `nat.sub` (amd64) with empty-tolerant operands: statement pieces (twin of `FvModexp.Arm64.NatSub` `Pre0`/`PreS0`)

`PreS0` = `PreS` weakened in place (27 conjuncts): `z`'s window fact under `0 < zc`, the operand facts under
`0 < len`, the aliasing facts of slot 14 under `0 < len`. `Pre0` = the compact form (the arm64 `Pre0` shape).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open FvModexp.Amd64.Callees

namespace FvModexp.Amd64.NatSub

def PreS0 (stk : Nat) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64)
    (s : State) : Prop :=
  CallEnv R L s stk 80 ∧ Outside wordT 16 R.rt ∧ yl.toNat ≤ xl.toNat ∧
    natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat xl.toNat ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧
    xc.toNat < 2 ^ 40 ∧ yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s stk 80)) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 14).toNat + 16) 8 ∧
      Apart zp.toNat (8 * zc.toNat) (s.fsBase.toNat - 8) 8 ∧
      (0 < xl.toNat → zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (0 < yl.toNat → zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    (0 < xl.toNat → s.mem.accessible xp.toNat (8 * xl.toNat) false = true) ∧
    (0 < xl.toNat → xp.toNat + 8 * xl.toNat ≤ 2 ^ 48) ∧
    (0 < xl.toNat → Held R L xp.toNat (8 * xl.toNat)) ∧ NatNorm s.mem xp.toNat xl.toNat ∧
    NatNorm s.mem yp.toNat yl.toNat ∧ (0 < xl.toNat → Outside xp.toNat (8 * xl.toNat) (win s stk 80)) ∧
    (0 < yl.toNat → s.mem.accessible yp.toNat (8 * yl.toNat) false = true) ∧
    (0 < yl.toNat → yp.toNat + 8 * yl.toNat ≤ 2 ^ 48) ∧
    (0 < yl.toNat → Held R L yp.toNat (8 * yl.toNat)) ∧ (0 < yl.toNat → Outside yp.toNat (8 * yl.toNat) (win s stk 80)) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

/-- **The empty-tolerant precondition** (compact form). -/
def Pre0 (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zc xp xl xc yp yl yc : BitVec 64) (s : State) : Prop :=
  CallEnv R L s 4288 80 ∧ Outside wordT 16 R.rt ∧ yl.toNat ≤ xl.toNat ∧
    natVal s.mem yp.toNat yl.toNat ≤ natVal s.mem xp.toNat xl.toNat ∧ xl.toNat ≤ xc.toNat ∧ yl.toNat ≤ yc.toNat ∧
    xc.toNat < 2 ^ 40 ∧ yc.toNat < 2 ^ 40 ∧ xl.toNat < 2 ^ 40 ∧ yl.toNat < 2 ^ 40 ∧ zc.toNat < 2 ^ 40 ∧
    NatLive s.mem R L zp.toNat zc.toNat ∧
    (0 < zc.toNat → Outside zp.toNat (8 * zc.toNat) (win s 4288 80)) ∧
    (0 < zc.toNat → Apart zp.toNat (8 * zc.toNat) ((s.regs 14).toNat + 16) 8 ∧
      Apart zp.toNat (8 * zc.toNat) (s.fsBase.toNat - 8) 8 ∧
      (0 < xl.toNat → zp = xp ∨ Apart zp.toNat (8 * zc.toNat) xp.toNat (8 * xl.toNat)) ∧
      (0 < yl.toNat → zp = yp ∨ Apart zp.toNat (8 * zc.toNat) yp.toNat (8 * yl.toNat))) ∧
    (0 < xl.toNat → s.mem.accessible xp.toNat (8 * xl.toNat) false = true ∧ xp.toNat + 8 * xl.toNat ≤ 2 ^ 48 ∧
      Held R L xp.toNat (8 * xl.toNat) ∧ Outside xp.toNat (8 * xl.toNat) (win s 4288 80)) ∧
    NatNorm s.mem xp.toNat xl.toNat ∧ NatNorm s.mem yp.toNat yl.toNat ∧
    (0 < yl.toNat → s.mem.accessible yp.toNat (8 * yl.toNat) false = true ∧ yp.toNat + 8 * yl.toNat ≤ 2 ^ 48 ∧
      Held R L yp.toNat (8 * yl.toNat) ∧ Outside yp.toNat (8 * yl.toNat) (win s 4288 80)) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    (zc.toNat < xl.toNat → R.ok (cA "runtime.makeslice") [wordT, xl.toNat, makeCap xl.toNat] ∧
      makeCost xl.toNat ≤ b) ∧
    (∀ d src k, k ≤ 8 * xl.toNat → R.ok (cA "runtime.memmove") [d, src, k])

theorem Pre0.toS0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    (h : Pre0 R b L zp zc xp xl xc yp yl yc s) : PreS0 4288 R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, fun h => (a15 h).1, fun h => (a15 h).2.1,
    fun h => (a15 h).2.2.1, a16, a17, fun h => (a15 h).2.2.2, fun h => (a18 h).1, fun h => (a18 h).2.1,
    fun h => (a18 h).2.2.1, fun h => (a18 h).2.2.2, a19, a20, a21⟩

theorem Pre.to0 {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    (h : Pre R b L zp zc xp xl xc yp yl yc s) : Pre0 R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, fun _ => a13,
    fun hz => ⟨(a14 hz).1, (a14 hz).2.1, fun _ => (a14 hz).2.2.1, fun _ => (a14 hz).2.2.2⟩,
    fun _ => ⟨a15, a16, a17, a20⟩, a18, a19, fun _ => ⟨a21, a22, a23, a24⟩, a25, a26, a27⟩

theorem PreS0.toS {stk : Nat} {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64}
    {s : State} (h : PreS0 stk R b L zp zc xp xl xc yp yl yc s) (hz : 0 < zc.toNat) (hx : 0 < xl.toNat)
    (hy : 0 < yl.toNat) : PreS stk R b L zp zc xp xl xc yp yl yc s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, a25, a26, a27⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13 hz,
    fun hz' => ⟨(a14 hz').1, (a14 hz').2.1, (a14 hz').2.2.1 hx, (a14 hz').2.2.2 hy⟩, a15 hx, a16 hx, a17 hx, a18, a19,
    a20 hx, a21 hy, a22 hy, a23 hy, a24 hy, a25, a26, a27⟩

theorem preS0_env {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {zp zc xp xl xc yp yl yc : BitVec 64} {s : State}
    (hpre : PreS0 4288 R b L zp zc xp xl xc yp yl yc s) :
    (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
    s.mem.readLE ((s.regs 14).toNat + 16) 8 + 4288 < (s.regs 4).toNat ∧ 4288 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 80 ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - 4288) (4288 + 80) true = true ∧ (s.regs 4).toNat % 8 = 0 ∧ TlsG s := by
  obtain ⟨⟨⟨hg1, hg2, hg3, hg4⟩, ⟨hb', ha, hw⟩, hal, _, _, _, _, _, _, ⟨htg, _, _⟩⟩, _⟩ := hpre
  simp only [stackguard0, stackguard0Offset, regG, regSP] at hg1 hg2 hg3 hb' ha hw
  exact ⟨by omega, hg2, hg3, hb', ha, hw, hal, htg⟩

end FvModexp.Amd64.NatSub
