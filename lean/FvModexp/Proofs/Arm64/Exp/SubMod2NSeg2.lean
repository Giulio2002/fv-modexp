import FvModexp.Proofs.Arm64.Exp.SubMod2NCall

/-!
# `nat.subMod2N` (arm64): joins of the `x < y` tail (agent infra)

* `J4` (`+0x28c`): after `for len(z)*64 < n { z = append(z, 0) }`: `len z = ⌈n/64⌉`, value `d = y' - x'`;
* `J5` (`+0x2ac`): after `for i := range z { z[i] = ^z[i] }`: value `B^W - 1 - d`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts FvModexp

namespace FvModexp.Arm64.SubMod2N

def J4 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (L3 : List (Nat × Nat)) (b3 : Nat),
    Pre R b L op zp zl zc yp yl yc n s →
    S.pc = BitVec.ofNat 64 (1805584 + 0x28c) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 (W n) → S.regs 2 = BitVec.ofNat 64 zc →
    S.regs 9 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 3 S.mem L3 b3 →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem zp (W n) = natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n →
    Goal impl R b L zp zl zc yp yl n s S

def J5 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (op zp zl zc yp yl yc n : Nat)
    (s : State) : Prop :=
  ∀ (S : State) (L3 : List (Nat × Nat)) (b3 : Nat),
    Pre R b L op zp zl zc yp yl yc n s →
    S.pc = BitVec.ofNat 64 (1805584 + 0x2ac) → S.sp = BitVec.ofNat 64 (s.sp.toNat - 144) →
    S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 →
    S.regs 0 = BitVec.ofNat 64 zp → S.regs 1 = BitVec.ofNat 64 (W n) → S.regs 2 = BitVec.ofNat 64 zc →
    S.regs 9 = BitVec.ofNat 64 n →
    Fw s S.mem zp zl zc yp n → Rt R b L s zp zc n 3 S.mem L3 b3 →
    natVal s.mem zp zl % 2 ^ n < natVal s.mem yp yl % 2 ^ n →
    natVal S.mem zp (W n) =
      2 ^ (64 * W n) - 1 - (natVal s.mem yp yl % 2 ^ n - natVal s.mem zp zl % 2 ^ n) →
    Goal impl R b L zp zl zc yp yl n s S

set_option maxRecDepth 20000 in
/-- a store into `z`'s array keeps the runtime facts and the frame words -/
theorem rt_zstore {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {op zp zl zc yp yl yc n : Nat} {s : State}
    (hpre : Pre R b L op zp zl zc yp yl yc n s) {M : Memory} {L1 : List (Nat × Nat)} {b1 k : Nat}
    (h : Rt R b L s zp zc n k M L1 b1) {a v : Nat} (h1 : zp ≤ a) (h2 : a + 8 ≤ zp + 8 * zc) :
    Rt R b L s zp zc n k (M.writeLE a 8 v) L1 b1 := by
  have hW := hpre.2.2.2.2.2.2.2.2.2.1
  simp only [W] at hW
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  obtain ⟨-, hzh, -, -⟩ := a7 (by omega)
  refine ⟨by rw [Memory.regions_writeLE]; exact a1, a2.writeLE v (List.mem_append_right _ (List.mem_singleton_self _))
    h1 (by simp only; omega), FvModexp.LiveFrame.writeLE_ws a3 v ⟨(zp, zp + 8 * zc), List.mem_singleton_self _, h1, by omega⟩, a4, a5,
    inv_store_held a6 (hzh.sub h1 (by omega)), fun hc => ?_⟩
  obtain ⟨c1, c2, c3, c4⟩ := a7 hc
  exact ⟨c1, c2, by rw [Memory.accessible_writeLE]; exact c3, c4⟩

end FvModexp.Arm64.SubMod2N
