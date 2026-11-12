import FvModexp.Proofs.Arm64.Nat.DrsNorm

/-!
# `divRecursiveStep` (arm64): the prologue (natdiv.go:750) up to the head of `u.norm()`

Frame 400 (`SUB $400, RSP, R20; STP (R29, R30), -8(R20)`): `SP' = SP - 400`, saved `X30` at `SP - 400`, `X29` at
`SP - 408`; spills `z` → `SP + 8`, `u` → `SP + 40`, `v` → `SP + 64`; the defer record pointer `SP - 16` and the defer
bit (byte `SP - 297`) are zeroed. The frame writes stay in `winA s 408 96`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.DivRec

/-- the frame ranges written by `divRecursiveStep` itself -/
@[reducible] def fw (s : State) : List (Nat × Nat) := winA s 408 96

theorem klsr1 (x : BitVec 64) :
    x.rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 = x >>> 1 := by
  ext i hi
  have c1 : ∀ i (h : i < 64), (9223372036854775807#64)[i] = decide (i < 63) := by decide
  have c2 : ∀ i (h : i < 64), (18446744073709551615#64)[i] = true := by decide
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_ushiftRight, c1 i hi, c2 i hi]
  by_cases h : i < 63
  · simp [h]; rw [BitVec.getLsbD_eq_getElem (by omega)]
  · simp [h]; exact BitVec.getLsbD_of_ge x _ (by omega)

/-- `LSR $1` on a word (the janus rotate form) -/
theorem lsr1 (x : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x).rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 = BitVec.ofNat 64 (x / 2) := by
  rw [klsr1]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)]

theorem mf_trans {m₀ m₁ m₂ : Memory} {rs : List (Nat × Nat)} (h₁ : MemFrame m₀ m₁ rs) (h₂ : MemFrame m₁ m₂ rs) :
    MemFrame m₀ m₂ rs :=
  ⟨fun a k ho => by rw [h₂.readLE a k ho, h₁.readLE a k ho],
   fun a n w => by rw [h₂.accessible, h₁.accessible]⟩

/-- the frame facts at every point after the prologue (entry state `s`, current state `S`) -/
structure Fr (s S : State) : Prop where
  sp : S.sp = s.sp - 400#64
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 408#64
  r18 : S.regs 18 = s.regs 18
  reg : S.mem.regions = s.mem.regions
  fr : MemFrame s.mem S.mem (fw s)
  lr : S.mem.readLE (s.sp.toNat - 400) 8 = (s.regs 30).toNat
  fp : S.mem.readLE (s.sp.toNat - 408) 8 = (s.regs 29).toNat

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- entry → the head of `u.norm()`: registers `X0..X10` kept, `z`, `u`, `v` spilled -/
theorem pro0 {R : RtInv} {L : List (Nat × Nat)} (impl : List Segment) (s : State) (W : Nat) (hpc : s.pc = BitVec.ofNat 64 0x1ba3a0)
    (hce : CallEnv R L s W 96) (hW : 408 ≤ W) (Q : State → Prop)
    (k : ∀ P, P.pc = BitVec.ofNat 64 nHead1 → Fr s P → (∀ j, j ≤ 10 → P.regs j = s.regs j) → P.mem.readLE (s.sp.toNat + 8) 8 = (s.regs 0).toNat →
      P.mem.readLE (s.sp.toNat + 40) 8 = (s.regs 4).toNat → P.mem.readLE (s.sp.toNat + 64) 8 = (s.regs 7).toNat →
      P.mem.readLE (s.sp.toNat - 16) 8 = 0 → P.mem.readLE (s.sp.toNat - 297) 1 = 0 →
      ReachesRet (LibDrs.program.link impl) (s.regs 30) P Q) :
    ReachesRet (LibDrs.program.link impl) (s.regs 30) s Q := by
  obtain ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, -, hout, hga, hgr, hLs, -⟩ := hce
  janus_run until [nHead1]
  refine k _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?qF, ?_, ?_⟩ ?qS ?_ ?_ ?_ ?_ ?_
  case qF => unfold fw winA; janus_frame
  case qS => intro j hj; simp only [setReg]; repeat' rw [if_neg (by omega)]
  all_goals try (janus_simp; done)
  all_goals (janus_simp; omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- after `u.norm()` (`R5 = ul'`) → the head of `v.norm()` (bounds check `ul' ≤ uc`) -/
theorem pro1 (impl : List Segment) (r : W64) (P : State) (ul' uc : Nat) (hpc : P.pc = BitVec.ofNat 64 nExit1)
    (h5 : P.regs 5 = BitVec.ofNat 64 ul') (h6 : P.regs 6 = BitVec.ofNat 64 uc) (hle : ul' ≤ uc) (huc : uc < 2 ^ 40)
    (Q : State → Prop)
    (k : ∀ P', P'.pc = BitVec.ofNat 64 nHead2 → P'.mem = P.mem → P'.sp = P.sp → (∀ j, j ≠ 11 → j ≠ 12 → P'.regs j = P.regs j) →
      ReachesRet (LibDrs.program.link impl) r P' Q) :
    ReachesRet (LibDrs.program.link impl) r P Q := by
  janus_run until [nHead2]
  refine k _ rfl rfl rfl ?_
  intro j h1 h2; try simp only [setReg]; repeat' rw [if_neg (by omega)]

theorem natVal_ge (m : Memory) (p n : Nat) (hn : 1 ≤ n) (ht : m.readLE (p + 8 * (n - 1)) 8 ≠ 0) :
    2 ^ (64 * (n - 1)) ≤ natVal m p n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at ht ⊢
  rw [natVal_succ]
  have : 1 ≤ m.readLE (p + 8 * k) 8 := Nat.pos_of_ne_zero ht
  calc 2 ^ (64 * k) = 2 ^ (64 * k) * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ (64 * k) * m.readLE (p + 8 * k) 8 := Nat.mul_le_mul_left _ this
    _ ≤ _ := Nat.le_add_left _ _

theorem natVal_lt (m : Memory) (p n : Nat) : natVal m p n < 2 ^ (64 * n) := by
  unfold natVal
  have := Memory.readLE_lt m p (8 * n)
  rwa [show (256 : Nat) ^ (8 * n) = 2 ^ (64 * n) by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega] at this

/-- the divisor's top word decides `v.norm()`: the normalised length is `vl` -/
theorem norm_v {M : Memory} {vp vl n' : Nat} (h2 : 1 ≤ vl) (htop : 2 ^ 63 ≤ M.readLE (vp + 8 * (vl - 1)) 8)
    (hle : n' ≤ vl) (hv : natVal M vp n' = natVal M vp vl) : n' = vl := by
  refine Nat.le_antisymm hle (Nat.not_lt.1 fun hlt => ?_)
  have h1 := natVal_lt M vp n'
  have h3 := natVal_ge M vp vl h2 (by omega)
  have h4 : 2 ^ (64 * n') ≤ 2 ^ (64 * (vl - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end FvModexp.Arm64.DivRec
