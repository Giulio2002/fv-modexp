import FvModexp.Proofs.Arm64.Nat.LibSubVW
import FvModexp.Proofs.Arm64.Nat.Callees
import FvModexp.Proofs.Common.AsmVW

/-!
# `math/big.subVW(z, x []Word, y Word) (c Word)` (go-bigmodexpfix arith.go:157, Go ABIInternal, arm64)

```go
func subVW(z, x []Word, y Word) (c Word) {
	if len(x) != len(z) { panic("subVW len") }
	if len(z) == 0 { return y }
	zi, cc := bits.Sub(uint(x[0]), uint(y), 0); z[0] = Word(zi)
	if cc == 0 { if &z[0] != &x[0] { copy(z[1:], x[1:]) }; return 0 }
	for i := 1; i < len(z); i++ {
		xi := x[i]
		if xi != 0 { z[i] = xi - 1; if &z[0] != &x[0] { copy(z[i+1:], x[i+1:]) }; return 0 }
		z[i] = ^Word(0)
	}
	return 1
}
```

The twin of `AddVW` (same frame, same `copy` code); split the same way: `ret0` (`+0x9c`, `+0x13c`), `copy`
(`+0x8c`, `+0x12c`), the borrow loop head `+0xc8` (`fin1`, `body`, `loop`), `ens_lib`, `ens`, `sum`.
Result: `c = y` for `len z = 0` (the `return y`), else the borrow `[x < y]`; `z = (x + B^n - y) mod B^n`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open FvModexp.Arm64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Arm64.SubVW

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.subVW"
def names : List String := [fn]

abbrev entry : Nat := segAddr Extracted.program fn

/-- the precondition (`xl = zl` separately) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xc : BitVec 64) (s : State) : Prop :=
  CallEnvND R L s 4144 40 ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat ≤ xc.toNat ∧ zc.toNat < 2 ^ 63 ∧ xc.toNat < 2 ^ 63 ∧
    NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4144 40) ∧
    (0 < zl.toNat → Apart zp.toNat (8 * zl.toNat) ((s.regs 28).toNat + 16) 8) ∧
    s.mem.accessible xp.toNat (8 * zl.toNat) false = true ∧ xp.toNat + 8 * zl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * zl.toNat) ∧ Outside xp.toNat (8 * zl.toNat) (win s 4144 40) ∧
    (zp = xp ∨ Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * zl.toNat)) ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
    (if zp = xp then True else VWMoves R zp.toNat zl.toNat zc.toNat xp.toNat xc.toNat)

/-- the postcondition -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl xp y : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat =
      (if zl.toNat = 0 then y.toNat else if natVal s.mem xp.toNat zl.toNat < y.toNat then 1 else 0) ∧
    natVal s'.mem zp.toNat zl.toNat =
      (natVal s.mem xp.toNat zl.toNat + 2 ^ (64 * zl.toNat) - y.toNat) % 2 ^ (64 * zl.toNat) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
      R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
      MemFrame s.mem s'.mem (R.rt ++ winA s 4144 40 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)]

/-- a segment-boundary state `S` (inside the frame) against the call state `s`; `k` limbs of `z` written -/
structure Rel (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret zp k : Nat) (s S : State) : Prop where
  sp : S.sp = s.sp - 48#64
  g : S.regs 28 = s.regs 28
  fp : S.regs 29 = s.sp - 56#64
  r18 : S.regs 18 = s.regs 18
  lr : S.mem.readLE (s.sp.toNat - 48) 8 = ret
  sfp : S.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat
  mf : MemFrame s.mem S.mem (R.rt ++ winA s 4144 40 ++ [(zp, zp + 8 * k)])
  lf : LiveFrame s.mem S.mem L [(zp, zp + 8 * k)]
  inv : R.inv b L (s.regs 28).toNat (view R.rt L S.mem)

theorem liveFrame_mono {m m' : Memory} {L ws ws' : List (Nat × Nat)} (h : LiveFrame m m' L ws)
    (hs : ∀ a n, Outside a n ws' → Outside a n ws) : LiveFrame m m' L ws' :=
  ⟨fun a n hin ho => h.readLE a n hin (hs a n ho)⟩

theorem out_z {a n zp k k' : Nat} (hk : k ≤ k') (rt ws : List (Nat × Nat))
    (h : Outside a n (rt ++ ws ++ [(zp, zp + 8 * k')])) : Outside a n (rt ++ ws ++ [(zp, zp + 8 * k)]) := by
  rw [outside_append, outside_append] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  revert h2
  try simp only [outside_cons, outside_nil, and_true]
  omega

set_option maxRecDepth 20000 in
/-- the epilogue returning `0`, from a state whose `z` holds `x - y` (no borrow out) -/
theorem ret0 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (S : State) (k : Nat) (hk : k ≤ zl.toNat) (hz : 0 < zl.toNat)
    (hrel : Rel R b L ret zp.toNat k s S)
    (hpc : S.pc = BitVec.ofNat 64 (entry + 0x9c) ∨ S.pc = BitVec.ofNat 64 (entry + 0x13c))
    (hval : natVal S.mem zp.toNat zl.toNat + y.toNat = natVal s.mem xp.toNat zl.toNat) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hLs⟩, -⟩ := hpre
  obtain ⟨hsp, h28, h29, h18, h_rd_lr, h_rd_fp, hmf, hlf, hinv⟩ := hrel
  have hspn : S.sp.toNat = s.sp.toNat - 48 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hacc : S.mem.accessible (s.sp.toNat - 4144) (4144 + 40) true = true := by rw [hmf.accessible]; exact hw
  have hZ := natVal_lt s.mem xp.toNat zl.toNat
  have hZ' := natVal_lt S.mem zp.toNat zl.toNat
  have hP : 0 < 2 ^ (64 * zl.toNat) := Nat.two_pow_pos _
  rcases hpc with hpc | hpc
  all_goals
    janus_run
    refine ⟨?_, ?_, L, b, LiveExt.refl R L, Nat.le_refl _, hinv, ⟨fun a n h => hmf.readLE a n (out_z hk _ _ h), hmf.accessible⟩,
      liveFrame_mono hlf (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)⟩
    · rw [if_neg (by omega), if_neg (by omega)]; rfl
    · rw [show natVal s.mem xp.toNat zl.toNat + 2 ^ (64 * zl.toNat) - y.toNat =
        natVal S.mem zp.toNat zl.toNat + 2 ^ (64 * zl.toNat) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hZ']

theorem val_split (m : Memory) (p j n : Nat) (h : j ≤ n) :
    m.readLE p (8 * n) = m.readLE p (8 * j) + 2 ^ (64 * j) * m.readLE (p + 8 * j) (8 * (n - j)) := by
  rw [show 8 * n = 8 * j + 8 * (n - j) by omega, Memory.readLE_add,
    show (256 : Nat) ^ (8 * j) = 2 ^ (64 * j) by rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]

set_option maxRecDepth 20000 in
/-- the memory after the `memmove` of `copy`: frame, live frame, saved words and the value of `z` -/
theorem after (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hne : zp ≠ xp) (S : State) (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ zl.toNat)
    (hrel : Rel R b L ret zp.toNat j s S) (D Sr N : BitVec 64)
    (hD : D.toNat = if j < zc.toNat then zp.toNat + 8 * j else zp.toNat)
    (hS : Sr.toNat = if j < xc.toNat then xp.toNat + 8 * j else xp.toNat)
    (hN : N.toNat = zl.toNat - j)
    (hval : natVal S.mem zp.toNat j + y.toNat = natVal s.mem xp.toNat j) (m : Memory)
    (hMF : MemFrame S.mem m (R.rt ++ [(s.sp.toNat - 48 - 4096, s.sp.toNat - 48 - 8),
      (s.sp.toNat - 48 + 8, s.sp.toNat - 48 + 8 + 24)] ++ [(D.toNat, D.toNat + 8 * N.toNat)]))
    (hLF : LiveFrame S.mem m L [(D.toNat, D.toNat + 8 * N.toNat)])
    (hCP : Mem.Copied S.mem m D.toNat Sr.toNat (8 * N.toNat)) :
    m.readLE (s.sp.toNat - 48) 8 = ret ∧ m.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat ∧
      MemFrame s.mem m (R.rt ++ winA s 4144 40 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
      LiveFrame s.mem m L [(zp.toNat, zp.toNat + 8 * zl.toNat)] ∧
      natVal m zp.toNat zl.toNat + y.toNat = natVal s.mem xp.toNat zl.toNat := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hLs⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre
  obtain ⟨hsp, h28, h29, h18, h_rd_lr, h_rd_fp, hmf, hlf, hinv⟩ := hrel
  have hzx' : Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * zl.toNat) := hzx.resolve_left hne
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw hxw
  unfold Apart at hzx'
  have hDr : zp.toNat ≤ D.toNat ∧ D.toNat + 8 * N.toNat ≤ zp.toNat + 8 * zl.toNat ∧
      (zp.toNat + 8 * j ≤ D.toNat ∨ D.toNat + 8 * N.toNat ≤ zp.toNat) := by
    rw [hD, hN]; split <;> omega
  have hMF' : MemFrame S.mem m (R.rt ++ ([(s.sp.toNat - 48 - 4096, s.sp.toNat - 48 - 8),
      (s.sp.toNat - 48 + 8, s.sp.toNat - 48 + 8 + 24)] ++ [(D.toNat, D.toNat + 8 * N.toNat)])) := by
    rw [← List.append_assoc]; exact hMF
  have hmf' : MemFrame s.mem S.mem (R.rt ++ (winA s 4144 40 ++ [(zp.toNat, zp.toNat + 8 * j)])) := by
    rw [← List.append_assoc]; exact hmf
  have hLF' : LiveFrame S.mem m L ([(s.sp.toNat - 48 - 4096, s.sp.toNat - 48 - 8),
      (s.sp.toNat - 48 + 8, s.sp.toNat - 48 + 8 + 24)] ++ [(D.toNat, D.toNat + 8 * N.toNat)]) :=
    liveFrame_mono hLF (fun a n h => by rw [outside_append] at h; exact h.2)
  have hlf' : LiveFrame s.mem S.mem L (winA s 4144 40 ++ [(zp.toNat, zp.toNat + 8 * j)]) :=
    liveFrame_mono hlf (fun a n h => by rw [outside_append] at h; exact h.2)
  have hsk : ∀ a n, s.sp.toNat - 56 ≤ a → a + n ≤ s.sp.toNat - 40 →
      Outside a n (R.rt ++ [(s.sp.toNat - 48 - 4096, s.sp.toNat - 48 - 8),
        (s.sp.toNat - 48 + 8, s.sp.toNat - 48 + 8 + 24)] ++ [(D.toNat, D.toNat + 8 * N.toNat)]) := by
    intro a n h1 h2
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega⟩, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hMF.readLE _ _ (hsk _ _ (by omega) (by omega))]; exact h_rd_lr
  · rw [hMF.readLE _ _ (hsk _ _ (by omega) (by omega))]; exact h_rd_fp
  · refine MemFrame.trans hmf hMF (fun a n h => ?_)
    simp only [outside_append, outside_cons, outside_nil, and_true, winA] at h ⊢
    obtain ⟨⟨hr, h1, h2⟩, h3⟩ := h
    exact ⟨⟨⟨hr, h1, h2⟩, by omega⟩, ⟨hr, by omega, by omega⟩, by omega⟩
  · exact LiveFrame.trans (liveFrame_mono hlf (fun a n h => by
        simp only [outside_cons, outside_nil, and_true] at h ⊢; omega))
      (liveFrame_mono hLF (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega))
      (fun _ _ h => h)
  · have hlow : m.readLE zp.toNat (8 * j) = S.mem.readLE zp.toNat (8 * j) :=
      Held.readLE (hzh.sub (Nat.le_refl _) (by omega)) hMF' hLF' (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨⟨by omega, by omega⟩, by omega⟩)
    show m.readLE zp.toNat (8 * zl.toNat) + y.toNat = s.mem.readLE xp.toNat (8 * zl.toNat)
    rw [val_split m zp.toNat j zl.toNat hj, val_split s.mem xp.toNat j zl.toNat hj, hlow]
    have hv : S.mem.readLE zp.toNat (8 * j) + y.toNat = s.mem.readLE xp.toNat (8 * j) := hval
    by_cases hjl : j = zl.toNat
    · subst hjl; simp only [Nat.sub_self, Nat.mul_zero, Memory.readLE_zero]; omega
    have hjz : j < zc.toNat := by omega
    have hjx : j < xc.toNat := by omega
    simp only [hjz, hjx, ite_true] at hD hS
    have hc := FvModexp.Asm.readLE_of_copied hCP
    rw [hD, hS, hN] at hc
    have hx : S.mem.readLE (xp.toNat + 8 * j) (8 * (zl.toNat - j)) = s.mem.readLE (xp.toNat + 8 * j) (8 * (zl.toNat - j)) :=
      Held.readLE (hxh.sub (by omega) (by omega)) hmf' hlf' (by
        simp only [outside_append, winA, outside_cons, outside_nil, and_true]
        refine ⟨⟨by omega, by omega⟩, by omega⟩)
    rw [hc, hx]; omega

set_option maxRecDepth 20000 in
/-- a store of limb `i` of `z` keeps `Rel` (now `i + 1` limbs written) -/
theorem rel_store (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl zc xp xc : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (S : State) (i : Nat) (hi : i < zl.toNat)
    (hrel : Rel R b L ret zp.toNat i s S) (v : Nat) (S' : State) (hsp : S'.sp = S.sp) (h28 : S'.regs 28 = S.regs 28)
    (h29 : S'.regs 29 = S.regs 29) (h18 : S'.regs 18 = S.regs 18)
    (hm : S'.mem = S.mem.writeLE (zp.toNat + i * 8) 8 v) : Rel R b L ret zp.toNat (i + 1) s S' := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hLs⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre
  obtain ⟨hsp0, h280, h290, h180, h_rd_lr, h_rd_fp, hmf, hlf, hinv⟩ := hrel
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw
  refine ⟨hsp.trans hsp0, h28.trans h280, h29.trans h290, h18.trans h180, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h_rd_lr
  · rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h_rd_fp
  · rw [hm]
    refine ⟨fun a n h => ?_, fun a n w => by rw [Memory.accessible_writeLE]; exact hmf.accessible a n w⟩
    have h' := h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h'
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hmf.readLE a n (out_z (Nat.le_succ i) _ _ h)
  · rw [hm]
    exact LiveFrame.writeLE_ws (liveFrame_mono hlf (fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)) v
      (InRanges.cons_head _ (by omega) (by omega))
  · rw [hm]; exact inv_store_held hinv (hzh.sub (by omega) (by omega))

/-- bytes `[o, o + n)` of `x` at a boundary state (`k` limbs of `z` written): unchanged since the call -/
theorem rel_x (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl zc xp xc : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (S : State) (o n k : Nat) (hi : o + n ≤ 8 * zl.toNat)
    (hrel : Rel R b L ret zp.toNat k s S) (hkz : k ≤ zl.toNat) (hk : zp = xp → 8 * k ≤ o) :
    S.mem.readLE (xp.toNat + o) n = s.mem.readLE (xp.toNat + o) n := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hLs⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre
  obtain ⟨hsp0, h280, h290, h180, h_rd_lr, h_rd_fp, hmf, hlf, hinv⟩ := hrel
  have hmf' : MemFrame s.mem S.mem (R.rt ++ (winA s 4144 40 ++ [(zp.toNat, zp.toNat + 8 * k)])) := by
    rw [← List.append_assoc]; exact hmf
  have hlf' : LiveFrame s.mem S.mem L (winA s 4144 40 ++ [(zp.toNat, zp.toNat + 8 * k)]) :=
    liveFrame_mono hlf (fun a n h => by rw [outside_append] at h; exact h.2)
  simp only [Outside, and_true] at hxw
  refine Held.readLE (hxh.sub (by omega) (by omega)) hmf' hlf' ?_
  simp only [outside_append, winA, outside_cons, outside_nil, and_true]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rcases hzx with h | h
  · have := hk h; subst h; omega
  · unfold Apart at h; omega

set_option maxRecDepth 20000 in
/-- `copy(z[j:], x[j:])` (`+0x8c` after limb 0, `+0x12c` in the loop): `X0`/`X1` the masked slice pointers, `X3` the
count; then `ret0` -/
theorem copy (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hmv : MemmoveLive (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hne : zp ≠ xp) (S : State) (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ zl.toNat)
    (hrel : Rel R b L ret zp.toNat j s S)
    (hpc : S.pc = BitVec.ofNat 64 (entry + 0x8c) ∨ S.pc = BitVec.ofNat 64 (entry + 0x12c))
    (D Sr N : BitVec 64) (h0 : S.regs 0 = D) (h1 : S.regs 1 = Sr) (h3 : S.regs 3 = N)
    (hD : D.toNat = if j < zc.toNat then zp.toNat + 8 * j else zp.toNat)
    (hS : Sr.toNat = if j < xc.toNat then xp.toNat + 8 * j else xp.toNat)
    (hN : N.toNat = zl.toNat - j)
    (hval : natVal S.mem zp.toNat j + y.toNat = natVal s.mem xp.toNat j) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hLs⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre'
  have hrel' := hrel
  obtain ⟨hsp, h28, h29, h18, h_rd_lr, h_rd_fp, hmf, hlf, hinv⟩ := hrel'
  simp only [hne, if_false] at hmv'
  have hok := hmv' j hj1 hj
  rw [← hD, ← hS, show 8 * (zl.toNat - j) = 8 * N.toNat by rw [hN]] at hok
  have hzx' : Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * zl.toNat) := hzx.resolve_left hne
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  have hzg' := hzg (by omega)
  simp only [Outside, and_true] at hzw hxw
  have hspn : S.sp.toNat = s.sp.toNat - 48 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have h_rd_g : S.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hmf.readLE _ _ (by
      simp only [outside_append, winA, outside_cons, outside_nil, and_true]
      unfold Apart at hga hzg'
      exact ⟨⟨hgr, by omega, by omega⟩, by omega⟩)
  have hgacc : S.mem.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hmf.accessible]; exact hg2
  have hsacc : S.mem.accessible (s.sp.toNat - 4144) (4144 + 40) true = true := by rw [hmf.accessible]; exact hw
  have hDr : zp.toNat ≤ D.toNat ∧ D.toNat + 8 * N.toNat ≤ zp.toNat + 8 * zl.toNat := by
    rw [hD, hN]; split <;> omega
  have hSr : xp.toNat ≤ Sr.toNat ∧ Sr.toNat + 8 * N.toNat ≤ xp.toNat + 8 * zl.toNat := by
    rw [hS, hN]; split <;> omega
  have hDacc : S.mem.accessible D.toNat (8 * N.toNat) true = true := by
    rw [hmf.accessible]; exact Memory.accessible_sub _ hzacc (Or.inr rfl) hDr.1 hDr.2
  have hSacc : S.mem.accessible Sr.toNat (8 * N.toNat) false = true := by
    rw [hmf.accessible]; exact Memory.accessible_sub _ hxacc (Or.inl rfl) hSr.1 hSr.2
  have hDh : InRanges D.toNat (8 * N.toNat) L ∨ Outside D.toNat (8 * N.toNat) R.rt := hzh.sub hDr.1 hDr.2
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 40 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; exact this
  have hN61 : N.toNat < 2 ^ 61 := by omega
  rcases hpc with hpc | hpc
  all_goals
    janus_run until [entry + 0x9c, entry + 0x13c] calls [hmv L b]
    · have hjl : j = zl.toNat := by
        by_cases hjz : j < zc.toNat <;> by_cases hjx : j < xc.toNat <;>
          simp only [hjz, hjx, ite_true, ite_false] at hD hS <;> unfold Apart at hzx' <;> omega
      subst hjl
      exact ret0 impl R b L ret hret s zp zl zc xp xc y hpre _ zl.toNat (Nat.le_refl _) (by omega)
        ⟨rfl, hrel.g, hrel.fp, hrel.r18, hrel.lr, hrel.sfp, hrel.mf, hrel.lf, hrel.inv⟩
        (by first | exact Or.inl rfl | exact Or.inr rfl) hval
    · rename_i junk fl v m ex ep hMF hLF hINV hCP
      obtain ⟨e1, e2, e3, e4, e5⟩ := after R b L ret s zp zl zc xp xc y hpre hne S j hj1 hj hrel D Sr N hD hS hN hval m
        hMF hLF hCP
      refine ret0 impl R b L ret hret s zp zl zc xp xc y hpre _ zl.toNat (Nat.le_refl _) (by omega)
        ⟨rfl, ?_, ?_, ?_, e1, e2, e3, e4, hINV⟩ (by first | exact Or.inl rfl | exact Or.inr rfl) e5
      all_goals janus_simp

set_option maxRecDepth 20000 in
/-- after `z[i] = x[i] - 1` with `z = x` (`+0x13c`): nothing more to copy -/
theorem step_inplace (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (he : zp = xp) (S : State) (i : Nat) (hi : i < zl.toNat)
    (hrel : Rel R b L ret zp.toNat i s S)
    (hval : natVal S.mem zp.toNat i + y.toNat = natVal s.mem xp.toNat i + 2 ^ (64 * i))
    (hxv : s.mem.readLE (xp.toNat + i * 8) 8 ≠ 0)
    (S' : State) (hsp : S'.sp = S.sp) (h28 : S'.regs 28 = S.regs 28) (h29 : S'.regs 29 = S.regs 29)
    (h18 : S'.regs 18 = S.regs 18)
    (hm : S'.mem = S.mem.writeLE (zp.toNat + i * 8) 8 (s.mem.readLE (xp.toNat + i * 8) 8 - 1))
    (hpc : S'.pc = BitVec.ofNat 64 (entry + 0x13c)) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S'
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  have hr' := rel_store R b L ret s zp zl zc xp xc hpre S i hi hrel _ S' hsp h28 h29 h18 hm
  refine ret0 impl R b L ret hret s zp zl zc xp xc y hpre S' (i + 1) (by omega) (by omega) hr' (Or.inr hpc) ?_
  have hlow : natVal S'.mem zp.toNat (i + 1) + y.toNat = natVal s.mem xp.toNat (i + 1) := by
    rw [hm]; exact FvModexp.Asm.v_dec S.mem s.mem _ _ i _ hval hxv
  have hup := rel_x R b L ret s zp zl zc xp xc hpre S' (8 * (i + 1)) (8 * (zl.toNat - (i + 1))) (i + 1) (by omega)
    hr' (by omega) (fun _ => Nat.le_refl _)
  show S'.mem.readLE zp.toNat (8 * zl.toNat) + y.toNat = s.mem.readLE xp.toNat (8 * zl.toNat)
  rw [val_split S'.mem zp.toNat (i + 1) zl.toNat (by omega), val_split s.mem xp.toNat (i + 1) zl.toNat (by omega)]
  have hlow' : S'.mem.readLE zp.toNat (8 * (i + 1)) + y.toNat = s.mem.readLE xp.toNat (8 * (i + 1)) := hlow
  rw [he] at hlow'; rw [he, hup]; omega

set_option maxRecDepth 20000 in
/-- after `z[i] = x[i] - 1` with `z ≠ x`, the pointers of `copy(z[i+1:], x[i+1:])` computed (`+0x12c`) -/
theorem step_copy (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hmv : MemmoveLive (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hne : ¬zp.toNat = xp.toNat) (S : State) (i : Nat) (hi : i < zl.toNat)
    (hrel : Rel R b L ret zp.toNat i s S)
    (hval : natVal S.mem zp.toNat i + y.toNat = natVal s.mem xp.toNat i + 2 ^ (64 * i))
    (hxv : s.mem.readLE (xp.toNat + i * 8) 8 ≠ 0)
    (S' : State) (hsp : S'.sp = S.sp) (h28 : S'.regs 28 = S.regs 28) (h29 : S'.regs 29 = S.regs 29)
    (h18 : S'.regs 18 = S.regs 18)
    (hm : S'.mem = S.mem.writeLE (zp.toNat + i * 8) 8 (s.mem.readLE (xp.toNat + i * 8) 8 - 1))
    (hpc : S'.pc = BitVec.ofNat 64 (entry + 0x12c))
    (h0 : S'.regs 0 = zp + (BitVec.ofNat 64 i + 1#64 &&& (0#64 - (zc - BitVec.ofNat 64 (i + 1))).sshiftRight 63) <<< 3)
    (h1 : S'.regs 1 = xp + (BitVec.ofNat 64 i + 1#64 &&& (0#64 - (xc - BitVec.ofNat 64 (i + 1))).sshiftRight 63) <<< 3)
    (h3 : S'.regs 3 = zl - BitVec.ofNat 64 (i + 1)) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S'
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  have hr' := rel_store R b L ret s zp zl zc xp xc hpre S i hi hrel _ S' hsp h28 h29 h18 hm
  have hpre' := hpre
  obtain ⟨-, hzc, hxc, hzc63, hxc63, hzl, -, -, -, hx48, -⟩ := hpre'
  obtain ⟨-, -, -, hz48⟩ := hzl (by omega)
  have hne' : zp ≠ xp := fun h => hne (by rw [h])
  refine copy impl R b L ret hmv hret s zp zl zc xp xc y hpre hne' S' (i + 1) (by omega) (by omega) hr'
    (Or.inr hpc) _ _ _ h0 h1 h3 ?_ ?_ ?_ ?_
  · rw [BitVec.toNat_add, FvModexp.Asm.maskB zc i hzc63 (by omega) (by omega)]
    split <;> omega
  · rw [BitVec.toNat_add, FvModexp.Asm.maskB xc i hxc63 (by omega) (by omega)]
    split <;> omega
  · rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [hm]; exact FvModexp.Asm.v_dec S.mem s.mem _ _ i _ hval hxv

/-- the loop state at the head (`+0xc8`, `X6 = i`) -/
def AtHead (zp zl zc xp xc : BitVec 64) (i : Nat) (S : State) : Prop :=
  S.pc = BitVec.ofNat 64 (entry + 0xc8) ∧ S.regs 0 = zp ∧ S.regs 1 = zl ∧ S.regs 2 = zc ∧ S.regs 3 = xp ∧
    S.regs 4 = zl ∧ S.regs 5 = xc ∧ S.regs 6 = BitVec.ofNat 64 i

set_option maxRecDepth 20000 in
/-- the loop exit (`i = len z`): the borrow out is `1` -/
theorem fin1 (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (S : State) (hz : 0 < zl.toNat) (hh : AtHead zp zl zc xp xc zl.toNat S)
    (hrel : Rel R b L ret zp.toNat zl.toNat s S)
    (hval : natVal S.mem zp.toNat zl.toNat + y.toNat = natVal s.mem xp.toNat zl.toNat + 2 ^ (64 * zl.toNat)) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hLs⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre
  obtain ⟨hpc, h0, h1, h2, h3, h4, h5, h6⟩ := hh
  obtain ⟨hsp, h28, h29, h18, h_rd_lr, h_rd_fp, hmf, hlf, hinv⟩ := hrel
  have hspn : S.sp.toNat = s.sp.toNat - 48 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hacc : S.mem.accessible (s.sp.toNat - 4144) (4144 + 40) true = true := by rw [hmf.accessible]; exact hw
  have hz63 : zl.toNat < 2 ^ 63 := by omega
  have hlt := natVal_lt S.mem zp.toNat zl.toNat
  have hP : 0 < 2 ^ (64 * zl.toNat) := Nat.two_pow_pos _
  janus_run
  refine ⟨?_, ?_, L, b, LiveExt.refl R L, Nat.le_refl _, hinv, hmf, hlf⟩
  · rw [if_neg (by omega), if_pos (by omega)]; rfl
  · rw [show natVal s.mem xp.toNat zl.toNat + 2 ^ (64 * zl.toNat) - y.toNat = natVal S.mem zp.toNat zl.toNat by omega,
      Nat.mod_eq_of_lt hlt]

set_option linter.janusRenameI false in
set_option maxRecDepth 20000 in
/-- one pass of the loop body (`i < len z`), the next head handed to `IH` -/
theorem body (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hmv : MemmoveLive (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (S : State) (i : Nat) (hi : i < zl.toNat) (hi1 : 1 ≤ i)
    (hh : AtHead zp zl zc xp xc i S) (hrel : Rel R b L ret zp.toNat i s S)
    (hval : natVal S.mem zp.toNat i + y.toNat = natVal s.mem xp.toNat i + 2 ^ (64 * i))
    (IH : ∀ S', AtHead zp zl zc xp xc (i + 1) S' → Rel R b L ret zp.toNat (i + 1) s S' →
      natVal S'.mem zp.toNat (i + 1) + y.toNat = natVal s.mem xp.toNat (i + 1) + 2 ^ (64 * (i + 1)) →
      Reaches ((LibSubVW.program.link impl).withExit ret) S'
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s')) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hLs⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre'
  obtain ⟨hpc, h0, h1, h2, h3, h4, h5, h6⟩ := hh
  have hrel' := hrel
  obtain ⟨hsp, h28, h29, h18, h_rd_lr, h_rd_fp, hmf, hlf, hinv⟩ := hrel'
  have hspn : S.sp.toNat = s.sp.toNat - 48 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hacc : S.mem.accessible (s.sp.toNat - 4144) (4144 + 40) true = true := by rw [hmf.accessible]; exact hw
  have hz63 : zl.toNat < 2 ^ 63 := by omega
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  have hzacc' : S.mem.accessible zp.toNat (8 * zl.toNat) true = true := by rw [hmf.accessible]; exact hzacc
  have hxacc' : S.mem.accessible xp.toNat (8 * zl.toNat) false = true := by rw [hmf.accessible]; exact hxacc
  have h_rd_x := rel_x R b L ret s zp zl zc xp xc hpre S (i * 8) 8 i (by omega) hrel (by omega) (fun _ => by omega)
  have hxl : s.mem.readLE (xp.toNat + i * 8) 8 < 2 ^ 64 := by
    have := Memory.readLE_lt s.mem (xp.toNat + i * 8) 8; simpa using this
  have hi64 : i + 1 < 2 ^ 64 := by omega
  clear hmv' hinv0 hLs hga hgr hout
  janus_run until [entry + 0xc8, entry + 0x12c, entry + 0x13c]
  · refine IH _ ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      (rel_store R b L ret s zp zl zc xp xc hpre S i hi hrel _ _ hsp.symm rfl rfl rfl rfl)
      (FvModexp.Asm.v_zero S.mem s.mem _ _ i _ hval hbr)
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · show BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1)
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · rename_i _ hxv
    exact step_inplace impl R b L ret hret s zp zl zc xp xc y hpre (BitVec.eq_of_toNat_eq hbr) S i hi hrel
      hval hxv _ hsp.symm rfl rfl rfl rfl rfl
  · rename_i _ hxv
    exact step_copy impl R b L ret hmv hret s zp zl zc xp xc y hpre hbr S i hi hrel
      hval hxv _ hsp.symm rfl rfl rfl rfl rfl rfl rfl rfl

/-- the borrow loop (`+0xc8`, `X6 = i`), by induction on `len z - i`: `z[0:i] + y = x[0:i] + B^i` -/
theorem loop (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hmv : MemmoveLive (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) :
    ∀ t (S : State) (i : Nat), i + t = zl.toNat → 1 ≤ i → AtHead zp zl zc xp xc i S →
      Rel R b L ret zp.toNat i s S →
      natVal S.mem zp.toNat i + y.toNat = natVal s.mem xp.toNat i + 2 ^ (64 * i) →
      Reaches ((LibSubVW.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  intro t
  induction t with
  | zero =>
    intro S i hi hi1 hh hrel hval
    obtain rfl : i = zl.toNat := by omega
    exact fin1 impl R b L ret hret s zp zl zc xp xc y hpre S (by omega) hh hrel hval
  | succ t ih =>
    intro S i hi hi1 hh hrel hval
    exact body impl R b L ret hmv hret s zp zl zc xp xc y hpre S i (by omega) hi1 hh hrel hval
      (fun S' hh' hrel' hval' => ih S' (i + 1) (by omega) (by omega) hh' hrel' hval')

set_option maxRecDepth 20000 in
/-- the prologue's stores (saved `X30`, `X29`, the spills of `X0`, `X3`) and `z[0] = v`: `Rel` with one limb written -/
theorem entry_rel (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl zc xp xc : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hz : 0 < zl.toNat) (hret : ret < 2 ^ 48) (v : Nat) {S' : State}
    (hsp : S'.sp = s.sp - 48#64) (h28 : S'.regs 28 = s.regs 28) (h29 : S'.regs 29 = s.sp - 56#64)
    (h18 : S'.regs 18 = s.regs 18)
    (hm : S'.mem = ((((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat).writeLE
      (s.sp.toNat + 8) 8 zp.toNat).writeLE (s.sp.toNat + 32) 8 xp.toNat).writeLE zp.toNat 8 v) :
    Rel R b L ret zp.toNat 1 s S' ∧ S'.mem.readLE zp.toNat 8 = v % 2 ^ 64 := by
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hLs⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hz
  simp only [Outside, and_true] at hzw
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 40 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; exact this
  have hwin : ∀ r ∈ winA s 4144 40, s.sp.toNat - 4144 ≤ r.1 ∧ r.2 ≤ s.sp.toNat + 40 := by
    simp only [winA, List.mem_cons, List.mem_nil_iff, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega
  have hmf : MemFrame s.mem S'.mem (winA s 4144 40 ++ [(zp.toNat, zp.toNat + 8 * 1)]) := by
    rw [hm]; simp only [winA, List.cons_append, List.nil_append]; janus_frame
  have hrt : ∀ a n, s.sp.toNat - 4144 ≤ a → a + n ≤ s.sp.toNat + 40 → Outside a n R.rt :=
    fun a n h1 h2 => Outside.of_sub hout h1 (by omega)
  refine ⟨⟨hsp, h28, h29, h18, ?_, ?_, ?_, liveFrame_of_frame (rs := winA s 4144 40) hmf hLs' hwin, ?_⟩, ?_⟩
  · rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (by omega)
  · rw [hm, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (s.regs 29).isLt
  · exact ⟨fun a n h => hmf.readLE a n (by simp only [outside_append] at h ⊢; exact ⟨h.1.2, h.2⟩), hmf.accessible⟩
  · rw [hm]
    refine inv_store_held (inv_store_out (inv_store_out (inv_store_out (inv_store_out hinv0
      (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega)))
      (hrt _ _ (by omega) (by omega))) (hzh.sub (Nat.le_refl _) (by omega))
  · rw [hm, Memory.readLE_writeLE_self]

/-- `entry_rel` in continuation form (for a goal about the executor's state literal) -/
theorem entry_k (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl zc xp xc : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hz : 0 < zl.toNat) (hret : ret < 2 ^ 48) (v : Nat) (p : Program)
    (Q : Outcome → Prop) (S' : State)
    (hsp : S'.sp = s.sp - 48#64) (h28 : S'.regs 28 = s.regs 28) (h29 : S'.regs 29 = s.sp - 56#64)
    (h18 : S'.regs 18 = s.regs 18)
    (hm : S'.mem = ((((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat).writeLE
      (s.sp.toNat + 8) 8 zp.toNat).writeLE (s.sp.toNat + 32) 8 xp.toNat).writeLE zp.toNat 8 v)
    (K : Rel R b L ret zp.toNat 1 s S' → S'.mem.readLE zp.toNat 8 = v % 2 ^ 64 → Reaches p S' Q) : Reaches p S' Q :=
  let h := entry_rel R b L ret s zp zl zc xp xc hpre hz hret v hsp h28 h29 h18 hm
  K h.1 h.2

/-- `z = x` with the low `j` limbs of `z` holding `x[0:j] + y`: the rest of `z` is still `x`, so `z = x + y` -/
theorem val_inplace (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (he : zp = xp) (S : State) (j : Nat) (hj : j ≤ zl.toNat)
    (hrel : Rel R b L ret zp.toNat j s S)
    (hlow : natVal S.mem zp.toNat j + y.toNat = natVal s.mem xp.toNat j) :
    natVal S.mem zp.toNat zl.toNat + y.toNat = natVal s.mem xp.toNat zl.toNat := by
  have hup := rel_x R b L ret s zp zl zc xp xc hpre S (8 * j) (8 * (zl.toNat - j)) j (by omega)
    hrel hj (fun _ => Nat.le_refl _)
  show S.mem.readLE zp.toNat (8 * zl.toNat) + y.toNat = s.mem.readLE xp.toNat (8 * zl.toNat)
  rw [val_split S.mem zp.toNat j zl.toNat hj, val_split s.mem xp.toNat j zl.toNat hj]
  have hlow' : S.mem.readLE zp.toNat (8 * j) + y.toNat = s.mem.readLE xp.toNat (8 * j) := hlow
  rw [he] at hlow'; rw [he, hup]; omega

set_option linter.janusRenameI false in
set_option maxRecDepth 20000 in
/-- `subVW` on the library program -/
theorem ens_lib (impl : List Segment) (R : RtInv)
    (hmv : MemmoveLive (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures (LibSubVW.program.link impl) entry [zp, zl, zc, xp, xl, xc, y]
      (fun s => xl = zl ∧ Pre R b L zp zl zc xp xc s) (fun s s' => Post R b L zp zl xp y s s') := by
  intro ret hret s hs ⟨hxz, hpre⟩
  have hpre' := hpre
  obtain ⟨⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hout, hga, hgr, hLs⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv, hmv'⟩ := hpre'
  janus_intro hs
  subst hxz
  simp only [Outside, and_true] at hzw hxw
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ s.sp.toNat - 4144 ∨ s.sp.toNat + 40 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [Outside, and_true] at this; exact this
  have hwin : ∀ r ∈ winA s 4144 40, s.sp.toNat - 4144 ≤ r.1 ∧ r.2 ≤ s.sp.toNat + 40 := by
    simp only [winA, List.mem_cons, List.mem_nil_iff, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega
  by_cases hz0 : xl.toNat = 0
  · janus_run
    refine ⟨by simp [hz0]; rfl, by simp [hz0, Nat.mod_one], L, b, LiveExt.refl R L, Nat.le_refl _, by janus_live, ?_, ?_⟩
    · simp only [winA, List.append_assoc, List.cons_append, List.nil_append]; janus_frame
    · refine liveFrame_of_frame (rs := winA s 4144 40) ?_ hLs' hwin
      simp only [winA, List.cons_append, List.nil_append]; janus_frame
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  clear hmv'
  have hx0 : s.mem.readLE xp.toNat 8 < 2 ^ 64 := by
    have := Memory.readLE_lt s.mem xp.toNat 8; simpa using this
  have hy := y.isLt
  have hb0 := FvModexp.Asm.borrow0 _ hx0 y
  have m8z := FvModexp.Asm.mask8B zc hzc63 (by omega)
  have m8x := FvModexp.Asm.mask8B xc hxc63 (by omega)
  janus_run [hb0] until [entry + 0xc8, entry + 0x8c, entry + 0x9c]
  all_goals
    refine entry_k R b L ret s zp xl zc xp xc hpre (by omega) hret.user
      (18446744073709551616 - y.toNat + s.mem.readLE xp.toNat 8) _ _ _ rfl rfl rfl rfl rfl (fun hr1 hv1 => ?_)
  · rename_i _ _ hnc
    refine ret0 impl R b L ret hret s zp xl zc xp xc y hpre _ 1 (by omega) (by omega) hr1 (Or.inl rfl)
      (val_inplace R b L ret s zp xl zc xp xc y hpre (BitVec.eq_of_toNat_eq hbr) _ 1 (by omega) hr1 ?_)
    simp only [natVal, Nat.mul_one]; rw [hv1]; omega
  · rename_i _ _ hnc
    have hne : zp ≠ xp := fun h => hbr (by rw [h])
    refine copy impl R b L ret hmv hret s zp xl zc xp xc y hpre hne _ 1 (Nat.le_refl _) (by omega) hr1
      (Or.inl rfl) _ _ _ rfl rfl rfl ?_ ?_ ?_ ?_
    · show (zp + _ : BitVec 64).toNat = _
      rw [BitVec.toNat_add, m8z]; split <;> omega
    · show (xp + _ : BitVec 64).toNat = _
      rw [BitVec.toNat_add, m8x]; split <;> omega
    · show (xl - 1#64 : BitVec 64).toNat = _
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    · simp only [natVal, Nat.mul_one]; rw [hv1]; omega
  · refine loop impl R b L ret hmv hret s zp xl zc xp xc y hpre (xl.toNat - 1) _ 1 (by omega) (Nat.le_refl _)
      ⟨rfl, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, rfl⟩ hr1 ?_
    simp only [natVal, Nat.mul_one]; rw [hv1]; omega

/-- **`subVW` (arm64)**, CONVENTIONS §3 shape (`Pre`/`Post` above; `xl = zl` is the `len(z) != len(x)` panic excluded) -/
theorem ens (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments [fn]).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y]
      (fun s => xl = zl ∧ Pre R b L zp zl zc xp xc s) (fun s s' => Post R b L zp zl xp y s s') := by
  have hmv' := MemmoveLive.of_codeIn (codeIn_ofImpl_restrict_of_apart hap [fn]) hmv
  have e : Extracted.program.onlySegments [fn] = LibSubVW.program := LibSubVW.eq_only.symm
  rw [e] at hmv' ⊢
  exact ens_lib impl R hmv' b L zp zl zc xp xl xc y

set_option linter.defProp false in
/-- `ens` as a callee summary inside a caller whose program keeps the functions `ms ⊇ [fn]` (CONVENTIONS §4) -/
def sum (impl : List Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) (ms : List String)
    (hsub : ∀ x, [fn].contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmv b L zp zl zc xp xl xc y) (noExit_restrict hap [fn])
    (codeIn_restrict_mono hap hsub)

end FvModexp.Arm64.SubVW
