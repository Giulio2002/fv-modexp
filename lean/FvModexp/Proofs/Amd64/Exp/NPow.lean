import FvModexp.Proofs.Amd64.Exp.NDisp

set_option autoImplicit false

/-!
# `nat.expNN` (amd64): `m.isPow2()` (nat.go:376-388, inlined at `0x5e7800..0x5e7840`) → `expNNPowerOfTwo` entry
(agent expmc s70; twin of `Arm64.ExpN.powAll`)

For `m = 2^(64(n-1) + e)` (normalised: words `0..n-2` zero, word `n-1 = 2^e`), from the loop head `powH` (`BX = n`,
`R10 = i`, `R13 = mp`; `AX` = `z`'s pointer, reloaded from `[t - 0x60]` after each zero word): no `panicBounds`
(`i < n`), the test `i == len(m)-1 && x&(x-1) == 0` succeeds, `logM = 64 i + ctz(x)` (`SHLQ $6; BSFQ; ADDQ`), the
stack argument `y` is stored to `[t - 0x108, t - 0xf0)`, `R10 := logM`, `BX := R11` (= `n`), `CALL expNNPowerOfTwo`
(`0x5e8fa0`, return `0x5e7865` pushed at `t - 0x110`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.ExpN

/-- `expNNPowerOfTwo`'s entry, the return point of its call -/
abbrev p2A : Nat := 6197152
abbrev p2R : Nat := 6191205

theorem ctzNat_pow : ∀ n e, e < n → Janus.Amd64.ctzNat n (2 ^ e) = e
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, e, h => by
    rcases e with _ | e
    · simp [Janus.Amd64.ctzNat]
    · have h2 : 2 ^ (e + 1) % 2 = 0 := by rw [Nat.pow_succ]; exact Nat.mul_mod_left _ _
      have h3 : 2 ^ (e + 1) / 2 = 2 ^ e := by rw [Nat.pow_succ]; exact Nat.mul_div_cancel _ (by decide)
      simp only [Janus.Amd64.ctzNat, h2, h3, Nat.zero_ne_one, ite_false]
      rw [ctzNat_pow n e (by omega)]; omega

/-- the continuation at `expNNPowerOfTwo`'s entry (registers relative to `G`, the loop's register file) -/
@[reducible] def P2K (impl : List Amd64.Segment) (ret0 : Nat) (Q : Amd64.Outcome → Prop) (G : Nat → BitVec 64)
    (fs : BitVec 64) (df : Bool) (x15 : BitVec 128) (t lg : Nat) (M : Janus.Arm64.Memory) : Prop :=
  ∀ (S' : State) (M' : Janus.Arm64.Memory),
    S'.rip = BitVec.ofNat 64 p2A → S'.regs 4 = BitVec.ofNat 64 (t - 0x110) →
    S'.regs 0 = G 0 → S'.regs 1 = G 1 → S'.regs 3 = G 11 → S'.regs 7 = G 7 →
    S'.regs 6 = G 6 → S'.regs 8 = G 8 → S'.regs 9 = G 9 → S'.regs 10 = BitVec.ofNat 64 lg →
    S'.regs 14 = G 14 → S'.fsBase = fs → S'.df = df → S'.xmm 15 = x15 → S'.mem = M' →
    MemFrame M M' [(t - 0x110, t - 0xf0)] → M'.regions = M.regions →
    M'.readLE (t - 0x110) 8 = p2R → M'.readLE (t - 0x108) 8 = (G 12).toNat → M'.readLE (t - 0x100) 8 = (G 15).toNat →
    M'.readLE (t - 0xf8) 8 = (G 2).toNat →
    Reaches ((LibN.program.link impl).withExit ret0) S' Q

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.unusedSimpArgs false in
theorem powStep (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (G : Nat → BitVec 64) (fs : BitVec 64) (df : Bool) (x15 : BitVec 128)
    (t mp n e i : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x110) 0x188 true = true)
    (hmp : mp + 8 * n ≤ 2 ^ 48) (hma : M.accessible mp (8 * n) false = true)
    (hi : i + 1 ≤ n) (he : e < 64) (hw : M.readLE (mp + 8 * i) 8 = if i + 1 = n then 2 ^ e else 0)
    (h0 : M.readLE (t - 0x60) 8 = (G 0).toNat)
    (S : State) (hpc : S.rip = BitVec.ofNat 64 powH) (hsp : S.regs 4 = BitVec.ofNat 64 (t - 0x108))
    (hG : ∀ r, r ≠ 10 → S.regs r = G r) (h3 : G 3 = BitVec.ofNat 64 n) (h13 : G 13 = BitVec.ofNat 64 mp)
    (h10 : S.regs 10 = BitVec.ofNat 64 i) (hfs : S.fsBase = fs) (hdf : S.df = df) (hx : S.xmm 15 = x15)
    (hmem : S.mem = M)
    (KN : i + 1 < n → ∀ S' : State, S'.rip = BitVec.ofNat 64 powH → (∀ r, r ≠ 10 → S'.regs r = G r) →
      S'.regs 10 = BitVec.ofNat 64 (i + 1) → S'.fsBase = fs → S'.df = df → S'.xmm 15 = x15 → S'.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S' Q)
    (KP : i + 1 = n → P2K impl ret0 Q G fs df x15 t (64 * i + e) M) :
    Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  have ha : M.accessible (mp + 8 * i) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hma (by omega) (by omega)
  have hpe : 2 ^ e < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) he
  have hpz : 2 ^ e ≠ 0 := Nat.pos_iff_ne_zero.1 Nat.one_le_two_pow
  have s0 := hG 0 (by decide); have s1 := hG 1 (by decide); have s2 := hG 2 (by decide)
  have s3 := hG 3 (by decide); have s6 := hG 6 (by decide); have s7 := hG 7 (by decide)
  have s8 := hG 8 (by decide); have s9 := hG 9 (by decide); have s11 := hG 11 (by decide)
  have s12 := hG 12 (by decide); have s13 := hG 13 (by decide); have s14 := hG 14 (by decide)
  have s15 := hG 15 (by decide)
  rw [h3] at s3; rw [h13] at s13
  have aa8 : t - 0x108 + 0xa8 = t - 0x60 := by omega
  have g0 : BitVec.ofNat 64 (G 0).toNat = G 0 := BitVec.ofNat_toNat _ _
  subst hmem
  by_cases hl : i + 1 = n
  · simp only [hl, ↓reduceIte] at hw
    have hw' : S.mem.readLE (mp + i * 8) 8 = 2 ^ e := by rw [Nat.mul_comm]; exact hw
    have hc : Janus.Amd64.ctzNat 64 (2 ^ e) = e := ctzNat_pow 64 e he
    have es1 : BitVec.ofNat 64 (t - 0x108) - 8#64 = BitVec.ofNat 64 (t - 0x110) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have ha3 : 2 ^ e &&& 2 ^ e - 1 = 0 := by rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_self _
    have hi45 : i < 2 ^ 45 := by omega
    janus64_run [hw', hc, es1, aa8, h0, g0] until [p2A, powH, 6191290, 6191436]
    refine KP hl _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_
    iterate 9 (first | rfl | (simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; janus_assumption))
    · apply BitVec.eq_of_toNat_eq
      simp only [setRegF_apply, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq, hc]
      omega
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; janus_assumption
    · exact hfs
    · rfl
    · exact hx
    · janus_frame
    · simp only [Janus.Arm64.Memory.regions_writeLE]
    all_goals (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, rdd_eq, Nat.mod_eq_of_lt (BitVec.isLt _), Nat.reducePow, Nat.reduceMod])
  · simp only [hl, ↓reduceIte] at hw
    have hw' : S.mem.readLE (mp + i * 8) 8 = 0 := by rw [Nat.mul_comm]; exact hw
    janus64_run [hw', aa8, h0, g0] until [p2A, powH, 6191290, 6191436]
    refine KN (by omega) _ rfl (fun r hr => ?_) rfl hfs rfl hx rfl
    simp only [setRegF_apply]
    by_cases r0 : r = 0
    · subst r0; simp
    · simp only [hr, r0, ite_false]; exact hG r hr

/-- the whole `isPow2` loop from `i` (words `i..n-2` zero, word `n-1 = 2^e`) to `expNNPowerOfTwo`'s entry -/
theorem powAll (impl : List Amd64.Segment) (ret0 : Nat) (hret : RetAddr (LibN.program.link impl) ret0)
    (Q : Amd64.Outcome → Prop) (G : Nat → BitVec 64) (fs : BitVec 64) (df : Bool) (x15 : BitVec 128)
    (t mp n e : Nat) (M : Janus.Arm64.Memory)
    (ht1 : 0x110 ≤ t) (ht2 : t + 0x78 ≤ 2 ^ 48) (hacc : M.accessible (t - 0x110) 0x188 true = true)
    (hmp : mp + 8 * n ≤ 2 ^ 48) (hma : M.accessible mp (8 * n) false = true) (he : e < 64)
    (hw : ∀ j, j < n → M.readLE (mp + 8 * j) 8 = if j + 1 = n then 2 ^ e else 0)
    (h0 : M.readLE (t - 0x60) 8 = (G 0).toNat) (h3 : G 3 = BitVec.ofNat 64 n) (h4 : G 4 = BitVec.ofNat 64 (t - 0x108))
    (h13 : G 13 = BitVec.ofNat 64 mp)
    (KP : P2K impl ret0 Q G fs df x15 t (64 * (n - 1) + e) M) :
    ∀ d i (S : State), n - 1 - i = d → i < n → S.rip = BitVec.ofNat 64 powH → (∀ r, r ≠ 10 → S.regs r = G r) →
      S.regs 10 = BitVec.ofNat 64 i → S.fsBase = fs → S.df = df → S.xmm 15 = x15 → S.mem = M →
      Reaches ((LibN.program.link impl).withExit ret0) S Q := by
  intro d
  induction d with
  | zero =>
    intro i S hd hi hpc hG h10 hfs hdf hx hmem
    have hl : i + 1 = n := by omega
    refine powStep impl ret0 hret Q G fs df x15 t mp n e i M ht1 ht2 hacc hmp hma (by omega) he (hw i hi) h0 S hpc
      ((hG 4 (by decide)).trans h4) hG h3 h13 h10 hfs hdf hx hmem (fun h => absurd h (by omega)) (fun _ => ?_)
    rw [show i = n - 1 by omega]; exact KP
  | succ d ih =>
    intro i S hd hi hpc hG h10 hfs hdf hx hmem
    exact powStep impl ret0 hret Q G fs df x15 t mp n e i M ht1 ht2 hacc hmp hma (by omega) he (hw i hi) h0 S hpc
      ((hG 4 (by decide)).trans h4) hG h3 h13 h10 hfs hdf hx hmem
      (fun hl S' e1 e2 e3 e4 e5 e6 e7 => ih (i + 1) S' (by omega) hl e1 e2 e3 e4 e5 e6 e7) (fun hl => absurd hl (by omega))

end FvModexp.Amd64.ExpN
