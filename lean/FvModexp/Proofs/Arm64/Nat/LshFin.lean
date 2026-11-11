import FvModexp.Proofs.Arm64.Nat.LshDefs
import FvModexp.Proofs.Common.ExpmcFrame
import FvModexp.Proofs.Common.DivmcNat
import FvModexp.Proofs.Common.TruncMath
import FvModexp.Proofs.Common.BitArith

/-!
# `nat.lsh` (arm64): `clear(z[0 : n-m])` (`+0x234`), the inlined `z.norm()` loop (`+0x26c`) and the return

At `hClr` (`CMP R6>>6, R2`): `R0 = p`, `R1 = n + 1`, `R2 = c`, `R6 = s`, `R8 = s / 64`; `z[n-m : n+1]` holds
`X · 2^(s % 64)`. `CBZ R8` skips the clear; else `memclrNoHeapPointers(p, 8 (s/64))`, reloads `R0, R1, R2` from
`SP - 24, SP - 48, SP - 80`. Norm loop: `for i > 0 && z[i-1] == 0 { i-- }` (`+0x268 MOVD R3, R1` is the loop-back
entry), `return z[0:i]` (`CMP R2, R1; BHI panic`; `MOVD -8(RSP), R29; MOVD.P 160(RSP), R30; RET`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

set_option linter.janusRenameI false

namespace FvModexp.Arm64.Lsh

abbrev hNorm : Nat := segAddr Extracted.program fn + 0x26c
abbrev hClr : Nat := segAddr Extracted.program fn + 0x234
abbrev hJoin : Nat := segAddr Extracted.program fn + 0x16c

theorem natVal_drop_zero {M : Memory} {p i : Nat} (h : M.readLE (p + 8 * i) 8 = 0) :
    natVal M p (i + 1) = natVal M p i := by rw [natVal_succ, h]; simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem norm (impl : List Segment) (s : State) (M : Memory) (p c n0 V : Nat) (Q : State → Prop)
    (hfin : ∀ (s' : State) (n' : Nat), s'.mem = M → s'.regs 0 = BitVec.ofNat 64 p → s'.regs 1 = BitVec.ofNat 64 n' →
      s'.regs 2 = BitVec.ofNat 64 c → n' ≤ n0 → natVal M p n' = V → NatNorm M p n' → Q s')
    (hn0 : n0 ≤ c) (hc : c < 2 ^ 41) (hp : p + 8 * n0 ≤ 2 ^ 48) (hacc : M.accessible p (8 * n0) false = true)
    (hr1 : M.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat) (hr2 : M.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat)
    (hal : s.sp.toNat % 16 = 0) (hsp0 : 4256 ≤ s.sp.toNat) (hsp1 : s.sp.toNat + 64 ≤ 2 ^ 48)
    (hsacc : M.accessible (s.sp.toNat - 4256) (4256 + 64) true = true) (hl4 : (s.regs 30).toNat % 4 = 0)
    (hl48 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ (i : Nat) (S : State), i ≤ n0 → S.pc = BitVec.ofNat 64 hNorm → S.regs 1 = BitVec.ofNat 64 i →
      S.regs 0 = BitVec.ofNat 64 p → S.regs 2 = BitVec.ofNat 64 c → S.sp = s.sp - 160#64 →
      S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 168#64 → S.regs 18 = s.regs 18 → S.mem = M → natVal M p i = V →
      ReachesRet (LibLsh.program.link impl) (s.regs 30) S fun s' =>
        (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧ Q s' := by
  intro i
  induction i with
  | zero =>
    intro S hi hpc h1 h0 h2 hsp h28 h29 h18 hm hv
    have hc' : (c % 18446744073709551616) = c := Nat.mod_eq_of_lt (by omega)
    janus_run [hm, hr1, hr2, hc']
    refine hfin _ 0 rfl ?_ ?_ ?_ (Nat.zero_le _) (by simpa using hv) (Or.inl rfl)
    all_goals janus_simp
  | succ i ih =>
    intro S hi hpc h1 h0 h2 hsp h28 h29 h18 hm hv
    have key : BitVec.ofNat 64 (i + 1) - 1#64 = BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hc' : (c % 18446744073709551616) = c := Nat.mod_eq_of_lt (by omega)
    janus_run [hm, hr1, hr2, key, hc'] until [hNorm]
    · have hz : M.readLE (p + 8 * i) 8 = 0 := by rw [show p + 8 * i = p + i * 8 by omega]; janus_assumption
      exact ih _ (by omega) rfl (by janus_simp) (by janus_simp) (by janus_simp) rfl (by janus_simp) (by janus_simp)
        (by janus_simp) rfl ((natVal_drop_zero hz).symm.trans hv)
    · have hz : ¬M.readLE (p + i * 8) 8 = 0 := by janus_assumption
      refine hfin _ (i + 1) rfl ?_ ?_ ?_ hi hv (Or.inr ?_)
      all_goals try janus_simp
      rw [show p + 8 * i = p + i * 8 by omega]; exact hz

/-- `z[0 : q]` zero below `X · 2^r` at `q` gives `X · 2^(64 q + r)` -/
theorem val_clr (m : Memory) (p q xl X r : Nat) (h0 : m.readLE p (8 * q) = 0)
    (h1 : natVal m (p + 8 * q) (xl + 1) = X * 2 ^ r) :
    natVal m p (xl + q + 1) = X * 2 ^ (64 * q + r) := by
  rw [show xl + q + 1 = q + (xl + 1) by omega, natVal_add, h1]
  simp only [natVal] at h0 ⊢
  rw [h0, Nat.zero_add, Nat.pow_add]; ac_rfl

theorem shr6 (sh : Nat) (h : sh < 2 ^ 64) : BitVec.ofNat 64 sh >>> 6 = BitVec.ofNat 64 (sh / 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

/-- the slice-pointer mask `q & ((q - c) >> 63)` of `z[q:]` with `q < c` -/
theorem slice_mask (q c : Nat) (hq : q < c) (hc : c < 2 ^ 40) :
    (q &&& ((0#64 - (BitVec.ofNat 64 c - BitVec.ofNat 64 q)).sshiftRight 63).toNat) = q := by
  rw [BitArith.asr63_toNat]
  have e : (0#64 - (BitVec.ofNat 64 c - BitVec.ofNat 64 q)).toNat = 2 ^ 64 - (c - q) := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [e, if_neg (by omega), show (2 : Nat) ^ 64 - 1 = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem lsr6 (sh : Nat) (h : sh < 2 ^ 64) :
    (BitVec.ofNat 64 sh).rotateRight 6 &&& 18446744073709551615#64 &&& 288230376151711743#64 =
      BitVec.ofNat 64 (sh / 64) := by
  rw [TruncMath.rot6]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- from the clear point (memory `M2` after the shifted copy and `z[n]`) to the return, with the postcondition -/
theorem fromClr (impl : List Segment) (R : RtInv)
    (hmc : MemclrNoHeapPointersLive (LibLsh.program.link impl) (cA "runtime.memclrNoHeapPointers") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zc x xl sh : Nat)
    (s : State) (p c : Nat) (L' : List (Nat × Nat)) (b' : Nat) (M : Memory)
    (h : Mid R b L zp zc x xl sh s p c L' b' M)
    (M2 : Memory) (hF1 : MemFrame M M2 (R.rt ++ ws s p c)) (hLF1 : LiveFrame M M2 L' [(p, p + 8 * c)])
    (hinv2 : R.inv b' L' (s.regs 28).toNat (view R.rt L' M2))
    (hval : natVal M2 (p + 8 * (sh / 64)) (xl + 1) = natVal s.mem x xl * 2 ^ (sh % 64))
    (r24 : M2.readLE (s.sp.toNat - 24) 8 = p) (r48 : M2.readLE (s.sp.toNat - 48) 8 = need xl sh)
    (r80 : M2.readLE (s.sp.toNat - 80) 8 = c)
    (S : State) (hpc : S.pc = BitVec.ofNat 64 hClr) (h0 : S.regs 0 = BitVec.ofNat 64 p)
    (h1 : S.regs 1 = BitVec.ofNat 64 (need xl sh)) (h2 : S.regs 2 = BitVec.ofNat 64 c)
    (h6 : S.regs 6 = BitVec.ofNat 64 sh) (h8 : S.regs 8 = BitVec.ofNat 64 (sh / 64))
    (hsp : S.sp = s.sp - 160#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 168#64)
    (h18 : S.regs 18 = s.regs 18) (hm : S.mem = M2) :
    ReachesRet (LibLsh.program.link impl) (s.regs 30) S fun s' =>
      (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
        Post R b L zp zc x xl sh s s' := by
  have hsp0 := h.sp0; have hsp1 := h.sp1; have hcap := h.cap; have hc40 := h.c40; have hp48 := h.p48
  have hn16 := h.n16; have hal := h.al; have hl4 := h.lr4; have hl48 := h.lr48; have hwrt := h.wrt
  have hpw := h.pw; have hgw := h.gw
  simp only [need] at hcap hn16 r48 h1
  unfold Apart at hpw hgw
  have hws : ∀ a n, (s.sp.toNat - 168 ≤ a ∧ a + n ≤ s.sp.toNat - 152) → Outside a n (R.rt ++ ws s p c) := by
    intro a n ha
    simp only [ws, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h.wrt.of_sub (by omega) (by omega), by omega, by omega, by omega⟩
  have r1 : M2.readLE (s.sp.toNat - 160) 8 = (s.regs 30).toNat := by
    rw [hF1.readLE _ _ (hws _ _ (by omega))]; exact h.lr
  have r2 : M2.readLE (s.sp.toNat - 168) 8 = (s.regs 29).toNat := by
    rw [hF1.readLE _ _ (hws _ _ (by omega))]; exact h.fp
  have hsacc : M2.accessible (s.sp.toNat - 4256) (4256 + 64) true = true := by rw [hF1.accessible]; exact h.sacc
  have hpacc : M2.accessible p (8 * c) true = true := by rw [hF1.accessible]; exact h.pacc
  have hc41 : c < 2 ^ 41 := by omega
  have hsh : sh < 2 ^ 64 := by
    have := h.xl0; omega
  have hq := lsr6 sh hsh
  have hq' := shr6 sh hsh
  have hcm : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
  have hshv : 64 * (sh / 64) + sh % 64 = sh := by omega
  -- the final step: norm from `i = n + 1` and the postcondition
  have fin : ∀ (m : Memory) (S' : State), MemFrame M m (R.rt ++ ws s p c) → LiveFrame M m L' [(p, p + 8 * c)] →
      R.inv b' L' (s.regs 28).toNat (view R.rt L' m) → natVal m p (xl + sh / 64 + 1) = natVal s.mem x xl * 2 ^ sh →
      S'.pc = BitVec.ofNat 64 hNorm → S'.regs 1 = BitVec.ofNat 64 (xl + sh / 64 + 1) →
      S'.regs 0 = BitVec.ofNat 64 p → S'.regs 2 = BitVec.ofNat 64 c → S'.sp = s.sp - 160#64 →
      S'.regs 28 = s.regs 28 → S'.regs 29 = s.sp - 168#64 → S'.regs 18 = s.regs 18 → S'.mem = m →
      ReachesRet (LibLsh.program.link impl) (s.regs 30) S' fun s' =>
        (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
          Post R b L zp zc x xl sh s s' := by
    intro m S' hF hLF hinv hv hpc' h1' h0' h2' hsp' h28' h29' h18' hm'
    have hFr := hF1.readLE
    refine norm impl s m p c (xl + sh / 64 + 1) (natVal s.mem x xl * 2 ^ sh) _ ?_ hcap hc41 (by omega)
      (by rw [hF.accessible]; exact Memory.accessible_weaken _ (Memory.accessible_mono _ h.pacc (Nat.le_refl _)
        (by omega)))
      (by rw [hF.readLE _ _ (hws _ _ (by omega))]; exact h.lr) (by rw [hF.readLE _ _ (hws _ _ (by omega))]; exact h.fp)
      hal hsp0 hsp1 (by rw [hF.accessible]; exact h.sacc) hl4 hl48 _ S' (Nat.le_refl _) hpc' h1' h0' h2' hsp' h28'
      h29' h18' hm' hv
    intro s' n' hm'' h0'' h1'' h2'' hn' hv' hN
    exact h.post hF hLF hinv s' n' hm'' h0'' h1'' h2'' (by omega) hv' hN
  by_cases hq0 : sh / 64 = 0
  · have hq0' : BitVec.ofNat 64 (sh / 64) = 0#64 := by rw [hq0]
    rw [hq0'] at hq hq' h8
    janus_run [hm, hq, hq', hcm] until [hNorm]
    refine fin M2 _ hF1 hLF1 hinv2 ?v ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case v =>
      have := val_clr M2 p (sh / 64) xl (natVal s.mem x xl) (sh % 64) (by rw [hq0]; rfl) hval
      rwa [hshv] at this
    all_goals janus_simp
  · have hLs := h.lsep
    simp only [LiveSep, win] at hLs
    have hLs2 : ∀ r ∈ L', (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 160 - 4096 ∨ s.sp.toNat - 160 - 8 ≤ r.1) ∧
        (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 160 + 8 ∨ s.sp.toNat - 160 + 8 + 16 ≤ r.1) := by
      intro r hr; have := hLs r hr; simp only [outside_cons, outside_nil, and_true] at this; omega
    have hph : Held R L' p (8 * (sh / 64)) := h.pheld.sub (Nat.le_refl _) (by omega)
    have hph' : InRanges p (8 * (sh / 64)) L' ∨ Outside p (8 * (sh / 64)) R.rt := hph
    have hmc1 : ∀ d, R.ok (cA "runtime.memclrNoHeapPointers") [d, 8 * (sh / 64)] :=
      fun d => h.sv.2.2.1 d _ (by omega)
    have hpacc' : M2.accessible p (8 * (sh / 64)) true = true :=
      Memory.accessible_mono _ hpacc (Nat.le_refl _) (by omega)
    have hg48 : (s.regs 28).toNat ≤ 281474976710632 := by have := h.g48; omega
    have hgacc : M2.accessible ((s.regs 28).toNat + 16) 8 false = true := by rw [hF1.accessible]; exact h.gacc
    have hgok : M2.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 160 := by
      rw [hF1.readLE _ _ (by
        simp only [ws, outside_append, outside_cons, outside_nil, and_true]
        have := h.pg; unfold Apart at this
        refine ⟨h.grt, by omega, by omega, by omega⟩), h.grd]
      have := h.gok; omega
    have hq8 : 8 * (BitVec.ofNat 64 (sh / 64)).toNat % 18446744073709551616 = 8 * (sh / 64) := by
      simp only [BitVec.toNat_ofNat]; omega
    have hq0'' : (BitVec.ofNat 64 (sh / 64) = 0#64) = False := by
      simp only [eq_iff_iff, iff_false]; intro e
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
    janus_run [hm, hq, hcm, hq8, hq0'', r24, r48, r80, r1, r2] until [hNorm] calls [hmc]
    rename_i _ _ _ m _ _ hF2 hLF2 hinv3 hz
    have hz' := Expmc.readLE_zeroed hz
    refine fin m _ (hF1.trans hF2 fun a k ho => ?_) (hLF1.trans ⟨fun a k hin ho => ?_⟩ fun _ _ hh => hh) hinv3 ?v
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case v =>
      have hh : Held R L' (p + 8 * (sh / 64)) (8 * (xl + 1)) := h.pheld.sub (by omega) (by omega)
      have h1v : m.readLE (p + 8 * (sh / 64)) (8 * (xl + 1)) = M2.readLE (p + 8 * (sh / 64)) (8 * (xl + 1)) := by
        rcases hh with hin | hout
        · exact hLF2.readLE _ _ hin (by simp only [outside_cons, outside_nil, and_true]; omega)
        · exact hF2.readLE _ _ (by
            simp only [outside_append, outside_cons, outside_nil, and_true]
            exact ⟨⟨hout, by omega, by omega⟩, by omega⟩)
      have := val_clr m p (sh / 64) xl (natVal s.mem x xl) (sh % 64) hz' (by
        simp only [natVal] at hval ⊢; rw [h1v]; exact hval)
      rwa [hshv] at this
    · refine ⟨ho, ?_⟩
      simp only [ws, outside_append, outside_cons, outside_nil, and_true] at ho ⊢
      obtain ⟨hr, h1', h2', h3'⟩ := ho
      exact ⟨⟨hr, by omega, by omega⟩, by omega⟩
    · simp only [outside_cons, outside_nil, and_true] at ho
      exact hLF2.readLE a k hin (by simp only [outside_cons, outside_nil, and_true]; omega)
    all_goals janus_simp

end FvModexp.Arm64.Lsh
