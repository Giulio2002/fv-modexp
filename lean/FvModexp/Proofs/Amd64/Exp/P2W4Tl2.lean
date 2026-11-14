import FvModexp.Proofs.Amd64.Exp.P2W4Tl
import FvModexp.Proofs.Common.ExpNorm

set_option autoImplicit false

/-!
# `expNNPowerOfTwoWindowSize4` (amd64): the three exits up to the closure, and the main `z.norm()` loop
(agent divmc s76, port of divmc s69; amd64 twin of agent infra's `Arm64.P2W4Tail` `tailA/tailB/tailN` + the norm of `Arm64.P2W4X4`,
shaped like agent expmc's amd64 `W2Fin.tail`/`finIter`/`fin`)

* `tailM` (from `tM`, +0x8ef `CMPQ SI, DX`), `tailS` (from `tS`, +0x368: `AX := 1`, inline `norm` +0x952 of the
  one-word `[p] = 1`), `tailN` (from `tN`, +0x385): stores, `MOVB $0, 0x57(SP)`, the closure (`atD`), `RET`.
* `fin`: the inline `z.norm()` loop (nat.go:68-74, head `nH` +0x8e0 `TESTQ SI, SI`, back edge `DECQ SI` +0x8db) from
  `R8 = p`, `SI = l`, `DX = c`, then `tailM`; the result length is `Expmc.normL M p l`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts FvModexp

namespace FvModexp.Amd64.P2W4

/-- the main exit's norm loop head (`TESTQ SI, SI`, fn+0x8e0) -/
abbrev nH : Nat := 6200416

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- the main exit from `tM` (`CMPQ SI, DX`) to the return -/
theorem tailM {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (S : State) (sp g st n0 bp r p l c : Nat) (fsB : W64) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 tM) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = fsB) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h8 : S.regs 8 = BitVec.ofNat 64 p) (h6 : S.regs 6 = BitVec.ofNat 64 l) (hdx : S.regs 2 = BitVec.ofNat 64 c)
    (hmem : S.mem = M) (hlc : l ≤ c) (hc : c < 2 ^ 64) (hp : p < 2 ^ 64)
    (he : TEnv sp st n0 bp r M) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (TPost sp g st n0 bp p l c fsB M) := by
  obtain ⟨hal, hs1, hs2, hacc, r1c0, r1a0, r1a8, r1b0, hst1, hsta, hn0, hstw, r1c8, r1d0, hr47⟩ := he
  subst hmem
  have u := hstw; unfold Apart at u
  have hlt : ¬ (c < l) := by omega
  rw [show dwE = 6200800 from rfl] at r1a0
  janus64_run [r1c0, r1a0, hlt] until [6200800]
  refine atD hap _ sp g st n0 bp r p l c 6200478 fsB _ (Or.inr (Or.inr rfl)) rfl ?_ ?_ ?_ hfs hx15 rfl hs1 hs2 hal
    ?_ ?_ ?_ ?_ hst1 ?_ ?_ hstw ?_ ?_ ?_ ?_ ?_ hr47 ?_
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact bv_sub8 (by omega) (by omega)
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  · simp only [Arm64.Memory.accessible_writeLE]; exact hacc
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1a8
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1b0
  · simp only [Arm64.Memory.accessible_writeLE]; exact hsta
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact hn0
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1c8
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1d0
  · exact tw_wr (tw_wr (tw_wr (tw_wr (tw_wr (MemFrame.refl _ _) _ (by omega)) _ (by omega)) _ (by omega)) _
      (by omega)) _ (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `return 1` via `setWord` from `tS` (`[p] = 1` stored): `AX := 1`, the inline `norm`, to the return -/
theorem tailS {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (S : State) (sp g st n0 bp r p c : Nat) (fsB : W64) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 tS) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = fsB) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h6 : S.regs 6 = BitVec.ofNat 64 p) (h7 : S.regs 7 = BitVec.ofNat 64 c)
    (hmem : S.mem = M) (hc1 : 1 ≤ c) (hc : c < 2 ^ 64) (hp : p < 2 ^ 64)
    (hp1 : M.readLE p 8 = 1) (hpa : M.accessible p 8 false = true) (hp48 : p + 8 ≤ 2 ^ 48)
    (he : TEnv sp st n0 bp r M) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (TPost sp g st n0 bp p 1 c fsB M) := by
  obtain ⟨hal, hs1, hs2, hacc, r1c0, r1a0, r1a8, r1b0, hst1, hsta, hn0, hstw, r1c8, r1d0, hr47⟩ := he
  subst hmem
  have u := hstw; unfold Apart at u
  have hlt : ¬ (c < 1) := by omega
  have ea : p + 1 * 8 - 8 = p := by omega
  rw [show dwE = 6200800 from rfl] at r1a0
  have hm1 : (1#64).msb = false := by decide
  janus64_run [r1c0, r1a0, hlt, ea, hp1, hpa, hm1] until [6200800]
  refine atD hap _ sp g st n0 bp r p 1 c 6200596 fsB _ (Or.inr (Or.inl rfl)) rfl ?_ ?_ ?_ hfs hx15 rfl hs1 hs2 hal
    ?_ ?_ ?_ ?_ hst1 ?_ ?_ hstw ?_ ?_ ?_ ?_ ?_ hr47 ?_
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact bv_sub8 (by omega) (by omega)
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  · simp only [Arm64.Memory.accessible_writeLE]; exact hacc
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1a8
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1b0
  · simp only [Arm64.Memory.accessible_writeLE]; exact hsta
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact hn0
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1c8
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1d0
  · exact tw_wr (tw_wr (tw_wr (tw_wr (tw_wr (MemFrame.refl _ _) _ (by omega)) _ (by omega)) _ (by omega)) _
      (by omega)) _ (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- `return 1` via `newobject` from `tN` (`[p] = 1` stored, `AX = p`) to the return -/
theorem tailN {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (S : State) (sp g st n0 bp r p : Nat) (fsB : W64) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 tN) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = fsB) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h0 : S.regs 0 = BitVec.ofNat 64 p) (hmem : S.mem = M) (hp : p < 2 ^ 64)
    (he : TEnv sp st n0 bp r M) :
    ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S (TPost sp g st n0 bp p 1 1 fsB M) := by
  obtain ⟨hal, hs1, hs2, hacc, r1c0, r1a0, r1a8, r1b0, hst1, hsta, hn0, hstw, r1c8, r1d0, hr47⟩ := he
  subst hmem
  have u := hstw; unfold Apart at u
  rw [show dwE = 6200800 from rfl] at r1a0
  janus64_run [r1c0, r1a0] until [6200800]
  refine atD hap _ sp g st n0 bp r p 1 1 6198922 fsB _ (Or.inl rfl) rfl ?_ ?_ ?_ hfs hx15 rfl hs1 hs2 hal
    ?_ ?_ ?_ ?_ hst1 ?_ ?_ hstw ?_ ?_ ?_ ?_ ?_ hr47 ?_
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact bv_sub8 (by omega) (by omega)
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
  · simp only [Arm64.Memory.accessible_writeLE]; exact hacc
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1a8
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1b0
  · simp only [Arm64.Memory.accessible_writeLE]; exact hsta
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact hn0
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1c8
  · simp (disch := omega) only [Arm64.Memory.readLE_writeLE_of_disjoint, Arm64.Memory.readLE_writeLE_self,
      show (256 : Nat) ^ 8 = 2 ^ 64 from rfl, Nat.mod_eq_of_lt]; exact r1d0
  · exact tw_wr (tw_wr (tw_wr (tw_wr (tw_wr (MemFrame.refl _ _) _ (by omega)) _ (by omega)) _ (by omega)) _
      (by omega)) _ (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
set_option linter.janusRenameI false in
/-- one test of the main exit's inline `z.norm()` loop (nat.go:68-74) from `nH` with `SI = l` -/
theorem finIter {impl : List Amd64.Segment} {ret : W64} {Q : State → Prop}
    (S : State) (sp g p l c : Nat) (fsB : W64) (M : Memory)
    (hpc : S.rip = BitVec.ofNat 64 nH) (hsp : S.regs 4 = BitVec.ofNat 64 sp)
    (h14 : S.regs 14 = BitVec.ofNat 64 g) (hfs : S.fsBase = fsB) (hx15 : S.xmm 15 = 0) (hdf : S.df = false)
    (h8 : S.regs 8 = BitVec.ofNat 64 p) (h6 : S.regs 6 = BitVec.ofNat 64 l) (hdx : S.regs 2 = BitVec.ofNat 64 c)
    (hmem : S.mem = M) (hl : l < 2 ^ 48) (hp : p < 2 ^ 64)
    (hpa : l = 0 ∨ (p + 8 * l ≤ 2 ^ 48 ∧ M.accessible p (8 * l) false = true))
    (KT : ∀ S' : State, S'.rip = BitVec.ofNat 64 tM → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase = fsB → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 8 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 l → S'.regs 2 = BitVec.ofNat 64 c → S'.mem = M →
      (l = 0 ∨ M.readLE (p + 8 * (l - 1)) 8 ≠ 0) → ReachesRet (LibW.program.link impl) ret S' Q)
    (KL : ∀ S' : State, 0 < l → M.readLE (p + 8 * (l - 1)) 8 = 0 →
      S'.rip = BitVec.ofNat 64 nH → S'.regs 4 = BitVec.ofNat 64 sp →
      S'.regs 14 = BitVec.ofNat 64 g → S'.fsBase = fsB → S'.xmm 15 = 0 → S'.df = false →
      S'.regs 8 = BitVec.ofNat 64 p → S'.regs 6 = BitVec.ofNat 64 (l - 1) → S'.regs 2 = BitVec.ofNat 64 c →
      S'.mem = M → ReachesRet (LibW.program.link impl) ret S' Q) :
    ReachesRet (LibW.program.link impl) ret S Q := by
  subst hmem
  rcases hpa with hl0 | ⟨hp48, hacc⟩
  · subst hl0
    have hz : (BitVec.ofNat 64 0 : BitVec 64) = 0#64 := rfl
    janus64_run until [nH, tM]
    exact KT _ rfl hsp h14 hfs hx15 rfl h8 h6 hdx rfl (Or.inl rfl)
  · rcases l with _ | l
    · janus64_run until [nH, tM]
      exact KT _ rfl hsp h14 hfs hx15 rfl h8 h6 hdx rfl (Or.inl rfl)
    · have ea : p + (l + 1) * 8 - 8 = p + 8 * l := by omega
      have hms : (BitVec.ofNat 64 (l + 1)).msb = false := by
        rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
      janus64_run [ea, hms] until [nH, tM]
      · refine KL _ (by omega) (by simpa using hbr) rfl ?_ ?_ hfs hx15 rfl ?_ ?_ ?_ rfl
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hsp
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h8
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hdx
      · refine KT _ rfl ?_ ?_ hfs hx15 rfl ?_ ?_ ?_ rfl (Or.inr (by simpa using hbr))
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hsp
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h14
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h8
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact h6
        · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte]; exact hdx

/-- **the main exit**: the inline `z.norm()` loop from `nH`, then `tailM` -/
theorem fin {impl : List Amd64.Segment} (hap : Amd64.ImplApart Extracted.program impl)
    (sp g st n0 bp r p c : Nat) (fsB : W64) (M : Memory) (hc : c < 2 ^ 40) (hp : p < 2 ^ 64)
    (he : TEnv sp st n0 bp r M) :
    ∀ (l : Nat) (S : State), S.rip = BitVec.ofNat 64 nH → S.regs 4 = BitVec.ofNat 64 sp →
      S.regs 14 = BitVec.ofNat 64 g → S.fsBase = fsB → S.xmm 15 = 0 → S.df = false →
      S.regs 8 = BitVec.ofNat 64 p → S.regs 6 = BitVec.ofNat 64 l → S.regs 2 = BitVec.ofNat 64 c → S.mem = M →
      l ≤ c → (l = 0 ∨ (p + 8 * l ≤ 2 ^ 48 ∧ M.accessible p (8 * l) false = true)) →
      ReachesRet (LibW.program.link impl) (BitVec.ofNat 64 r) S
        (TPost sp g st n0 bp p (Expmc.normL M p l) c fsB M) := by
  intro l
  induction l with
  | zero =>
    intro S hpc hsp h14 hfs hx15 hdf h8 h6 hdx hmem hlc hpa
    refine finIter S sp g p 0 c fsB M hpc hsp h14 hfs hx15 hdf h8 h6 hdx hmem (by omega) hp (Or.inl rfl) ?_ ?_
    · intro S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 _
      exact tailM hap S' sp g st n0 bp r p 0 c fsB M a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (by omega) (by omega) hp he
    · intro _ h; omega
  | succ l ih =>
    intro S hpc hsp h14 hfs hx15 hdf h8 h6 hdx hmem hlc hpa
    obtain ⟨hp48, hacc⟩ := hpa.resolve_left (by omega)
    refine finIter S sp g p (l + 1) c fsB M hpc hsp h14 hfs hx15 hdf h8 h6 hdx hmem (by omega) hp
      (Or.inr ⟨hp48, hacc⟩) ?_ ?_
    · intro S' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hnz
      have hN : Expmc.normL M p (l + 1) = l + 1 := by
        simp only [Expmc.normL]; rw [if_neg]; simpa using hnz
      rw [hN]
      exact tailM hap S' sp g st n0 bp r p (l + 1) c fsB M a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hlc (by omega) hp he
    · intro S' _ hz a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
      have hN : Expmc.normL M p (l + 1) = Expmc.normL M p l := by
        simp only [Expmc.normL]; rw [if_pos (by simpa using hz)]
      rw [hN]
      exact ih S' a1 a2 a3 a4 a5 a6 a7 a8 (by simpa using a9) a10 (by omega)
        (Or.inr ⟨by omega, M.accessible_sub hacc (Or.inl rfl) (Nat.le_refl _) (by omega)⟩)

end FvModexp.Amd64.P2W4
