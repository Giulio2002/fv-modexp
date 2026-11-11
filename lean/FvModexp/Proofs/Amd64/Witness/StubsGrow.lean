import FvModexp.Proofs.Amd64.Witness.Stubs

/-!
# The general 8-byte `growslice` stub (amd64): `GrowsliceLiveContract64` for any request

amd64 twin of `Arm64/Witness/StubsGrow*.lean` (agent asm). The stub `WStubs.grCode64` (`scripts/grow-stub64.s`) is
proved in place at the contract address (`grA`) of the witness runtime `WStubs.P`, in stages:
`nsc_entry` (entry → `HAVE`, `R8 = nextslicecap newLen oldCap`), `chain` (`HAVE` → `ALLOC`, `R10 = roundupsize (8·c)`,
in chunks of size classes), `g_alloc` (`ALLOC` → return: bump allocation, `REP MOVSB` copy, live return).
-/

namespace FvModexp.Amd64.WStubs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Toy

set_option maxRecDepth 100000

abbrev gLOOP : Nat := 0x485435
abbrev gHAVE : Nat := 0x48544d
abbrev gLARGE : Nat := 0x485850
abbrev gALLOC : Nat := 0x48585f
abbrev gFWD : Nat := 0x485880
abbrev gBWDL : Nat := 0x4858a0
abbrev gDONE : Nat := 0x4858ba

/-- What the stub keeps until `ALLOC`. -/
def Pre0 (s T : State) : Prop :=
  T.regs 4 = s.regs 4 ∧ T.regs 5 = s.regs 5 ∧ T.regs 14 = s.regs 14 ∧ T.xmm 15 = s.xmm 15 ∧ T.fsBase = s.fsBase ∧
    T.df = s.df ∧ T.mxcsr = s.mxcsr ∧ T.x87 = s.x87 ∧ T.fpucw = s.fpucw ∧ T.mem = s.mem ∧
    T.regs 0 = s.regs 0 ∧ T.regs 3 = s.regs 3 ∧ T.regs 1 = s.regs 1 ∧ T.regs 7 = s.regs 7

macro "pre0_tac" : tactic =>
  `(tactic| (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | rfl | assumption | simp [setRegF, *]))

theorem go_step (n c : Nat) : nextslicecap.go n c =
    if c + (c + 3 * 256) / 4 ≥ n then c + (c + 3 * 256) / 4 else nextslicecap.go n (c + (c + 3 * 256) / 4) := by
  rw [nextslicecap.go]

/-- The `nextslicecap` loop (`c += (c + 768) / 4` until `c ≥ newLen`), from its head with `R8 = c < newLen`. -/
theorem nsc_loop (s : State) {Q : State → Prop} (tgt : Nat) (hn : (s.regs 3).toNat < 2 ^ 40)
    (hk : ∀ T, Pre0 s T → T.rip = BitVec.ofNat 64 gHAVE → (T.regs 8).toNat = tgt → ReachesRet P (retAddrOf s) T Q) :
    ∀ d (T : State) (c : Nat), (s.regs 3).toNat - c = d → c < (s.regs 3).toNat →
      nextslicecap.go (s.regs 3).toNat c = tgt → T.rip = BitVec.ofNat 64 gLOOP → Pre0 s T →
      (T.regs 8).toNat = c → ReachesRet P (retAddrOf s) T Q := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
  intro T c hd hc hgo hpc hP h8
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  rw [go_step] at hgo
  have hn3 : (T.regs 3).toNat = (s.regs 3).toNat := by rw [h3]
  have e7 : ((T.regs 8 + 768#64) >>> 2).toNat = (c + 768) / 4 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, h8, Nat.shiftRight_eq_div_pow]; simp; omega
  have ev : (T.regs 8 + (T.regs 8 + 768#64) >>> 2).toNat = c + (c + 768) / 4 := by
    rw [BitVec.toNat_add, e7, h8]; omega
  janus64_run until [gLOOP, gHAVE]
  · refine ih _ (by omega) _ (c + (c + 768) / 4) rfl (by omega) ?_ rfl (by pre0_tac) (by simpa [setRegF] using ev)
    rw [if_neg (by omega)] at hgo; exact hgo
  · refine hk _ (by pre0_tac) rfl ?_
    rw [if_pos (by omega)] at hgo; simpa [setRegF, ← hgo] using ev

/-- Entry to `HAVE`: `R8 = nextslicecap newLen oldCap`. -/
theorem nsc_entry (s : State) {Q : State → Prop} (hpc : s.rip = BitVec.ofNat 64 grA)
    (hlt : (s.regs 1).toNat < (s.regs 3).toNat) (hn : (s.regs 3).toNat < 2 ^ 40)
    (hk : ∀ T, Pre0 s T → T.rip = BitVec.ofNat 64 gHAVE →
      (T.regs 8).toNat = nextslicecap (s.regs 3).toNat (s.regs 1).toNat → ReachesRet P (retAddrOf s) T Q) :
    ReachesRet P (retAddrOf s) s Q := by
  have e2 : (s.regs 1 + s.regs 1).toNat = (s.regs 1).toNat + (s.regs 1).toNat := by
    rw [BitVec.toNat_add]; omega
  janus64_run until [gLOOP, gHAVE]
  · refine hk _ (by pre0_tac) rfl ?_
    simp only [setRegF, if_true]; unfold nextslicecap; rw [if_pos (by omega)]
  · rename_i hbr0
    refine hk _ (by pre0_tac) rfl ?_
    simp only [setRegF, if_true]; rw [e2]; unfold nextslicecap; rw [if_neg (by omega), if_pos hbr]
  · rename_i hbr0
    refine nsc_loop s _ hn hk _ _ _ rfl hlt ?_ rfl (by pre0_tac) (by simp [setRegF])
    unfold nextslicecap; rw [if_neg (by omega), if_neg hbr]

/-! ## Size-class arithmetic (adapted from `Arm64/Witness/StubsGrow.lean`, agent top) -/

theorem rs_small {size : Nat} (h : size ≤ 32760) : roundupsize size true = classSize size := by
  simp [roundupsize, maxSmallSize, mallocHeaderSize, h]

theorem rs_large {size : Nat} (h : 32760 < size) : roundupsize size true = (size + 8191) / 8192 * 8192 := by
  simp [roundupsize, maxSmallSize, mallocHeaderSize, pageSize]; omega

theorem fal_drop (n : Nat) : ∀ (l : List Nat) (k : Nat), (∀ x ∈ l.take k, x < n) →
    classSize.firstAtLeast l n = classSize.firstAtLeast (l.drop k) n
  | [], _, _ => by simp
  | _ :: _, 0, _ => rfl
  | c :: cs, k + 1, h => by
    have hc : c < n := h c (by simp)
    simp only [List.take_succ_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [classSize.firstAtLeast, List.drop_succ_cons, if_neg (show ¬ n ≤ c by omega)]
    exact fal_drop n cs k h.2

/-- The size class of `n` is the `k`-th class when the previous class is below `n` (classes increase). -/
theorem cs_leaf (k n c : Nat) (hc : sizeClasses.drop k = c :: sizeClasses.drop (k + 1))
    (hpre : ∀ x ∈ sizeClasses.take k, x < n) (hn0 : n ≠ 0) (hhi : n ≤ c) : classSize n = c := by
  unfold classSize
  rw [if_neg hn0, fal_drop n _ k hpre, hc]
  simp [classSize.firstAtLeast, hhi]

theorem fal_mod8 (n : Nat) (hn : n % 8 = 0) : ∀ l : List Nat, (∀ x ∈ l, x % 8 = 0) →
    classSize.firstAtLeast l n % 8 = 0
  | [], _ => hn
  | c :: cs, h => by
    simp only [classSize.firstAtLeast]
    split
    · exact h c (by simp)
    · exact fal_mod8 n hn cs fun x hx => h x (by simp [hx])

theorem rs_mod8 (x : Nat) (hx : x % 8 = 0) : roundupsize x true % 8 = 0 := by
  by_cases h : x ≤ 32760
  · rw [rs_small h]; unfold classSize; split
    · rfl
    · exact fal_mod8 x hx _ (by decide)
  · rw [rs_large (by omega)]; omega

theorem nsc_go_le (n : Nat) : ∀ c, c < n → nextslicecap.go n c ≤ n + n / 4 + 192 := by
  intro c
  induction c using nextslicecap.go.induct n with
  | case1 c c' h => intro hc; rw [nextslicecap.go]; simp only [c'] at h; simp [h]; omega
  | case2 c c' h ih => intro hc; rw [nextslicecap.go]; simp only [c'] at h ih; simp [h]; exact ih (by omega)

theorem nsc_le (n c0 : Nat) (h : c0 < n) : nextslicecap n c0 ≤ 2 * n + 768 := by
  unfold nextslicecap; split
  · omega
  · split
    · omega
    · have := nsc_go_le n c0 h; omega

/-- The round of the call: `8 · growCap8 = K`. -/
theorem round_eq (n c0 : Nat) : 8 * growCap8 n c0 = roundupsize (8 * nextslicecap n c0) true := by
  unfold growCap8
  rw [Nat.mul_comm (nextslicecap n c0) 8]
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (rs_mod8 _ (by omega)))

/-! ## `HAVE` → `ALLOC`: `R10 = roundupsize (8·c)` -/

/-- the continuation at `ALLOC` -/
abbrev KA (s : State) (c : Nat) (Q : State → Prop) : Prop :=
  ∀ U, Pre0 s U → U.rip = BitVec.ofNat 64 gALLOC → (U.regs 10).toNat = roundupsize (8 * c) true →
    ReachesRet P (retAddrOf s) U Q

set_option maxRecDepth 20000 in
/-- size classes 64…66 (from `C64`) -/
theorem chunk8 (s T : State) {Q : State → Prop} (c : Nat) (hpc : T.rip = BitVec.ofNat 64 0x485821)
    (hP : Pre0 s T) (h9 : (T.regs 9).toNat = 8 * c) (hlo : 24576 < 8 * c) (hhi : 8 * c ≤ 32760)
    (hk : KA s c Q) : ReachesRet P (retAddrOf s) T Q := by
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  have hc8 : 8 * c ≠ 0 := by omega
  janus64_run until [gALLOC]
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 64 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 24576 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 65 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 27264 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 66 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 28672 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  all_goals (exfalso; omega)

set_option maxRecDepth 20000 in
/-- size classes 56…63 (from `C56`) -/
theorem chunk7 (s T : State) {Q : State → Prop} (c : Nat) (hpc : T.rip = BitVec.ofNat 64 0x4857a9)
    (hP : Pre0 s T) (h9 : (T.regs 9).toNat = 8 * c) (hlo : 12288 < 8 * c) (hhi : 8 * c ≤ 32760)
    (hk : KA s c Q) : ReachesRet P (retAddrOf s) T Q := by
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  have hc8 : 8 * c ≠ 0 := by omega
  janus64_run until [gALLOC, 0x485821]
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 56 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 12288 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 57 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 13568 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 58 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 14336 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 59 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 16384 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 60 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 18432 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 61 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 19072 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 62 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 20480 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 63 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 21760 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · exact chunk8 s _ c rfl (by pre0_tac) (by simpa [setRegF] using h9) (by omega) hhi hk

set_option maxRecDepth 20000 in
/-- size classes 48…55 (from `C48`) -/
theorem chunk6 (s T : State) {Q : State → Prop} (c : Nat) (hpc : T.rip = BitVec.ofNat 64 0x485731)
    (hP : Pre0 s T) (h9 : (T.regs 9).toNat = 8 * c) (hlo : 6528 < 8 * c) (hhi : 8 * c ≤ 32760)
    (hk : KA s c Q) : ReachesRet P (retAddrOf s) T Q := by
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  have hc8 : 8 * c ≠ 0 := by omega
  janus64_run until [gALLOC, 0x4857a9]
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 48 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 6528 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 49 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 6784 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 50 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 6912 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 51 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 8192 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 52 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 9472 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 53 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 9728 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 54 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 10240 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 55 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 10880 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · exact chunk7 s _ c rfl (by pre0_tac) (by simpa [setRegF] using h9) (by omega) hhi hk

set_option maxRecDepth 20000 in
/-- size classes 40…47 (from `C40`) -/
theorem chunk5 (s T : State) {Q : State → Prop} (c : Nat) (hpc : T.rip = BitVec.ofNat 64 0x4856b9)
    (hP : Pre0 s T) (h9 : (T.regs 9).toNat = 8 * c) (hlo : 2688 < 8 * c) (hhi : 8 * c ≤ 32760)
    (hk : KA s c Q) : ReachesRet P (retAddrOf s) T Q := by
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  have hc8 : 8 * c ≠ 0 := by omega
  janus64_run until [gALLOC, 0x485731]
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 40 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 2688 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 41 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 3072 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 42 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 3200 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 43 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 3456 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 44 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 4096 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 45 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 4864 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 46 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 5376 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 47 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 6144 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · exact chunk6 s _ c rfl (by pre0_tac) (by simpa [setRegF] using h9) (by omega) hhi hk

set_option maxRecDepth 20000 in
/-- size classes 32…39 (from `C32`) -/
theorem chunk4 (s T : State) {Q : State → Prop} (c : Nat) (hpc : T.rip = BitVec.ofNat 64 0x485641)
    (hP : Pre0 s T) (h9 : (T.regs 9).toNat = 8 * c) (hlo : 1024 < 8 * c) (hhi : 8 * c ≤ 32760)
    (hk : KA s c Q) : ReachesRet P (retAddrOf s) T Q := by
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  have hc8 : 8 * c ≠ 0 := by omega
  janus64_run until [gALLOC, 0x4856b9]
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 32 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 1024 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 33 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 1152 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 34 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 1280 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 35 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 1408 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 36 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 1536 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 37 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 1792 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 38 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 2048 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 39 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 2304 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · exact chunk5 s _ c rfl (by pre0_tac) (by simpa [setRegF] using h9) (by omega) hhi hk

set_option maxRecDepth 20000 in
/-- size classes 24…31 (from `C24`) -/
theorem chunk3 (s T : State) {Q : State → Prop} (c : Nat) (hpc : T.rip = BitVec.ofNat 64 0x4855c9)
    (hP : Pre0 s T) (h9 : (T.regs 9).toNat = 8 * c) (hlo : 448 < 8 * c) (hhi : 8 * c ≤ 32760)
    (hk : KA s c Q) : ReachesRet P (retAddrOf s) T Q := by
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  have hc8 : 8 * c ≠ 0 := by omega
  janus64_run until [gALLOC, 0x485641]
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 24 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 448 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 25 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 480 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 26 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 512 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 27 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 576 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 28 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 640 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 29 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 704 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 30 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 768 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 31 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 896 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · exact chunk4 s _ c rfl (by pre0_tac) (by simpa [setRegF] using h9) (by omega) hhi hk

set_option maxRecDepth 20000 in
/-- size classes 16…23 (from `C16`) -/
theorem chunk2 (s T : State) {Q : State → Prop} (c : Nat) (hpc : T.rip = BitVec.ofNat 64 0x485551)
    (hP : Pre0 s T) (h9 : (T.regs 9).toNat = 8 * c) (hlo : 224 < 8 * c) (hhi : 8 * c ≤ 32760)
    (hk : KA s c Q) : ReachesRet P (retAddrOf s) T Q := by
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  have hc8 : 8 * c ≠ 0 := by omega
  janus64_run until [gALLOC, 0x4855c9]
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 16 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 224 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 17 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 240 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 18 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 256 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 19 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 288 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 20 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 320 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 21 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 352 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 22 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 384 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 23 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 416 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · exact chunk3 s _ c rfl (by pre0_tac) (by simpa [setRegF] using h9) (by omega) hhi hk

set_option maxRecDepth 20000 in
/-- size classes 8…15 (from `C8`) -/
theorem chunk1 (s T : State) {Q : State → Prop} (c : Nat) (hpc : T.rip = BitVec.ofNat 64 0x4854d9)
    (hP : Pre0 s T) (h9 : (T.regs 9).toNat = 8 * c) (hlo : 96 < 8 * c) (hhi : 8 * c ≤ 32760)
    (hk : KA s c Q) : ReachesRet P (retAddrOf s) T Q := by
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  have hc8 : 8 * c ≠ 0 := by omega
  janus64_run until [gALLOC, 0x485551]
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 8 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 96 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 9 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 112 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 10 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 128 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 11 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 144 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 12 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 160 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 13 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 176 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 14 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 192 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 15 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 208 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · exact chunk2 s _ c rfl (by pre0_tac) (by simpa [setRegF] using h9) (by omega) hhi hk

set_option maxRecDepth 20000 in
/-- size classes 0…7 (from `C0`) -/
theorem chunk0 (s T : State) {Q : State → Prop} (c : Nat) (hpc : T.rip = BitVec.ofNat 64 0x485461)
    (hP : Pre0 s T) (h9 : (T.regs 9).toNat = 8 * c) (hlo : 0 < 8 * c) (hhi : 8 * c ≤ 32760)
    (hk : KA s c Q) : ReachesRet P (retAddrOf s) T Q := by
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  have hc8 : 8 * c ≠ 0 := by omega
  janus64_run until [gALLOC, 0x4854d9]
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 0 _ _ (by decide) (fun x hx => absurd hx (by simp)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 1 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 8 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 2 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 16 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 3 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 24 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 4 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 32 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 5 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 48 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 6 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 64 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · refine hk _ (by pre0_tac) rfl ?_
    rw [rs_small (by omega)]; simp only [setRegF, if_true, BitVec.toNat_ofNat]
    exact (cs_leaf 7 _ _ (by decide) (fun x hx => Nat.lt_of_le_of_lt (show x ≤ 80 by revert x hx; decide) (by omega)) hc8 (by omega)).symm
  · exact chunk1 s _ c rfl (by pre0_tac) (by simpa [setRegF] using h9) (by omega) hhi hk

theorem large_val (x : BitVec 64) (hx : x.toNat < 2 ^ 50) :
    (((x + 8191#64) >>> 13) <<< 13).toNat = (x.toNat + 8191) / 8192 * 8192 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := x.toNat + 8191) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem shl3_val (x : BitVec 64) (hx : x.toNat < 2 ^ 50) : (x <<< 3).toNat = 8 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega

/-- `HAVE` to `ALLOC`: `R10 = roundupsize (8 c) true` (page rounding, or the size-class chunks). -/
theorem chain (s T : State) {Q : State → Prop} (c : Nat) (hpc : T.rip = BitVec.ofNat 64 gHAVE)
    (hP : Pre0 s T) (h8 : (T.regs 8).toNat = c) (hc0 : 0 < c) (hc : c < 2 ^ 42) (hk : KA s c Q) :
    ReachesRet P (retAddrOf s) T Q := by
  have hP' := hP
  obtain ⟨h4, h5, h14, hx, hfs, hdf, hmx, h87, hfw, hm, h0, h3, h1, h7⟩ := hP
  have e9 : (T.regs 8 <<< 3).toNat = 8 * c := by rw [shl3_val _ (by omega), h8]
  janus64_run until [gALLOC, 0x485461]
  · refine hk _ (by pre0_tac) rfl ?_
    simp only [setRegF, if_true, ite_true]
    rw [large_val _ (by rw [e9]; omega), e9, rs_large (by omega)]
  · exact chunk0 s _ c rfl (by pre0_tac) (by simpa [setRegF] using e9) (by omega) (by omega) hk

/-! ## The copy loops (`FWD` / `BWDL`) -/

open Janus.Contracts.MemSat (toNat_add_one toNat_sub_one byte_copy)

/-- What the copy keeps: the ABI fields, `RBX` (`newLen`), `R10` (`K`), `R11` (`BUMP`), `R12` (`p`). -/
def CK (s : State) (v10 v12 : W64) (T : State) : Prop :=
  T.regs 4 = s.regs 4 ∧ T.regs 5 = s.regs 5 ∧ T.regs 14 = s.regs 14 ∧ T.xmm 15 = s.xmm 15 ∧ T.fsBase = s.fsBase ∧
    T.df = s.df ∧ T.mxcsr = s.mxcsr ∧ T.x87 = s.x87 ∧ T.fpucw = s.fpucw ∧ T.regs 3 = s.regs 3 ∧
    T.regs 10 = v10 ∧ T.regs 11 = 4194304#64 ∧ T.regs 12 = v12

macro "ck_tac" : tactic =>
  `(tactic| (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | rfl | assumption | simp [setRegF, *]))

theorem byte_copy' (m : Memory) (a : Nat) {a' : Nat} :
    BitVec.ofNat 8 (m.readLE a 1 / 256 ^ (a' - a')) = m.bytes a := by
  have := (m.bytes a).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Janus.Arm64.Memory.readLE_one, Nat.sub_self, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat]
  omega

theorem g_fwd (s : State) (v10 v12 : W64) {Q : State → Prop} (d src n : Nat)
    (hsrc : n = 0 ∨ s.mem.accessible src n false = true) (hdst : s.mem.accessible d n true = true)
    (hsrc48' : 0 < n → src + n ≤ 2 ^ 48) (hle : d ≤ src)
    (hk : ∀ T, T.rip = BitVec.ofNat 64 gDONE → CK s v10 v12 T → MemFrame s.mem T.mem [(d, d + n)] →
      Mem.Copied s.mem T.mem d src n → ReachesRet P (retAddrOf s) T Q) :
    ∀ k (T : State) (i : Nat), i + k = n → T.rip = BitVec.ofNat 64 gFWD →
      (T.regs 7).toNat = d + i → (T.regs 6).toNat = src + i → (T.regs 1).toNat = k → CK s v10 v12 T →
      MemFrame s.mem T.mem [(d, d + i)] → Mem.Copied s.mem T.mem d src i →
      ReachesRet P (retAddrOf s) T Q := by
  have hbd := Janus.Arm64.Memory.accessible_bound _ hdst
  intro k
  induction k with
  | zero =>
    intro T i hi hpc h7 h6 h1 hK hf hc
    have h1' : T.regs 1 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
    janus64_run until [gDONE]
    exact hk _ rfl (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK; ck_tac) (by rw [← hi, Nat.add_zero]; exact hf)
      (by rw [← hi, Nat.add_zero]; exact hc)
  | succ k ih =>
    intro T i hi hpc h7 h6 h1 hK hf hc
    have h1' : T.regs 1 ≠ 0#64 := fun h => by simp [h] at h1
    have hsrcA : s.mem.accessible src n false = true := hsrc.resolve_left (by omega)
    have hsrc48 := hsrc48' (by omega)
    have hr : T.mem.accessible (T.regs 6).toNat 1 false = true := by
      rw [hf.accessible, h6]; exact Janus.Arm64.Memory.accessible_mono _ hsrcA (by omega) (by omega)
    have hw : T.mem.accessible (T.regs 7).toNat 1 true = true := by
      rw [hf.accessible, h7]; exact Janus.Arm64.Memory.accessible_mono _ hdst (by omega) (by omega)
    janus64_run until [gFWD]
    have e0 : (T.regs 7 + 1#64).toNat = d + (i + 1) := by rw [toNat_add_one (by omega), h7]; omega
    have e1 : (T.regs 6 + 1#64).toNat = src + (i + 1) := by rw [toNat_add_one (by omega), h6]; omega
    refine ih _ (i + 1) (by omega) rfl (by simpa [setRegF] using e0) (by simpa [setRegF] using e1)
      (by simpa [setRegF] using toNat_sub_one h1)
      (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK; ck_tac) ?_ ?_
    · rw [h7]
      refine (hf.mono fun a n h => ?_).writeLE _ (List.mem_singleton_self _) (by simp <;> omega) (by simp <;> omega)
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
    · intro j hj
      rw [h7, h6]
      by_cases hji : j = i
      · subst hji
        rw [Janus.Arm64.Memory.bytes_writeLE_inside _ (by omega) (by omega)]
        first | exact byte_copy' _ _ | exact byte_copy _ _
      · rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]; exact hc j (by omega)

theorem g_bwd (s : State) (v10 v12 : W64) {Q : State → Prop} (d src n : Nat)
    (hsrc' : n = 0 ∨ s.mem.accessible src n false = true) (hsrc48' : 0 < n → src + n ≤ 2 ^ 48)
    (hdst : s.mem.accessible d n true = true) (hlt : src < d)
    (hk : ∀ T, T.rip = BitVec.ofNat 64 gDONE → CK s v10 v12 T → MemFrame s.mem T.mem [(d, d + n)] →
      Mem.Copied s.mem T.mem d src n → ReachesRet P (retAddrOf s) T Q) :
    ∀ k (T : State), k ≤ n → T.rip = BitVec.ofNat 64 gBWDL →
      (T.regs 7).toNat = d + k → (T.regs 6).toNat = src + k → (T.regs 1).toNat = k → CK s v10 v12 T →
      MemFrame s.mem T.mem [(d + k, d + n)] →
      (∀ j, k ≤ j → j < n → T.mem.bytes (d + j) = s.mem.bytes (src + j)) →
      ReachesRet P (retAddrOf s) T Q := by
  have hbd := Janus.Arm64.Memory.accessible_bound _ hdst
  intro k
  induction k with
  | zero =>
    intro T hk0 hpc h7 h6 h1 hK hf hc
    have h1' : T.regs 1 = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
    janus64_run until [gDONE]
    exact hk _ rfl (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK; ck_tac) (by simpa using hf)
      (fun j hj => hc j (Nat.zero_le _) hj)
  | succ k ih =>
    intro T hk0 hpc h7 h6 h1 hK hf hc
    have h1' : T.regs 1 ≠ 0#64 := fun h => by simp [h] at h1
    have hsrc : s.mem.accessible src n false = true := hsrc'.resolve_left (by omega)
    have hsrc48 := hsrc48' (by omega)
    have hbs := Janus.Arm64.Memory.accessible_bound _ hsrc
    have e2 := toNat_sub_one h1
    have ea : (T.regs 6 - 1#64).toNat = src + k := toNat_sub_one (by omega)
    have eb : (T.regs 7 - 1#64).toNat = d + k := toNat_sub_one (by omega)
    have hr : T.mem.accessible (T.regs 6 - 1#64).toNat 1 false = true := by
      rw [hf.accessible, ea]; exact Janus.Arm64.Memory.accessible_mono _ hsrc (by omega) (by omega)
    have hw : T.mem.accessible (T.regs 7 - 1#64).toNat 1 true = true := by
      rw [hf.accessible, eb]; exact Janus.Arm64.Memory.accessible_mono _ hdst (by omega) (by omega)
    janus64_run until [gBWDL]
    refine ih _ (by omega) rfl (by simpa [setRegF] using eb) (by simpa [setRegF] using ea)
      (by simpa [setRegF] using e2)
      (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hK; ck_tac) ?_ ?_
    · refine (hf.mono fun a n h => ?_).writeLE _ (List.mem_singleton_self _) (by simp <;> omega) (by simp <;> omega)
      simp only [outside_cons, outside_nil, and_true] at h ⊢; omega
    · intro j hj1 hj2
      by_cases hji : j = k
      · subst hji
        rw [Janus.Arm64.Memory.bytes_writeLE_inside _ (by omega) (by omega)]
        rw [show (T.regs 6).toNat - 1 = src + j by omega, show d + j = (T.regs 7).toNat - 1 by omega]
        exact byte_copy' _ _
      · rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]; exact hc j (by omega) hj2

end FvModexp.Amd64.WStubs
