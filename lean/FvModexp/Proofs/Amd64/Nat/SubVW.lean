import FvModexp.Proofs.Amd64.Nat.LibSubVW
import FvModexp.Proofs.Amd64.Nat.Callees
import FvModexp.Proofs.Common.AsmVW

/-!
# `math/big.subVW(z, x []Word, y Word) (c Word)` (go-bigmodexpfix arith.go:157, Go ABIInternal, amd64)

The amd64 twin of `FvModexp.Arm64.SubVW` and of `FvModexp.Amd64.AddVW` (same frame and `copy` code; `SUB`/`SBB`, the
borrow loop `TEST R9, R9`/`DEC R9`). Segments: `ret0` (`+0x91`, `+0x11e`), `copy` (`+0x83`, `+0x10d`), loop head `+0xad`.
Result: `c = y` for `len z = 0`, else the borrow `[x < y]`; `z = (x + B^n - y) mod B^n`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open FvModexp.Amd64.Callees Janus.Contracts.EqHashModel

namespace FvModexp.Amd64.SubVW

set_option linter.unusedSimpArgs false
set_option linter.janusRenameI false

def fn : String := "github.com/ethereum/go-bigmodexpfix/src/math/big.subVW"
def names : List String := [fn]

abbrev entry : Nat := segAddr Extracted.program fn

/-- the precondition (`xl = zl` separately) -/
@[reducible] def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xc : BitVec 64) (s : State) : Prop :=
  CallEnvND R L s 4136 40 ∧ zl.toNat ≤ zc.toNat ∧ zl.toNat ≤ xc.toNat ∧ zc.toNat < 2 ^ 63 ∧ xc.toNat < 2 ^ 63 ∧
    NatLive s.mem R L zp.toNat zl.toNat ∧ Outside zp.toNat (8 * zl.toNat) (win s 4136 40) ∧
    (0 < zl.toNat → Apart zp.toNat (8 * zl.toNat) ((s.regs 14).toNat + 16) 8 ∧
      Apart zp.toNat (8 * zl.toNat) (s.fsBase.toNat - 8) 8) ∧
    s.mem.accessible xp.toNat (8 * zl.toNat) false = true ∧ xp.toNat + 8 * zl.toNat ≤ 2 ^ 48 ∧
    Held R L xp.toNat (8 * zl.toNat) ∧ Outside xp.toNat (8 * zl.toNat) (win s 4136 40) ∧
    (zp = xp ∨ Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * zl.toNat)) ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
    (if zp = xp then True else VWMoves R zp.toNat zl.toNat zc.toNat xp.toNat xc.toNat)

/-- the postcondition -/
@[reducible] def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (zp zl xp y : BitVec 64) (s s' : State) : Prop :=
  s'.fsBase = s.fsBase ∧ s'.df = s.df ∧
    (s'.regs 0).toNat =
      (if zl.toNat = 0 then y.toNat else if natVal s.mem xp.toNat zl.toNat < y.toNat then 1 else 0) ∧
    natVal s'.mem zp.toNat zl.toNat =
      (natVal s.mem xp.toNat zl.toNat + 2 ^ (64 * zl.toNat) - y.toNat) % 2 ^ (64 * zl.toNat) ∧
    ∃ (L' : List (Nat × Nat)) (b' : Nat), LiveExt R L L' ∧ b ≤ b' ∧
      R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧
      MemFrame s.mem s'.mem (R.rt ++ win s 4136 40 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
      LiveFrame s.mem s'.mem L [(zp.toNat, zp.toNat + 8 * zl.toNat)]

/-- a segment-boundary state `S` (inside the frame) against the call state `s`; `k` limbs of `z` written -/
structure Rel (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret zp k : Nat) (s S : State) : Prop where
  sp : S.regs 4 = s.regs 4 - 32#64
  fp : S.regs 5 = s.regs 4 - 8#64
  g : S.regs 14 = s.regs 14
  x15 : S.xmm 15 = s.xmm 15
  x15z : s.xmm 15 = 0#128
  df : S.df = false
  fs : S.fsBase = s.fsBase
  lr : S.mem.readLE (s.regs 4).toNat 8 = ret
  sfp : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  mf : MemFrame s.mem S.mem (R.rt ++ win s 4136 40 ++ [(zp, zp + 8 * k)])
  lf : LiveFrame s.mem S.mem L [(zp, zp + 8 * k)]
  inv : R.inv b L (s.regs 14).toNat (view R.rt L S.mem)
  df0 : s.df = false

theorem liveFrame_mono {m m' : Memory} {L ws ws' : List (Nat × Nat)} (h : LiveFrame m m' L ws)
    (hs : ∀ a n, Outside a n ws' → Outside a n ws) : LiveFrame m m' L ws' :=
  ⟨fun a n hin ho => h.readLE a n hin (hs a n ho)⟩

theorem out_all {a n : Nat} {L : List (Nat × Nat)} (h : ∀ r ∈ L, a + n ≤ r.1 ∨ r.2 ≤ a) : Outside a n L := by
  induction L with
  | nil => trivial
  | cons r L ih =>
    exact ⟨by have := h r (by simp); omega, ih fun q hq => h q (by simp [hq])⟩

theorem out_z {a n zp k k' : Nat} (hk : k ≤ k') (rt ws : List (Nat × Nat))
    (h : Outside a n (rt ++ ws ++ [(zp, zp + 8 * k')])) : Outside a n (rt ++ ws ++ [(zp, zp + 8 * k)]) := by
  rw [outside_append, outside_append] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  revert h2
  try simp only [outside_cons, outside_nil, and_true]
  omega

set_option maxRecDepth 20000 in
/-- the epilogue returning `0`, from a state whose `z` holds `x + y` (no carry out) -/
theorem ret0 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (S : State) (k : Nat) (hk : k ≤ zl.toNat) (hz : 0 < zl.toNat)
    (hrel : Rel R b L ret zp.toNat k s S)
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x91) ∨ S.rip = BitVec.ofNat 64 (entry + 0x11e))
    (hval : natVal S.mem zp.toNat zl.toNat + y.toNat = natVal s.mem xp.toNat zl.toNat) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, htls⟩, -⟩ := hpre
  obtain ⟨hsp, h5, h14, h15, hx15, hdf, hfs, h_rd_lr, h_rd_fp, hmf, hlf, hinv, hdfR⟩ := hrel
  try simp only [regSP] at hb' ha hw
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 32 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hacc : S.mem.accessible ((s.regs 4).toNat - 4136) (4136 + 40) true = true := by rw [hmf.accessible]; exact hw
  have hZ := natVal_lt s.mem xp.toNat zl.toNat
  have hZ' := natVal_lt S.mem zp.toNat zl.toNat
  have hP : 0 < 2 ^ (64 * zl.toNat) := Nat.two_pow_pos _
  rcases hpc with hpc | hpc
  all_goals
    janus64_run
    refine ⟨hfs, hdfR.symm, ?_, ?_, L, b, LiveExt.refl R L, Nat.le_refl _, hinv,
      ⟨fun a n h => hmf.readLE a n (out_z hk _ _ h), hmf.accessible⟩,
      liveFrame_mono hlf (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)⟩
    · rw [if_neg (by omega), if_neg (by omega)]; rfl
    · rw [show natVal s.mem xp.toNat zl.toNat + 2 ^ (64 * zl.toNat) - y.toNat =
        natVal S.mem zp.toNat zl.toNat + 2 ^ (64 * zl.toNat) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hZ']

theorem val_split (m : Memory) (p j n : Nat) (h : j ≤ n) :
    m.readLE p (8 * n) = m.readLE p (8 * j) + 2 ^ (64 * j) * m.readLE (p + 8 * j) (8 * (n - j)) := by
  rw [show 8 * n = 8 * j + 8 * (n - j) by omega, Janus.Arm64.Memory.readLE_add,
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
    (hMF : MemFrame S.mem m (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat - 8)] ++
      [(D.toNat, D.toNat + 8 * N.toNat)]))
    (hLF : LiveFrame S.mem m L [(D.toNat, D.toNat + 8 * N.toNat)])
    (hCP : Mem.Copied S.mem m D.toNat Sr.toNat (8 * N.toNat)) :
    m.readLE (s.regs 4).toNat 8 = ret ∧ m.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
      MemFrame s.mem m (R.rt ++ win s 4136 40 ++ [(zp.toNat, zp.toNat + 8 * zl.toNat)]) ∧
      LiveFrame s.mem m L [(zp.toNat, zp.toNat + 8 * zl.toNat)] ∧
      natVal m zp.toNat zl.toNat + y.toNat = natVal s.mem xp.toNat zl.toNat := by
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, htls⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre
  simp only [regSP] at hb' ha hw
  obtain ⟨hsp, h5, h14, h15, hx15, hdf, hfs, h_rd_lr, h_rd_fp, hmf, hlf, hinv, hdfR⟩ := hrel
  have hzx' : Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * zl.toNat) := hzx.resolve_left hne
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw hxw
  unfold Apart at hzx'
  have hDr : zp.toNat ≤ D.toNat ∧ D.toNat + 8 * N.toNat ≤ zp.toNat + 8 * zl.toNat ∧
      (zp.toNat + 8 * j ≤ D.toNat ∨ D.toNat + 8 * N.toNat ≤ zp.toNat) := by
    rw [hD, hN]; split <;> omega
  have hMF' : MemFrame S.mem m (R.rt ++ ([((s.regs 4).toNat - 4136, (s.regs 4).toNat - 8)] ++
      [(D.toNat, D.toNat + 8 * N.toNat)])) := by
    rw [← List.append_assoc]; exact hMF
  have hmf' : MemFrame s.mem S.mem (R.rt ++ (win s 4136 40 ++ [(zp.toNat, zp.toNat + 8 * j)])) := by
    rw [← List.append_assoc]; exact hmf
  have hLF' : LiveFrame S.mem m L ([((s.regs 4).toNat - 4136, (s.regs 4).toNat - 8)] ++
      [(D.toNat, D.toNat + 8 * N.toNat)]) :=
    liveFrame_mono hLF (fun a n h => by rw [outside_append] at h; exact h.2)
  have hlf' : LiveFrame s.mem S.mem L (win s 4136 40 ++ [(zp.toNat, zp.toNat + 8 * j)]) :=
    liveFrame_mono hlf (fun a n h => by rw [outside_append] at h; exact h.2)
  have hsk : ∀ a n, (s.regs 4).toNat - 8 ≤ a → a + n ≤ (s.regs 4).toNat + 8 →
      Outside a n (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat - 8)] ++ [(D.toNat, D.toNat + 8 * N.toNat)]) := by
    intro a n h1 h2
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨Outside.of_sub hout (by omega) (by omega), by omega⟩, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hMF.readLE _ _ (hsk _ _ (by omega) (by omega))]; exact h_rd_lr
  · rw [hMF.readLE _ _ (hsk _ _ (by omega) (by omega))]; exact h_rd_fp
  · refine MemFrame.trans hmf hMF (fun a n h => ?_)
    simp only [outside_append, outside_cons, outside_nil, and_true, win] at h ⊢
    obtain ⟨⟨hr, h1⟩, h3⟩ := h
    exact ⟨⟨⟨hr, h1⟩, by omega⟩, ⟨hr, by omega⟩, by omega⟩
  · exact LiveFrame.trans (liveFrame_mono hlf (fun a n h => by
        simp only [outside_cons, outside_nil, and_true] at h ⊢; omega))
      (liveFrame_mono hLF (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega))
      (fun _ _ h => h)
  · have hlow : m.readLE zp.toNat (8 * j) = S.mem.readLE zp.toNat (8 * j) :=
      Held.readLE (hzh.sub (Nat.le_refl _) (by omega)) hMF' hLF' (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        refine ⟨by omega, by omega⟩)
    show m.readLE zp.toNat (8 * zl.toNat) + y.toNat = s.mem.readLE xp.toNat (8 * zl.toNat)
    rw [val_split m zp.toNat j zl.toNat hj, val_split s.mem xp.toNat j zl.toNat hj, hlow]
    have hv : S.mem.readLE zp.toNat (8 * j) + y.toNat = s.mem.readLE xp.toNat (8 * j) := hval
    by_cases hjl : j = zl.toNat
    · subst hjl; simp only [Nat.sub_self, Nat.mul_zero, Janus.Arm64.Memory.readLE_zero]; omega
    have hjz : j < zc.toNat := by omega
    have hjx : j < xc.toNat := by omega
    simp only [hjz, hjx, ite_true] at hD hS
    have hc := FvModexp.Asm.readLE_of_copied hCP
    rw [hD, hS, hN] at hc
    have hx : S.mem.readLE (xp.toNat + 8 * j) (8 * (zl.toNat - j)) = s.mem.readLE (xp.toNat + 8 * j) (8 * (zl.toNat - j)) :=
      Held.readLE (hxh.sub (by omega) (by omega)) hmf' hlf' (by
        simp only [outside_append, win, outside_cons, outside_nil, and_true]
        first | exact ⟨by omega, by omega⟩ | omega)
    rw [hc, hx]; omega


/-- the `CALL`'s push of its return address (at `a`, inside the caller's window) folded into the callee frame -/
theorem call_norm {S m : Memory} {rt L : List (Nat × Nat)} {a v d n src : Nat}
    (hMF : MemFrame (S.writeLE a 8 v) m (rt ++ [(a - 4096, a), (a + 8, a + 8 + 24)] ++ [(d, d + n)]))
    (hLF : LiveFrame (S.writeLE a 8 v) m L [(d, d + n)])
    (hCP : Mem.Copied (S.writeLE a 8 v) m d src n) (hsrc : src + n ≤ a ∨ a + 8 ≤ src) (haL : Outside a 8 L) :
    MemFrame S m (rt ++ [(a - 4096, a + 32)] ++ [(d, d + n)]) ∧ LiveFrame S m L [(d, d + n)] ∧
      Mem.Copied S m d src n := by
  refine ⟨⟨fun b k h => ?_, fun b k w => by rw [hMF.accessible, Janus.Arm64.Memory.accessible_writeLE]⟩, ?_, ?_⟩
  · simp only [outside_append, outside_cons, outside_nil, and_true] at h
    have ho : Outside b k (rt ++ [(a - 4096, a), (a + 8, a + 8 + 24)] ++ [(d, d + n)]) := by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨⟨h.1.1, by omega, by omega⟩, h.2⟩
    rw [hMF.readLE b k ho, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  · exact LiveFrame.trans (LiveFrame.writeLE (LiveFrame.refl S L [(d, d + n)]) v haL) hLF (fun _ _ h => h)
  · intro i hi
    rw [hCP i hi, Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]

set_option maxRecDepth 20000 in
/-- a store of limb `i` of `z` keeps `Rel` (now `i + 1` limbs written) -/
theorem rel_store (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl zc xp xc : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (S : State) (i : Nat) (hi : i < zl.toNat)
    (hrel : Rel R b L ret zp.toNat i s S) (v : Nat) (S' : State) (hsp : S'.regs 4 = S.regs 4)
    (h5 : S'.regs 5 = S.regs 5) (h14 : S'.regs 14 = S.regs 14) (h15 : S'.xmm 15 = S.xmm 15) (hdf : S'.df = false)
    (hfs : S'.fsBase = S.fsBase)
    (hm : S'.mem = S.mem.writeLE (zp.toNat + i * 8) 8 v) : Rel R b L ret zp.toNat (i + 1) s S' := by
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, htls⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre
  try simp only [regSP] at hb' ha hw
  obtain ⟨hsp0, h50, h140, h150, hx15, hdf0, hfs0, h_rd_lr, h_rd_fp, hmf, hlf, hinv, hdfR⟩ := hrel
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  simp only [Outside, and_true] at hzw
  refine ⟨hsp.trans hsp0, h5.trans h50, h14.trans h140, h15.trans h150, hx15, hdf, hfs.trans hfs0,
    ?_, ?_, ?_, ?_, ?_, hdfR⟩
  · rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h_rd_lr
  · rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h_rd_fp
  · rw [hm]
    refine ⟨fun a n h => ?_, fun a n w => by rw [Janus.Arm64.Memory.accessible_writeLE]; exact hmf.accessible a n w⟩
    have h' := h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h'
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
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
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, htls⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre
  try simp only [regSP] at hb' ha hw
  obtain ⟨hsp0, h50, h140, h150, hx15, hdf0, hfs0, h_rd_lr, h_rd_fp, hmf, hlf, hinv, hdfR⟩ := hrel
  have hmf' : MemFrame s.mem S.mem (R.rt ++ (win s 4136 40 ++ [(zp.toNat, zp.toNat + 8 * k)])) := by
    rw [← List.append_assoc]; exact hmf
  have hlf' : LiveFrame s.mem S.mem L (win s 4136 40 ++ [(zp.toNat, zp.toNat + 8 * k)]) :=
    liveFrame_mono hlf (fun a n h => by rw [outside_append] at h; exact h.2)
  simp only [Outside, and_true] at hxw
  refine Held.readLE (hxh.sub (by omega) (by omega)) hmf' hlf' ?_
  simp only [outside_append, win, outside_cons, outside_nil, and_true]
  refine ⟨by omega, ?_⟩
  rcases hzx with h | h
  · have := hk h; subst h; omega
  · unfold Apart at h; omega

set_option maxRecDepth 20000 in
/-- the return of `copy`'s `memmove` (`retState64`), handed to `ret0` -/
theorem cont (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hne : zp ≠ xp) (S : State) (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ zl.toNat)
    (hrel : Rel R b L ret zp.toNat j s S) (D Sr N : BitVec 64)
    (hD : D.toNat = if j < zc.toNat then zp.toNat + 8 * j else zp.toNat)
    (hS : Sr.toNat = if j < xc.toNat then xp.toNat + 8 * j else xp.toNat)
    (hN : N.toNat = zl.toNat - j)
    (hval : natVal S.mem zp.toNat j + y.toNat = natVal s.mem xp.toNat j) (m : Memory)
    (hc : MemFrame S.mem m (R.rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat - 8)] ++
        [(D.toNat, D.toNat + 8 * N.toNat)]) ∧ LiveFrame S.mem m L [(D.toNat, D.toNat + 8 * N.toNat)] ∧
      Mem.Copied S.mem m D.toNat Sr.toNat (8 * N.toNat))
    (hINV : R.inv b L (s.regs 14).toNat (view R.rt L m)) (S' : State)
    (hsp : S'.regs 4 = s.regs 4 - 32#64) (h5 : S'.regs 5 = s.regs 4 - 8#64) (h14 : S'.regs 14 = s.regs 14)
    (h15 : S'.xmm 15 = s.xmm 15) (hdf : S'.df = false) (hfs : S'.fsBase = s.fsBase) (hm : S'.mem = m)
    (hpc : S'.rip = BitVec.ofNat 64 (entry + 0x91) ∨ S'.rip = BitVec.ofNat 64 (entry + 0x11e)) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S'
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := after R b L ret s zp zl zc xp xc y hpre hne S j hj1 hj hrel D Sr N hD hS hN hval m
    hc.1 hc.2.1 hc.2.2
  subst hm
  exact ret0 impl R b L ret hret s zp zl zc xp xc y hpre S' zl.toNat (Nat.le_refl _) (by omega)
    ⟨hsp, h5, h14, h15, hrel.x15z, hdf, hfs, e1, e2, e3, e4, hINV, hrel.df0⟩ hpc e5

set_option maxRecDepth 20000 in
/-- `copy(z[1:], x[1:])` after limb 0 (`CMP RAX, RBX` at `+0x83`, count in `RCX`) -/
theorem copyA (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hmv : MemmoveLive64 (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hne : zp ≠ xp) (S : State) (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ zl.toNat)
    (hrel : Rel R b L ret zp.toNat j s S) (D Sr N : BitVec 64)
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x83)) (hc : S.regs 1 = N)
    (h0 : S.regs 0 = D) (h3 : S.regs 3 = Sr)
    (hD : D.toNat = if j < zc.toNat then zp.toNat + 8 * j else zp.toNat)
    (hS : Sr.toNat = if j < xc.toNat then xp.toNat + 8 * j else xp.toNat)
    (hN : N.toNat = zl.toNat - j)
    (hval : natVal S.mem zp.toNat j + y.toNat = natVal s.mem xp.toNat j) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, htls⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre'
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  have hrel' := hrel
  obtain ⟨hsp, h5, h14, h15, hx15, hdf, hfs, h_rd_lr, h_rd_fp, hmf, hlf, hinv, hdfR⟩ := hrel'
  simp only [hne, if_false] at hmv'
  have hok := hmv' j hj1 hj
  rw [← hD, ← hS, show 8 * (zl.toNat - j) = N.toNat * 8 by rw [hN]; omega] at hok
  have hzx' : Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * zl.toNat) := hzx.resolve_left hne
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  have hzg' := (hzg (by omega)).1
  simp only [Outside, and_true] at hzw hxw
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 32 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have h_rd_g : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hmf.readLE _ _ (by
      simp only [outside_append, win, outside_cons, outside_nil, and_true]
      unfold Apart at hga hzg'
      exact ⟨⟨hgr, by omega⟩, by omega⟩)
  have hgacc : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hmf.accessible]; exact hg2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 4136) (4136 + 40) true = true := by rw [hmf.accessible]; exact hw
  have hDr : zp.toNat ≤ D.toNat ∧ D.toNat + 8 * N.toNat ≤ zp.toNat + 8 * zl.toNat := by
    rw [hD, hN]; split <;> omega
  have hSr : xp.toNat ≤ Sr.toNat ∧ Sr.toNat + 8 * N.toNat ≤ xp.toNat + 8 * zl.toNat := by
    rw [hS, hN]; split <;> omega
  have hDacc : S.mem.accessible D.toNat (8 * N.toNat) true = true := by
    rw [hmf.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hzacc (Or.inr rfl) hDr.1 hDr.2
  have hSacc : S.mem.accessible Sr.toNat (8 * N.toNat) false = true := by
    rw [hmf.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hxacc (Or.inl rfl) hSr.1 hSr.2
  have hDh : InRanges D.toNat (N.toNat * 8) L ∨ Outside D.toNat (N.toNat * 8) R.rt :=
    hzh.sub hDr.1 (by omega)
  have hLsC : ∀ (r : Nat × Nat), r ∈ L → Outside r.fst (r.snd - r.fst)
      ([((s.regs 4).toNat - 40 - 4096, (s.regs 4).toNat - 40),
          ((s.regs 4).toNat - 40 + 8, (s.regs 4).toNat - 40 + 8 + 24)] ++
        [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 8)]) := by
    intro r hr
    have := hLs r hr
    simp only [win, Outside, outside_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  have hN61 : N.toNat < 2 ^ 61 := by omega
  janus64_run until [entry + 0x91] calls [hmv L b]
  · have hDS : D = Sr := by
      apply BitVec.eq_of_toNat_eq; have := D.isLt; have := Sr.isLt; omega
    have hjl : j = zl.toNat := by
      rw [hDS] at hD
      by_cases hjz : j < zc.toNat <;> by_cases hjx : j < xc.toNat <;>
        simp only [hjz, hjx, ite_true, ite_false] at hD hS <;> unfold Apart at hzx' <;> omega
    subst hjl
    exact ret0 impl R b L ret hret s zp zl zc xp xc y hpre _ zl.toNat (Nat.le_refl _) (by omega)
      ⟨hrel.sp, hrel.fp, hrel.g, hrel.x15, hrel.x15z, (by first | exact hrel.df | rfl), hrel.fs, hrel.lr, hrel.sfp, hrel.mf, hrel.lf,
        hrel.inv, hrel.df0⟩
      (Or.inl rfl) hval
  · rename_i _ _ _ _ m _ _ hMF hLF hINV hCP
    have hc := call_norm hMF hLF hCP (by omega) (out_all fun r hr => by
      have := hLs r hr; simp only [win, Outside, outside_cons, outside_nil, and_true] at this; omega)
    rw [show (s.regs 4).toNat - 40 - 4096 = (s.regs 4).toNat - 4136 by omega,
      show (s.regs 4).toNat - 40 + 32 = (s.regs 4).toNat - 8 by omega, Nat.mul_comm N.toNat 8] at hc
    refine cont impl R b L ret hret s zp zl zc xp xc y hpre hne S j hj1 hj hrel D Sr N hD hS hN hval m hc hINV
      _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Or.inl ?_)
    all_goals first | (janus64_simp; done) | (janus64_simp; bv_omega)

set_option maxRecDepth 20000 in
/-- `copy(z[i+1:], x[i+1:])` in the loop (`CMP RAX, RBX` at `+0x10d`, count in `R9`) -/
theorem copyB (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hmv : MemmoveLive64 (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hne : zp ≠ xp) (S : State) (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ zl.toNat)
    (hrel : Rel R b L ret zp.toNat j s S) (D Sr N : BitVec 64)
    (hpc : S.rip = BitVec.ofNat 64 (entry + 0x10d)) (hc : S.regs 9 = N)
    (h0 : S.regs 0 = D) (h3 : S.regs 3 = Sr)
    (hD : D.toNat = if j < zc.toNat then zp.toNat + 8 * j else zp.toNat)
    (hS : Sr.toNat = if j < xc.toNat then xp.toNat + 8 * j else xp.toNat)
    (hN : N.toNat = zl.toNat - j)
    (hval : natVal S.mem zp.toNat j + y.toNat = natVal s.mem xp.toNat j) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, htls⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre'
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  have hrel' := hrel
  obtain ⟨hsp, h5, h14, h15, hx15, hdf, hfs, h_rd_lr, h_rd_fp, hmf, hlf, hinv, hdfR⟩ := hrel'
  simp only [hne, if_false] at hmv'
  have hok := hmv' j hj1 hj
  rw [← hD, ← hS, show 8 * (zl.toNat - j) = N.toNat * 8 by rw [hN]; omega] at hok
  have hzx' : Apart zp.toNat (8 * zl.toNat) xp.toNat (8 * zl.toNat) := hzx.resolve_left hne
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  have hzg' := (hzg (by omega)).1
  simp only [Outside, and_true] at hzw hxw
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 32 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have h_rd_g : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hmf.readLE _ _ (by
      simp only [outside_append, win, outside_cons, outside_nil, and_true]
      unfold Apart at hga hzg'
      exact ⟨⟨hgr, by omega⟩, by omega⟩)
  have hgacc : S.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by rw [hmf.accessible]; exact hg2
  have hsacc : S.mem.accessible ((s.regs 4).toNat - 4136) (4136 + 40) true = true := by rw [hmf.accessible]; exact hw
  have hDr : zp.toNat ≤ D.toNat ∧ D.toNat + 8 * N.toNat ≤ zp.toNat + 8 * zl.toNat := by
    rw [hD, hN]; split <;> omega
  have hSr : xp.toNat ≤ Sr.toNat ∧ Sr.toNat + 8 * N.toNat ≤ xp.toNat + 8 * zl.toNat := by
    rw [hS, hN]; split <;> omega
  have hDacc : S.mem.accessible D.toNat (8 * N.toNat) true = true := by
    rw [hmf.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hzacc (Or.inr rfl) hDr.1 hDr.2
  have hSacc : S.mem.accessible Sr.toNat (8 * N.toNat) false = true := by
    rw [hmf.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hxacc (Or.inl rfl) hSr.1 hSr.2
  have hDh : InRanges D.toNat (N.toNat * 8) L ∨ Outside D.toNat (N.toNat * 8) R.rt :=
    hzh.sub hDr.1 (by omega)
  have hLsC : ∀ (r : Nat × Nat), r ∈ L → Outside r.fst (r.snd - r.fst)
      ([((s.regs 4).toNat - 40 - 4096, (s.regs 4).toNat - 40),
          ((s.regs 4).toNat - 40 + 8, (s.regs 4).toNat - 40 + 8 + 24)] ++
        [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 8)]) := by
    intro r hr
    have := hLs r hr
    simp only [win, Outside, outside_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  have hN61 : N.toNat < 2 ^ 61 := by omega
  janus64_run until [entry + 0x11e] calls [hmv L b]
  · have hDS : D = Sr := by
      apply BitVec.eq_of_toNat_eq; have := D.isLt; have := Sr.isLt; omega
    have hjl : j = zl.toNat := by
      rw [hDS] at hD
      by_cases hjz : j < zc.toNat <;> by_cases hjx : j < xc.toNat <;>
        simp only [hjz, hjx, ite_true, ite_false] at hD hS <;> unfold Apart at hzx' <;> omega
    subst hjl
    exact ret0 impl R b L ret hret s zp zl zc xp xc y hpre _ zl.toNat (Nat.le_refl _) (by omega)
      ⟨hrel.sp, hrel.fp, hrel.g, hrel.x15, hrel.x15z, (by first | exact hrel.df | rfl), hrel.fs, hrel.lr, hrel.sfp, hrel.mf, hrel.lf,
        hrel.inv, hrel.df0⟩
      (Or.inr rfl) hval
  · rename_i _ _ _ _ m _ _ hMF hLF hINV hCP
    have hc := call_norm hMF hLF hCP (by omega) (out_all fun r hr => by
      have := hLs r hr; simp only [win, Outside, outside_cons, outside_nil, and_true] at this; omega)
    rw [show (s.regs 4).toNat - 40 - 4096 = (s.regs 4).toNat - 4136 by omega,
      show (s.regs 4).toNat - 40 + 32 = (s.regs 4).toNat - 8 by omega, Nat.mul_comm N.toNat 8] at hc
    refine cont impl R b L ret hret s zp zl zc xp xc y hpre hne S j hj1 hj hrel D Sr N hD hS hN hval m hc hINV
      _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (Or.inr ?_)
    all_goals first | (janus64_simp; done) | (janus64_simp; bv_omega)

set_option maxRecDepth 20000 in
/-- after `z[i] = x[i] - 1` with `z = x` (`+0x11e`): nothing more to copy -/
theorem step_inplace (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (he : zp = xp) (S : State) (i : Nat) (hi : i < zl.toNat)
    (hrel : Rel R b L ret zp.toNat i s S)
    (hval : natVal S.mem zp.toNat i + y.toNat = natVal s.mem xp.toNat i + 2 ^ (64 * i))
    (hxv : s.mem.readLE (xp.toNat + i * 8) 8 ≠ 0)
    (S' : State) (hsp : S'.regs 4 = S.regs 4) (h5 : S'.regs 5 = S.regs 5) (h14 : S'.regs 14 = S.regs 14)
    (h15 : S'.xmm 15 = S.xmm 15) (hdf : S'.df = false) (hfs : S'.fsBase = S.fsBase)
    (hm : S'.mem = S.mem.writeLE (zp.toNat + i * 8) 8 (s.mem.readLE (xp.toNat + i * 8) 8 - 1))
    (hpc : S'.rip = BitVec.ofNat 64 (entry + 0x11e)) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S'
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  have hr' := rel_store R b L ret s zp zl zc xp xc hpre S i hi hrel _ S' hsp h5 h14 h15 hdf hfs hm
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
/-- after `z[i] = x[i] - 1` with `z ≠ x`, the pointers of `copy(z[i+1:], x[i+1:])` computed (`+0x10d`) -/
theorem step_copy (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hmv : MemmoveLive64 (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hne : zp ≠ xp) (S : State) (i : Nat) (hi : i < zl.toNat)
    (hrel : Rel R b L ret zp.toNat i s S)
    (hval : natVal S.mem zp.toNat i + y.toNat = natVal s.mem xp.toNat i + 2 ^ (64 * i))
    (hxv : s.mem.readLE (xp.toNat + i * 8) 8 ≠ 0)
    (S' : State) (hsp : S'.regs 4 = S.regs 4) (h5 : S'.regs 5 = S.regs 5) (h14 : S'.regs 14 = S.regs 14)
    (h15 : S'.xmm 15 = S.xmm 15) (hdf : S'.df = false) (hfs : S'.fsBase = S.fsBase)
    (hm : S'.mem = S.mem.writeLE (zp.toNat + i * 8) 8 (s.mem.readLE (xp.toNat + i * 8) 8 - 1))
    (hpc : S'.rip = BitVec.ofNat 64 (entry + 0x10d))
    (h0 : S'.regs 0 = zp + ((0#64 - (zc - BitVec.ofNat 64 (i + 1))).sshiftRight 63 &&& BitVec.ofNat 64 (i + 1) <<< 3))
    (h3 : S'.regs 3 = xp + ((0#64 - (xc - BitVec.ofNat 64 (i + 1))).sshiftRight 63 &&& BitVec.ofNat 64 (i + 1) <<< 3))
    (h9 : S'.regs 9 = zl - BitVec.ofNat 64 (i + 1)) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S'
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  have hr' := rel_store R b L ret s zp zl zc xp xc hpre S i hi hrel _ S' hsp h5 h14 h15 hdf hfs hm
  have hpre' := hpre
  obtain ⟨-, hzc, hxc, hzc63, hxc63, hzl, -, -, -, hx48, -⟩ := hpre'
  obtain ⟨-, -, -, hz48⟩ := hzl (by omega)
  refine copyB impl R b L ret hmv hret s zp zl zc xp xc y hpre hne S' (i + 1) (by omega) (by omega) hr'
    _ _ _ hpc h9 h0 h3 ?_ ?_ ?_ ?_
  · rw [BitVec.toNat_add, FvModexp.Asm.maskB64 zc i hzc63 (by omega) (by omega)]
    split <;> omega
  · rw [BitVec.toNat_add, FvModexp.Asm.maskB64 xc i hxc63 (by omega) (by omega)]
    split <;> omega
  · rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [hm]; exact FvModexp.Asm.v_dec S.mem s.mem _ _ i _ hval hxv

/-- the loop state at the head (`+0xad`, `RDX = i`) -/
def AtHead (zp zl zc xp xc : BitVec 64) (i : Nat) (S : State) : Prop :=
  S.rip = BitVec.ofNat 64 (entry + 0xad) ∧ S.regs 0 = zp ∧ S.regs 3 = zl ∧ S.regs 1 = zc ∧ S.regs 7 = xp ∧
    S.regs 6 = zl ∧ S.regs 8 = xc ∧ S.regs 2 = BitVec.ofNat 64 i

set_option maxRecDepth 20000 in
/-- the loop exit (`i = len z`): the carry out is `1` -/
theorem fin1 (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hret : RetAddr (LibSubVW.program.link impl) ret) (s : State) (zp zl zc xp xc y : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (S : State) (hz : 0 < zl.toNat) (hh : AtHead zp zl zc xp xc zl.toNat S)
    (hrel : Rel R b L ret zp.toNat zl.toNat s S)
    (hval : natVal S.mem zp.toNat zl.toNat + y.toNat = natVal s.mem xp.toNat zl.toNat + 2 ^ (64 * zl.toNat)) :
    Reaches ((LibSubVW.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ Post R b L zp zl xp y s s') := by
  have hpre' := hpre
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, htls⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre'
  try simp only [regSP] at hb' ha hw
  obtain ⟨hpc, h0, h1, h2, h3, h4, h5, h6⟩ := hh
  obtain ⟨hsp, h5', h14, h15, hx15, hdf, hfs, h_rd_lr, h_rd_fp, hmf, hlf, hinv, hdfR⟩ := hrel
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 32 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hacc : S.mem.accessible ((s.regs 4).toNat - 4136) (4136 + 40) true = true := by rw [hmf.accessible]; exact hw
  have hz63 : zl.toNat < 2 ^ 63 := by omega
  have hlt := natVal_lt S.mem zp.toNat zl.toNat
  have hP : 0 < 2 ^ (64 * zl.toNat) := Nat.two_pow_pos _
  clear hmv' hinv0
  janus64_run
  refine ⟨hfs, hdfR.symm, ?_, ?_, L, b, LiveExt.refl R L, Nat.le_refl _, hinv, hmf, hlf⟩
  · rw [if_neg (by omega), if_pos (by omega)]; rfl
  · rw [show natVal s.mem xp.toNat zl.toNat + 2 ^ (64 * zl.toNat) - y.toNat = natVal S.mem zp.toNat zl.toNat by omega,
      Nat.mod_eq_of_lt hlt]

set_option maxRecDepth 20000 in
/-- one pass of the loop body (`i < len z`), the next head handed to `IH` -/
theorem body (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hmv : MemmoveLive64 (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
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
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, htls⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre'
  try simp only [regSP] at hb' ha hw
  obtain ⟨hpc, h0, h1, h2, h3, h4, h5, h6⟩ := hh
  have hrel' := hrel
  obtain ⟨hsp, h5', h14, h15, hx15, hdf, hfs, h_rd_lr, h_rd_fp, hmf, hlf, hinv, hdfR⟩ := hrel'
  have hspn : (S.regs 4).toNat = (s.regs 4).toNat - 32 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hacc : S.mem.accessible ((s.regs 4).toNat - 4136) (4136 + 40) true = true := by rw [hmf.accessible]; exact hw
  have hz63 : zl.toNat < 2 ^ 63 := by omega
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  have hzacc' : S.mem.accessible zp.toNat (8 * zl.toNat) true = true := by rw [hmf.accessible]; exact hzacc
  have hxacc' : S.mem.accessible xp.toNat (8 * zl.toNat) false = true := by rw [hmf.accessible]; exact hxacc
  have h_rd_x := rel_x R b L ret s zp zl zc xp xc hpre S (i * 8) 8 i (by omega) hrel (by omega) (fun _ => by omega)
  have hi64 : i + 1 < 2 ^ 64 := by omega
  clear hmv' hinv0 hLs hga hgr hout
  janus64_run until [entry + 0xad, entry + 0x10d, entry + 0x11e]
  · refine IH _ ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      (rel_store R b L ret s zp zl zc xp xc hpre S i hi hrel _ _ rfl rfl rfl rfl rfl rfl rfl)
      (FvModexp.Asm.v_zero S.mem s.mem _ _ i _ hval hbr)
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · rfl
  · rename_i _ hxv
    have he : zp = xp := by
      apply BitVec.eq_of_toNat_eq; have := zp.isLt; have := xp.isLt; omega
    exact step_inplace impl R b L ret hret s zp zl zc xp xc y hpre he S i hi hrel
      hval hxv _ rfl rfl rfl rfl rfl rfl rfl rfl
  · rename_i _ hxv
    have hne : zp ≠ xp := by
      intro h; subst h; have := zp.isLt; omega
    exact step_copy impl R b L ret hmv hret s zp zl zc xp xc y hpre hne S i hi hrel
      hval hxv _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- the borrow loop (`+0xad`, `RDX = i`), by induction on `len z - i`: `z[0:i] + y = x[0:i] + B^i` -/
theorem loop (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat)
    (hmv : MemmoveLive64 (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
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
/-- the prologue's stores (saved `RBP`, the spills of `RAX`, `RDI`) and `z[0] = v`: `Rel` with one limb written -/
theorem entry_rel (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl zc xp xc : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hz : 0 < zl.toNat) (hlr : s.mem.readLE (s.regs 4).toNat 8 = ret)
    (hx15 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (v : Nat) {S' : State}
    (hsp : S'.regs 4 = s.regs 4 - 32#64) (h5 : S'.regs 5 = s.regs 4 - 8#64) (h14 : S'.regs 14 = s.regs 14)
    (h15 : S'.xmm 15 = s.xmm 15) (hdf : S'.df = false) (hfs : S'.fsBase = s.fsBase)
    (hm : S'.mem = (((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat + 8) 8 zp.toNat).writeLE ((s.regs 4).toNat + 32) 8 xp.toNat).writeLE zp.toNat 8 v) :
    Rel R b L ret zp.toNat 1 s S' ∧ S'.mem.readLE zp.toNat 8 = v % 2 ^ 64 := by
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, htls⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv0, hmv'⟩ := hpre
  try simp only [regSP] at hb' ha hw
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl hz
  simp only [Outside, and_true] at hzw
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 40 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [win, Outside, outside_cons, outside_nil, and_true] at this; exact this
  have hwin : ∀ r ∈ win s 4136 40, (s.regs 4).toNat - 4136 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat + 40 := by
    simp only [win, List.mem_cons, List.mem_nil_iff, or_false]
    rintro r rfl; simp only; omega
  have hmf : MemFrame s.mem S'.mem (win s 4136 40 ++ [(zp.toNat, zp.toNat + 8 * 1)]) := by
    rw [hm]; simp only [win, List.cons_append, List.nil_append]; janus_frame
  have hrt : ∀ a n, (s.regs 4).toNat - 4136 ≤ a → a + n ≤ (s.regs 4).toNat + 40 → Outside a n R.rt :=
    fun a n h1 h2 => Outside.of_sub hout h1 (by omega)
  refine ⟨⟨hsp, h5, h14, h15, hx15, hdf, hfs, ?_, ?_, ?_, liveFrame_of_frame (rs := win s 4136 40) hmf hLs' hwin, ?_, hdf0⟩, ?_⟩
  · rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hlr
  · rw [hm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.mod_eq_of_lt (s.regs 5).isLt
  · exact ⟨fun a n h => hmf.readLE a n (by simp only [outside_append] at h ⊢; exact ⟨h.1.2, h.2⟩), hmf.accessible⟩
  · rw [hm]
    refine inv_store_held (inv_store_out (inv_store_out (inv_store_out hinv0
      (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega)))
      (hzh.sub (Nat.le_refl _) (by omega))
  · rw [hm, Janus.Arm64.Memory.readLE_writeLE_self]

/-- `entry_rel` in continuation form (for a goal about the executor's state literal) -/
theorem entry_k (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (ret : Nat) (s : State) (zp zl zc xp xc : BitVec 64)
    (hpre : Pre R b L zp zl zc xp xc s) (hz : 0 < zl.toNat) (hlr : s.mem.readLE (s.regs 4).toNat 8 = ret)
    (hx15 : s.xmm 15 = 0#128) (hdf0 : s.df = false) (v : Nat) (p : Amd64.Program) (Q : Amd64.Outcome → Prop) (S' : State)
    (hsp : S'.regs 4 = s.regs 4 - 32#64) (h5 : S'.regs 5 = s.regs 4 - 8#64) (h14 : S'.regs 14 = s.regs 14)
    (h15 : S'.xmm 15 = s.xmm 15) (hdf : S'.df = false) (hfs : S'.fsBase = s.fsBase)
    (hm : S'.mem = (((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat + 8) 8 zp.toNat).writeLE ((s.regs 4).toNat + 32) 8 xp.toNat).writeLE zp.toNat 8 v)
    (K : Rel R b L ret zp.toNat 1 s S' → S'.mem.readLE zp.toNat 8 = v % 2 ^ 64 → Reaches p S' Q) : Reaches p S' Q :=
  let h := entry_rel R b L ret s zp zl zc xp xc hpre hz hlr hx15 hdf0 v hsp h5 h14 h15 hdf hfs hm
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

set_option maxRecDepth 20000 in
/-- `subVW` on the library program -/
theorem ens_lib (impl : List Amd64.Segment) (R : RtInv)
    (hmv : MemmoveLive64 (LibSubVW.program.link impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures (LibSubVW.program.link impl) entry [zp, zl, zc, xp, xl, xc, y]
      (fun s => xl = zl ∧ Pre R b L zp zl zc xp xc s) (fun s s' => Post R b L zp zl xp y s s') := by
  intro ret hret s hs ⟨hxz, hpre⟩
  have hpre' := hpre
  obtain ⟨⟨hg, ⟨hb', ha, hw⟩, hal, hout, hga, hgr, hLs, htls⟩, hzc, hxc, hzc63, hxc63, hzl, hzw, hzg,
    hxacc, hx48, hxh, hxw, hzx, hinv, hmv'⟩ := hpre'
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hout hal hga hgr
  janus64_intro hs
  subst hxz
  simp only [Outside, and_true] at hzw hxw
  have hLs' : ∀ r ∈ L, r.1 + (r.2 - r.1) ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 40 ≤ r.1 := by
    intro r hr; have := hLs r hr; simp only [win, Outside, outside_cons, outside_nil, and_true] at this; exact this
  have hwin : ∀ r ∈ win s 4136 40, (s.regs 4).toNat - 4136 ≤ r.1 ∧ r.2 ≤ (s.regs 4).toNat + 40 := by
    simp only [win, List.mem_cons, List.mem_nil_iff, or_false]
    rintro r rfl; simp only; omega
  have hrt : ∀ a n, (s.regs 4).toNat - 4136 ≤ a → a + n ≤ (s.regs 4).toNat + 40 → Outside a n R.rt :=
    fun a n h1 h2 => Outside.of_sub hout h1 (by omega)
  by_cases hz0 : xl.toNat = 0
  · janus64_run
    refine ⟨rfl, h_df.symm, by simp [hz0]; rfl, by simp [hz0, Nat.mod_one], L, b, LiveExt.refl R L, Nat.le_refl _, ?_, ?_, ?_⟩
    · exact inv_store_out (inv_store_out (inv_store_out hinv
        (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega))) (hrt _ _ (by omega) (by omega))
    · simp only [win, List.append_assoc, List.cons_append, List.nil_append]; janus_frame
    · refine liveFrame_of_frame (rs := win s 4136 40) ?_ hLs' hwin
      simp only [win, List.cons_append, List.nil_append]; janus_frame
  obtain ⟨hzal, hzh, hzacc, hz48⟩ := hzl (by omega)
  clear hmv'
  have hx0 : s.mem.readLE xp.toNat 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt s.mem xp.toNat 8; simpa using this
  have hy := y.isLt
  have m8z := FvModexp.Asm.mask8_64 zc hzc63 (by omega)
  have m8x := FvModexp.Asm.mask8_64 xc hxc63 (by omega)
  janus64_run until [entry + 0xad, entry + 0x83, entry + 0x91]
  all_goals
    refine entry_k R b L ret s zp xl zc xp xc hpre (by omega) h_ret h_x15 h_df (18446744073709551616 - y.toNat + s.mem.readLE xp.toNat 8)
      _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun hr1 hv1 => ?_)
  all_goals first | rfl | (janus64_simp; done) | skip
  · rename_i _ _ hnc
    have hnc' : y.toNat ≤ s.mem.readLE xp.toNat 8 := by
      by_cases h : s.mem.readLE xp.toNat 8 < y.toNat
      · simp [h] at hnc
      · omega
    have he : zp = xp := by
      apply BitVec.eq_of_toNat_eq; have := zp.isLt; have := xp.isLt; omega
    refine ret0 impl R b L ret hret s zp xl zc xp xc y hpre _ 1 (by omega) (by omega) hr1 (Or.inl rfl)
      (val_inplace R b L ret s zp xl zc xp xc y hpre he _ 1 (by omega) hr1 ?_)
    simp only [natVal, Nat.mul_one]; rw [hv1]; omega
  · rename_i _ _ hnc
    have hnc' : y.toNat ≤ s.mem.readLE xp.toNat 8 := by
      by_cases h : s.mem.readLE xp.toNat 8 < y.toNat
      · simp [h] at hnc
      · omega
    have hne : zp ≠ xp := by
      intro h; subst h; have := zp.isLt; omega
    refine copyA impl R b L ret hmv hret s zp xl zc xp xc y hpre hne _ 1 (Nat.le_refl _) (by omega) hr1
      (zp + BitVec.setWidth 64 (BitVec.setWidth 32 ((0#64 - (zc - 1#64)).sshiftRight 63) &&& 8#32))
      (xp + BitVec.setWidth 64 (BitVec.setWidth 32 ((0#64 - (xc - 1#64)).sshiftRight 63) &&& 8#32))
      (xl - 1#64) rfl rfl rfl rfl ?_ ?_ ?_ ?_
    · rw [BitVec.toNat_add, m8z]; split <;> omega
    · rw [BitVec.toNat_add, m8x]; split <;> omega
    · rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    · simp only [natVal, Nat.mul_one]; rw [hv1]; omega
  · have hc : s.mem.readLE xp.toNat 8 < y.toNat := by
      by_cases h : s.mem.readLE xp.toNat 8 < y.toNat
      · exact h
      · simp [h] at hbr
    refine loop impl R b L ret hmv hret s zp xl zc xp xc y hpre (xl.toNat - 1) _ 1 (by omega) (Nat.le_refl _)
      ⟨rfl, h_a0, h_a1, h_a2, h_a3, h_a4, h_a5, rfl⟩ hr1 ?_
    simp only [natVal, Nat.mul_one]; rw [hv1]; omega

/-- **`subVW` (amd64)**, CONVENTIONS §3 shape (`Pre`/`Post` above; `xl = zl` is the `len(z) != len(x)` panic excluded) -/
theorem ens (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) :
    Ensures ((Extracted.program.onlySegments [fn]).link impl) (segAddr Extracted.program fn)
      [zp, zl, zc, xp, xl, xc, y]
      (fun s => xl = zl ∧ Pre R b L zp zl zc xp xc s) (fun s s' => Post R b L zp zl xp y s s') := by
  have hmv' := MemmoveLive64.of_codeIn (codeIn_ofImpl_restrict_of_apart64 hap [fn]) hmv
  have e : Extracted.program.onlySegments [fn] = LibSubVW.program := LibSubVW.eq_only.symm
  rw [e] at hmv' ⊢
  exact ens_lib impl R hmv' b L zp zl zc xp xl xc y

set_option linter.defProp false in
/-- `ens` as a callee summary inside a caller whose program keeps the functions `ms ⊇ [fn]` (CONVENTIONS §4) -/
def sum (impl : List Amd64.Segment) (hap : ImplApart Extracted.program impl) (R : RtInv)
    (hmv : MemmoveLive64 (Extracted.program.ofImpl impl) (cA "runtime.memmove") 4096 R)
    (b : Nat) (L : List (Nat × Nat)) (zp zl zc xp xl xc y : BitVec 64) (ms : List String)
    (hsub : ∀ x, [fn].contains x = true → ms.contains x = true) :=
  Ensures.toSummaryIn (ens impl hap R hmv b L zp zl zc xp xl xc y) (A64.noExit_restrict64 hap [fn])
    (by simp [numIntRegs]) (A64.codeIn_restrict_mono64 hap hsub)

end FvModexp.Amd64.SubVW
